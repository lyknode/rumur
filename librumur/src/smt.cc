#include <cstddef>
#include <gmpxx.h>
#include <rumur/except.h>
#include <rumur/Expr.h>
#include <rumur/Node.h>
#include <rumur/Number.h>
#include <rumur/smt.h>
#include <rumur/Stmt.h>
#include <rumur/traverse.h>
#include <sstream>
#include <string>
#include "utils.h"

namespace rumur {

SMTContext::SMTContext() { }

SMTContext::SMTContext(bool prefer_bitvectors_, size_t bitvector_width_)
 : prefer_bitvectors(prefer_bitvectors_), bitvector_width(bitvector_width_) { }

std::string SMTContext::register_symbol(size_t id) {
  // invent a new symbol and map this ID to it
  std::string s = make_symbol();
  scope.emplace_back(id, s);
  return s;
}

std::string SMTContext::lookup_symbol(size_t id, const Node &origin) const {

  // lookup the symbol in enclosing scopes from innermost to outermost
  for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
    if (it->first == id)
      return it->second;
  }

  // we expect any symbol encountered in a well-formed AST to be associated with
  // a previously encountered definition
  throw Error("unknown symbol encountered; applying SMT translation to an "
    "unvalidated AST?", origin.loc);
}

std::string SMTContext::make_symbol() {
  return "s" + std::to_string(counter++);
}

std::string SMTContext::add(const Node&) const {
  return prefer_bitvectors ? "bvadd" : "+";
}

std::string SMTContext::band(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvand";
  throw Error("SMT translation involving bitwise AND is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::bnot(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvnot";
  throw Error("SMT translation involving bitwise NOT is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::bor(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvor";
  throw Error("SMT translation involving bitwise OR is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::bxor(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvxor";
  throw Error("SMT translation involving bitwise XOR is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::div(const Node&) const {
  // solvers like CVC4 may fail with an error when given "div" but just ignore
  // this for now
  return prefer_bitvectors ? "bvsdiv" : "div";
}

std::string SMTContext::geq(const Node&) const {
  return prefer_bitvectors ? "bvsge" : ">=";
}

std::string SMTContext::gt(const Node&) const {
  return prefer_bitvectors ? "bvsgt" : ">";
}

std::string SMTContext::leq(const Node&) const {
  return prefer_bitvectors ? "bvsle" : "<=";
}

std::string SMTContext::lsh(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvshl";
  throw Error("SMT translation involving left shift is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::lt(const Node&) const {
  return prefer_bitvectors ? "bvslt" : "<";
}

std::string SMTContext::mod(const Node&) const {
  return prefer_bitvectors ? "bvsmod" : "mod";
}

std::string SMTContext::mul(const Node&) const {
  return prefer_bitvectors ? "bvmul" : "*";
}

std::string SMTContext::neg(const Node&) const {
  return prefer_bitvectors ? "bvneg" : "-";
}

std::string SMTContext::rsh(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvashr";
  throw Error("SMT translation involving right shift is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTContext::sub(const Node&) const {
  return prefer_bitvectors ? "bvsub" : "-";
}

std::string SMTContext::numeric_literal(const mpz_class &value,
    const Number &origin) const {

  if (value < 0)
    return "(" + neg(origin) + " " + numeric_literal(-value, origin) + ")";

  if (prefer_bitvectors) {
    return "(_ bv" + value.get_str() + " " + std::to_string(bitvector_width)
      + ")";
  }

  return value.get_str();
}

// unravel an lvalue to its leftmost component
static const Expr &get_stump(const Expr &lvalue) {

  // an lvalue can only be an identifier, record field, or array element (see
  // parser.yy)

  if (auto i = dynamic_cast<const Field*>(&lvalue)) {
    // do we need to keep unraveling?
    if (!isa<ExprID>(i->record))
      return get_stump(*i->record);
    return lvalue;
  }

  if (auto i = dynamic_cast<const Element*>(&lvalue)) {
    // do we need to keep unraveling?
    if (!isa<ExprID>(i->array))
      return get_stump(*i->array);
    return lvalue;
  }

  return lvalue;
}

// retrieve the originating ID of an lvalue
static const ExprID &get_root(const Expr &lvalue) {

  // an lvalue can only be an identifier, record field, or array element (see
  // parser.yy)

  if (auto i = dynamic_cast<const Field*>(&lvalue))
    return get_root(*i->record);

  if (auto i = dynamic_cast<const Element*>(&lvalue))
    return get_root(*i->array);

  if (auto i = dynamic_cast<const ExprID*>(&lvalue))
    return *i;

  throw Error("expression in lvalue is not an identifier, record field, or "
    "array element", lvalue.loc);
}

namespace { class Translator : public ConstTraversal {

 private:
  std::ostream &out;
  SMTContext &ctxt;

 public:
  Translator(std::ostream &out_, SMTContext &ctxt_): out(out_), ctxt(ctxt_) { }

  Translator &operator<<(const std::string &s) {
    out << s;
    return *this;
  }

  Translator &operator<<(const Expr &e) {
    dispatch(e);
    return *this;
  }

  void visit_add(const Add &n) {
    *this << "(" << ctxt.add(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_and(const And &n) {
    *this << "(and " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_assignment(const Assignment &n) {

    // Translate the RHS, that we need to evaluate *before* the LHS. The RHS may
    // contain an ID that is also the LHS, but the RHS needs to see the SMT
    // symbol of the state before the assignment.
    const std::string rhs = to_smt(*n.rhs, ctxt);

    // find the root expression whose value we need to update
    const Expr &stump = get_stump(*n.lhs);

    // determine how to express an update to this entity

    std::ostringstream buf;

    if (auto i = dynamic_cast<const ExprID*>(&stump)) {
      buf << rhs;

    } else if (auto f = dynamic_cast<const Field*>(&stump)) {
      buf << "(mk_TODO ...";

    } else if (auto e = dynamic_cast<const Element*>(&stump)) {
      const std::string array = to_smt(*e->array, ctxt);
      const std::string index = to_smt(*e->index, ctxt);
      buf << "(store " << array << " " << index << " " << rhs << ")";

    } else {
      throw Error("expression in lvalue is not an identifier, record field, or "
        "array element", n.lhs->loc);
    }

    // find the left hand side of the stump
    const ExprID &root = get_root(stump);

    // invent a new name to store the updated value
    const std::string fresh = ctxt.register_symbol(root.value->unique_id);

    *this << "(assert (= " << fresh << " " << buf.str() << "))";
  }

  void visit_band(const Band &n) {
    *this << "(" << ctxt.band(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_bnot(const Bnot &n) {
    *this << "(" << ctxt.bnot(n) << " " << *n.rhs << ")";
  }

  void visit_bor(const Bor &n) {
    *this << "(" << ctxt.bor(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_element(const Element &n) {
    *this << "(select " << *n.array << " " << *n.index << ")";
  }

  void visit_exprid(const ExprID &n) {
    *this << ctxt.lookup_symbol(n.value->unique_id, n);
  }

  void visit_eq(const Eq &n) {
    *this << "(= " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_div(const Div &n) {
    *this << "(" << ctxt.div(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_geq(const Geq &n) {
    *this << "(" << ctxt.geq(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_gt(const Gt &n) {
    *this << "(" << ctxt.gt(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_implication(const Implication &n) {
    *this << "(=> " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_isundefined(const IsUndefined &n) {
    throw Error("SMT translation of isundefined expressions is not supported",
      n.loc);
  }

  void visit_leq(const Leq &n) {
    *this << "(" << ctxt.leq(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_lsh(const Lsh &n) {
    *this << "(" << ctxt.lsh(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_lt(const Lt &n) {
    *this << "(" << ctxt.lt(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_mod(const Mod &n) {
    *this << "(" << ctxt.mod(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_mul(const Mul &n) {
    *this << "(" << ctxt.mul(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_negative(const Negative &n) {
    *this << "(" << ctxt.neg(n) << " " << *n.rhs << ")";
  }

  void visit_neq(const Neq &n) {
    *this << "(not (= " << *n.lhs << " " << *n.rhs << "))";
  }

  void visit_number(const Number &n) {
    *this << ctxt.numeric_literal(n.value, n);
  }

  void visit_not(const Not &n) {
    *this << "(not " << *n.rhs << ")";
  }

  void visit_or(const Or &n) {
    *this << "(or " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_rsh(const Rsh &n) {
    *this << "(" << ctxt.rsh(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_sub(const Sub &n) {
    *this << "(" << ctxt.sub(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_ternary(const Ternary &n) {
    *this << "(ite " << *n.cond << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_xor(const Xor &n) {
    *this << "(" << ctxt.bxor(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

}; }

void to_smt(std::ostream &out, const Node &n, SMTContext &ctxt) {
  Translator t(out, ctxt);
  t.dispatch(n);
}

std::string to_smt(const Expr &n, SMTContext &ctxt) {
  std::ostringstream buf;
  to_smt(buf, n, ctxt);
  return buf.str();
}

}
