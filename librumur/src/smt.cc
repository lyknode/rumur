#include <cstddef>
#include <gmpxx.h>
#include <rumur/except.h>
#include <rumur/Expr.h>
#include <rumur/Node.h>
#include <rumur/Number.h>
#include <rumur/traverse.h>
#include <rumur/smt.h>
#include <rumur/SymContext.h>
#include <sstream>
#include <string>

namespace rumur {

std::string SMTConfig::add(const Node&) const {
  return prefer_bitvectors ? "bvadd" : "+";
}

std::string SMTConfig::band(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvand";
  throw Error("SMT translation involving bitwise AND is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::bnot(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvnot";
  throw Error("SMT translation involving bitwise NOT is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::bor(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvor";
  throw Error("SMT translation involving bitwise OR is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::bxor(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvxor";
  throw Error("SMT translation involving bitwise XOR is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::div(const Node&) const {
  // solvers like CVC4 may fail with an error when given "div" but just ignore
  // this for now
  return prefer_bitvectors ? "bvsdiv" : "div";
}

std::string SMTConfig::geq(const Node&) const {
  return prefer_bitvectors ? "bvsge" : ">=";
}

std::string SMTConfig::gt(const Node&) const {
  return prefer_bitvectors ? "bvsgt" : ">";
}

std::string SMTConfig::leq(const Node&) const {
  return prefer_bitvectors ? "bvsle" : "<=";
}

std::string SMTConfig::lsh(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvshl";
  throw Error("SMT translation involving left shift is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::lt(const Node&) const {
  return prefer_bitvectors ? "bvslt" : "<";
}

std::string SMTConfig::mod(const Node&) const {
  return prefer_bitvectors ? "bvsmod" : "mod";
}

std::string SMTConfig::mul(const Node&) const {
  return prefer_bitvectors ? "bvmul" : "*";
}

std::string SMTConfig::neg(const Node&) const {
  return prefer_bitvectors ? "bvneg" : "-";
}

std::string SMTConfig::rsh(const Node &origin) const {
  if (prefer_bitvectors)
    return "bvashr";
  throw Error("SMT translation involving right shift is only supported when "
    "using bitvector representations", origin.loc);
}

std::string SMTConfig::sub(const Node&) const {
  return prefer_bitvectors ? "bvsub" : "-";
}

std::string SMTConfig::numeric_literal(const mpz_class &value,
    const Number &origin) const {

  if (value < 0)
    return "(" + neg(origin) + " " + numeric_literal(-value, origin) + ")";

  if (prefer_bitvectors) {
    return "(_ bv" + value.get_str() + " " + std::to_string(bitvector_width)
      + ")";
  }

  return value.get_str();
}

namespace { class Translator : public ConstTraversal {

 private:
  std::ostream &out;
  SymContext &ctxt;
  const SMTConfig &conf;

 public:
  Translator(std::ostream &out_, SymContext &ctxt_, const SMTConfig &conf_)
    : out(out_), ctxt(ctxt_), conf(conf_) { }

  Translator &operator<<(const std::string &s) {
    out << s;
    return *this;
  }

  Translator &operator<<(const Expr &e) {
    dispatch(e);
    return *this;
  }

  void visit_add(const Add &n) {
    *this << "(" << conf.add(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_and(const And &n) {
    *this << "(and " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_band(const Band &n) {
    *this << "(" << conf.band(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_bnot(const Bnot &n) {
    *this << "(" << conf.bnot(n) << " " << *n.rhs << ")";
  }

  void visit_bor(const Bor &n) {
    *this << "(" << conf.bor(n) << " " << *n.lhs << " " << *n.rhs << ")";
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
    *this << "(" << conf.div(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_geq(const Geq &n) {
    *this << "(" << conf.geq(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_gt(const Gt &n) {
    *this << "(" << conf.gt(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_implication(const Implication &n) {
    *this << "(=> " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_isundefined(const IsUndefined &n) {
    throw Error("SMT translation of isundefined expressions is not supported",
      n.loc);
  }

  void visit_leq(const Leq &n) {
    *this << "(" << conf.leq(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_lsh(const Lsh &n) {
    *this << "(" << conf.lsh(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_lt(const Lt &n) {
    *this << "(" << conf.lt(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_mod(const Mod &n) {
    *this << "(" << conf.mod(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_mul(const Mul &n) {
    *this << "(" << conf.mul(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_negative(const Negative &n) {
    *this << "(" << conf.neg(n) << " " << *n.rhs << ")";
  }

  void visit_neq(const Neq &n) {
    *this << "(not (= " << *n.lhs << " " << *n.rhs << "))";
  }

  void visit_number(const Number &n) {
    *this << conf.numeric_literal(n.value, n);
  }

  void visit_not(const Not &n) {
    *this << "(not " << *n.rhs << ")";
  }

  void visit_or(const Or &n) {
    *this << "(or " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_rsh(const Rsh &n) {
    *this << "(" << conf.rsh(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_sub(const Sub &n) {
    *this << "(" << conf.sub(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_ternary(const Ternary &n) {
    *this << "(ite " << *n.cond << " " << *n.lhs << " " << *n.rhs << ")";
  }

  void visit_xor(const Xor &n) {
    *this << "(" << conf.bxor(n) << " " << *n.lhs << " " << *n.rhs << ")";
  }

}; }

void to_smt(std::ostream &out, const Expr &n, SymContext &ctxt,
  SMTConfig &conf) {

  Translator t(out, ctxt, conf);
  t.dispatch(n);
}

std::string to_smt(const Expr &n, SymContext &ctxt, SMTConfig &conf) {
  std::ostringstream buf;
  to_smt(buf, n, ctxt, conf);
  return buf.str();
}

}
