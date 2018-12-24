#include <cassert>
#include <cstddef>
#include "generate.h"
#include <gmpxx.h>
#include <iostream>
#include <memory>
#include <rumur/rumur.h>
#include <string>
#include "utils.h"

using namespace rumur;

namespace {

class Generator : public ConstExprTraversal {

 private:
  std::ostream *out;
  bool lvalue;

 public:
  Generator(std::ostream &o, bool lvalue_): out(&o), lvalue(lvalue_) { }

  // Make emitting an rvalue more concise below
  Generator &operator<<(const Expr &e) {
    Generator g(*out, false);
    g.dispatch(e);
    return *this;
  }

  Generator &operator<<(const std::string &s) {
    *out << s;
    return *this;
  }

  void visit(const Add &n) final {
    if (lvalue)
      invalid(n);
    *this << "add(s, " << *n.lhs << ", " << *n.rhs << ")";
  }

  void visit(const And &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " && " << *n.rhs << ")";
  }

  void visit(const Div &n) final {
    if (lvalue)
      invalid(n);
    *this << "divide(s, " << *n.lhs << ", " << *n.rhs << ")";
  }

  void visit(const Element &n) final {
    if (lvalue && !n.is_lvalue())
      invalid(n);

    // First, determine the width of the array's elements

    const TypeExpr *t1 = n.array->type();
    assert(t1 != nullptr && "array with invalid type");
    const TypeExpr *t2 = t1->resolve();
    assert(t2 != nullptr && "array with invalid type");

    auto a = dynamic_cast<const Array&>(*t2);
    mpz_class element_width = a.element_type->width();

    // Second, determine the minimum and maximum values of the array's index type

    const TypeExpr *t3 = a.index_type->resolve();
    assert(t3 != nullptr && "array with invalid index type");

    mpz_class min, max;
    if (auto r = dynamic_cast<const Range*>(t3)) {
      min = r->min->constant_fold();
      max = r->max->constant_fold();
    } else if (auto e = dynamic_cast<const Enum*>(t3)) {
      min = 0;
      max = e->count() - 1;
    } else if (auto s = dynamic_cast<const Scalarset*>(t3)) {
      min = 0;
      max = s->bound->constant_fold() - 1;
    } else {
      assert(false && "array with invalid index type");
    }

    if (!lvalue && a.element_type->is_simple()) {
      const std::string lb = a.element_type->lower_bound();
      const std::string ub = a.element_type->upper_bound();
      *out << "handle_read(s, " << lb << ", " << ub << ", ";
    }

    *out << "handle_index(s, SIZE_C(" << element_width << "), VALUE_C(" << min
      << "), VALUE_C(" << max << "), ";
    if (lvalue) {
      generate_lvalue(*out, *n.array);
    } else {
      generate_rvalue(*out, *n.array);
    }
    *this << ", " << *n.index << ")";

    if (!lvalue && a.element_type->is_simple())
      *out << ")";
  }

  void visit(const Eq &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " == " << *n.rhs << ")";
  }

  void visit(const Exists &n) final {
    if (lvalue)
      invalid(n);

    *out << "({ bool result = false; ";
    generate_quantifier_header(*out, n.quantifier);
    *this << "if (" << *n.expr << ") { result = true; break; }";
    generate_quantifier_footer(*out, n.quantifier);
    *out << " result; })";
  }

  void visit(const ExprID &n) final {
    if (n.value == nullptr)
      throw Error("symbol \"" + n.id + "\" in expression is unresolved", n.loc);

    if (lvalue && !n.is_lvalue())
      invalid(n);

    /* This is a reference to a const. Note, this also covers enum
     * members.
     */
    if (auto c = dynamic_cast<const ConstDecl*>(n.value.get())) {
      assert(!lvalue && "const appearing as an lvalue");
      *out << "VALUE_C(" << c->value->constant_fold() << ")";
      return;
    }

    // This is either a state variable, a local variable or an alias.
    if (isa<AliasDecl>(n.value) || isa<VarDecl>(n.value)) {

      const TypeExpr *t = n.type();
      assert((!n.is_lvalue() || t != nullptr) && "lvalue without a type");

      if (!lvalue && n.is_lvalue() && t->is_simple()) {
        const std::string lb = t->lower_bound();
        const std::string ub = t->upper_bound();
        *out << "handle_read(s, " << lb << ", " << ub << ", ";
      }

      *out << "ru_" << n.id;

      if (!lvalue && n.is_lvalue() && t->is_simple())
        *out << ")";
      return;
    }

    // FIXME: there's another case here where it's a reference to a quanitified
    // variable. I suspect we should just handle that the same way as a local.
  }

  void visit(const Field &n) final {
    if (lvalue && !n.is_lvalue())
      invalid(n);

    const TypeExpr *root = n.record->type();
    assert(root != nullptr);
    const TypeExpr *resolved = root->resolve();
    assert(resolved != nullptr);
    if (auto r = dynamic_cast<const Record*>(resolved)) {
      mpz_class offset = 0;
      for (const Ptr<VarDecl> &f : r->fields) {
        if (f->name == n.field) {
          if (!lvalue && f->type->is_simple()) {
            const std::string lb = f->type->lower_bound();
            const std::string ub = f->type->upper_bound();
            *out << "handle_read(s, " << lb << ", " << ub << ", ";
          }
          *out << "handle_narrow(";
          if (lvalue) {
            generate_lvalue(*out, *n.record);
          } else {
            generate_rvalue(*out, *n.record);
          }
          *out << ", " << offset << ", " << f->type->width() << ")";
          if (!lvalue && f->type->is_simple())
            *out << ")";
          return;
        }
        offset += f->type->width();
      }
      throw Error("no field named \"" + n.field + "\" in record", n.loc);
    }
    throw Error("left hand side of field expression is not a record", n.loc);
  }

  void visit(const Forall &n) final {
    if (lvalue)
      invalid(n);

    *out << "({ bool result = true; ";
    generate_quantifier_header(*out, n.quantifier);
    *this << "if (!" << *n.expr << ") { result = false; break; }";
    generate_quantifier_footer(*out, n.quantifier);
    *out << " result; })";
  }

  void visit(const FunctionCall &n) final {
    if (lvalue)
      invalid(n);

    if (n.function == nullptr)
      throw Error("unresolved function reference " + n.name, n.loc);

    const Ptr<TypeExpr> &return_type = n.function->return_type;

    // Open a statement-expression so we can declare temporaries.
    *out << "({ ";

    /* Firstly, one of our assumptions in the following is that any complex
     * argument we have is capable of being an lvalue. This is because there is
     * currently no syntax to express a complex rvalue.
     */
    for (const Ptr<Expr> &a __attribute__((unused)) : n.arguments)
      assert((a->type() == nullptr || a->type()->is_simple() || a->is_lvalue())
        && "non-lvalue complex argument");

    /* Secondly, a read-only value is never passed to a var parameter. This
     * should have been validated by FunctionCall::validate().
     */
    {
      auto it = n.function->parameters.begin();
      for (const Ptr<Expr> &a __attribute__((unused)) : n.arguments) {
        assert(((*it)->is_readonly() || !a->is_readonly()) &&
          "read-only value passed to var parameter");
        it++;
      }
    }

    /* Now for each parameter we need to consider four distinct methods, based
     * on the parameter's circumstance as described in the following table:
     *
     *   ┌──────┬────────────────┬─────────┬────────────╥────────┐
     *   │ var? │ simple/complex │ lvalue? │ read-only? ║ method │
     *   ├──────┼────────────────┼─────────┼────────────╫────────┤
     *   │  no  │     simple     │    no   │     -      ║    1   │
     *   │  no  │     simple     │   yes   │     no     ║    2   │
     *   │  no  │     simple     │   yes   │    yes     ║    2   │
     *   │  no  │    complex     │    -    │     no     ║    3   │
     *   │  no  │    complex     │    -    │    yes     ║    3   │
     *   │ yes  │     simple     │    no   │     no     ║    1   │
     *   │ yes  │     simple     │   yes   │     no     ║    4   │
     *   │ yes  │    complex     │    -    │     no     ║    4   │
     *   └──────┴────────────────┴─────────┴────────────╨────────┘
     *
     *   1. We can create a temporary handle and backing storage, then extract
     *      the value of the argument as an rvalue and write it to this
     *      temporary. The temporary can then be passed into the function,
     *      ensuring we don't modify the original argument.
     *
     *   2. We can do the same as (1), but extract the value of the argument
     *      with handle_read_raw. We need to do this because the argument might
     *      be undefined, in which case we want to extract its value without
     *      error. Another wrinkle we need to handle here is that the argument
     *      might be of a different range type than the function parameter type
     *      (differing lower and upper bounds).
     *
     *   3. We can create a temporary handle and backing store and then use
     *      handle_copy to transfer the value of the original argument. This is
     *      correct as we know the argument and the parameter it will be passed
     *      as have identical width.
     *
     *   4. We just pass the original handle, the lvalue of the argument.
     */

    auto get_method =
      [](const Ptr<VarDecl> &parameter, const Ptr<Expr> &argument) {

        bool var = !parameter->is_readonly();
        bool simple = parameter->type->is_simple();
        bool is_lvalue = argument->is_lvalue();
        bool readonly = argument->is_readonly();

        if (!var &&  simple && !is_lvalue             ) return 1;
        if (!var &&  simple &&  is_lvalue && !readonly) return 2;
        if (!var &&  simple &&  is_lvalue &&  readonly) return 2;
        if (!var && !simple &&               !readonly) return 3;
        if (!var && !simple &&                readonly) return 3;
        if ( var &&  simple && !is_lvalue             ) return 1;
        if ( var &&  simple &&  is_lvalue && !readonly) return 4;
        if ( var && !simple &&               !readonly) return 4;

        assert(!"unreachable");
        __builtin_unreachable();
      };

    // Create the temporaries for each argument.
    {
      size_t index = 0;
      auto it = n.function->parameters.begin();
      for (const Ptr<Expr> &a : n.arguments) {
        const Ptr<VarDecl> &p = *it;

        const std::string storage = "v" + std::to_string(n.unique_id) + "_"
          + std::to_string(index) + "_";
        const std::string handle = "v" + std::to_string(n.unique_id) + "_"
          + std::to_string(index);

        auto method = get_method(p, a);
        assert(method >= 1 && method <= 4);

        if (method == 1 || method == 2 || method == 3)
          *out
            << "uint8_t " << storage << "[BITS_TO_BYTES(" << p->width()
              << ")] = { 0 }; "
            << "struct handle " << handle << " = { .base = " << storage
              << ", .offset = 0, .width = SIZE_C(" << p->width() << ") }; ";

        if (method == 1) {
          const std::string lb = p->get_type()->lower_bound();
          const std::string ub = p->get_type()->upper_bound();

          *out
            << "handle_write(state_drop_const(s), " << lb << ", " << ub << ", "
              << handle << ", ";
          generate_rvalue(*out, *a);
          *out << "); ";

        } else if (method == 2) {
          const std::string lb = p->get_type()->lower_bound();
          const std::string ub = p->get_type()->upper_bound();

          const std::string lba = a->type()->lower_bound();

          *out
            << "{ "
            << "value_t v = handle_read_raw(";
          generate_lvalue(*out, *a);
          *out << "); "
            << "if (v != 0 && (v + " << lba << " - 1 < " << lb << " || v + "
              << lba << " - 1 > " << ub << ")) { "
            << "error(s, false, \"call to function %s passed an out-of-range "
              << "value %\" PRIVAL \" to parameter " << (index + 1) << "\", \""
              << n.name << "\", v + " << lba << " - 1); "
            << "} "
            << "handle_write_raw(" << handle << ", v == 0 ? v : (v + " << lba
              << " - " << lb << ")); "
            << "} ";

        } else if (method == 3) {
          assert(a->type()->width() == p->width() && "complex function "
            "parameter receiving an argument of a differing width");

          *out
            << "handle_copy(" << handle << ", ";
          generate_lvalue(*out, *a);
          *out << "); ";

        }

        it++;
        index++;
      }
    }

    *out << "ru_" << n.name << "(state_drop_const(s)";

    // Pass the return type output parameter if required.
    if (return_type != nullptr && !return_type->is_simple())
      *out << ", (struct handle){ .base = ret" << n.unique_id
        << ", .offset = 0ul, .width = SIZE_C(" << return_type->width() << ") }";

    // Now emit the arguments to the function.
    {
      size_t index = 0;
      auto it = n.function->parameters.begin();
      for (const Ptr<Expr> &a : n.arguments) {

        *out << ", ";

        assert(it != n.function->parameters.end() &&
          "function call has more arguments than its target function");

        const Ptr<VarDecl> &p = *it;

        const std::string handle = "v" + std::to_string(n.unique_id) + "_"
          + std::to_string(index);

        if (get_method(p, a) == 4) {
          generate_lvalue(*out, *a);
        } else {
          *out << handle;
        }

        index++;
        it++;
      }
    }

    *out << ");";

    // Close the statement-expression.
    *out << " })";
  }

  void visit(const Geq &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " >= " << *n.rhs << ")";
  }

  void visit(const Gt &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " > " << *n.rhs << ")";
  }

  void visit(const Implication &n) final {
    if (lvalue)
      invalid(n);
    *this << "(!" << *n.lhs << " || " << *n.rhs << ")";
  }

  void visit(const IsUndefined &n) final {
    *this << "handle_isundefined(";
    generate_lvalue(*out, *n.expr);
    *this << ")";
  }

  void visit(const Leq &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " <= " << *n.rhs << ")";
  }

  void visit(const Lt &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " < " << *n.rhs << ")";
  }

  void visit(const Mod &n) final {
    if (lvalue)
      invalid(n);
    *this << "mod(s, " << *n.lhs << ", " << *n.rhs << ")";
  }

  void visit(const Mul &n) final {
    if (lvalue)
      invalid(n);
    *this << "mul(s, " << *n.lhs << ", " << *n.rhs << ")";
  }

  void visit(const Negative &n) final {
    if (lvalue)
      invalid(n);
    *this << "negate(s, " << *n.rhs << ")";
  }

  void visit(const Neq &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " != " << *n.rhs << ")";
  }

  void visit(const Not &n) final {
    if (lvalue)
      invalid(n);
    *this << "(!" << *n.rhs << ")";
  }

  void visit(const Number &n) final {
    *out << "VALUE_C(" << n.value << ")";
  }

  void visit(const Or &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.lhs << " || " << *n.rhs << ")";
  }
   
  void visit(const Sub &n) final {
    if (lvalue)
      invalid(n);
    *this << "sub(s, " << *n.lhs << ", " << *n.rhs << ")";
  }

  void visit(const Ternary &n) final {
    if (lvalue)
      invalid(n);
    *this << "(" << *n.cond << " ? " << *n.lhs << " : " << *n.rhs << ")";
  }

  virtual ~Generator() = default;

 private:
  void invalid(const Expr &n) const {
    throw Error("invalid expression used as lvalue", n.loc);
  }
};

}

void generate_lvalue(std::ostream &out, const Expr &e) {
  Generator g(out, true);
  g.dispatch(e);
}

void generate_rvalue(std::ostream &out, const Expr &e) {
  Generator g(out, false);
  g.dispatch(e);
}
