#include <cassert>
#include <cstddef>
#include <iostream>
#include <rumur/rumur.h>
#include <string>
#include <utility>

using namespace rumur;

static std::string escape(const std::string &s) {
  // TODO: use ../../rumur/src/utils.cc:escape()
  return s;
}

namespace {

class CGenerator : public ConstTraversal {

 private:
  std::ostream &out;
  size_t indent_level = 0;

 public:
  explicit CGenerator(std::ostream &out_): out(out_) { }

  // helpers to make output below more natural

  CGenerator &operator<<(const std::string &s) {
    out << s;
    return *this;
  }

  CGenerator &operator<<(const Node &n) {
    dispatch(n);
    return *this;
  }

  void visit_add(const Add &n) final {
    *this << "(" << *n.lhs << " + " << *n.rhs << ")";
  }

  void visit_and(const And &n) final {
    *this << "(" << *n.lhs << " && " << *n.rhs << ")";
  }

  void visit_assignment(const Assignment &n) final {
    *this << indentation() << *n.lhs << " = " << *n.rhs << ";\n";
  }

  void visit_constdecl(const ConstDecl &n) final {
    *this << indentation() << "const ";
    if (n.type == nullptr) {
      *this << "__auto_type";
    } else {
      *this << *n.type;
    }
    *this << " " << n.name << " = " << *n.value << ";\n";
  }

  void visit_div(const Div &n) final {
    *this << "(" << *n.lhs << " / " << *n.rhs << ")";
  }

  void visit_element(const Element &n) final {
    *this << "(" << *n.array << "[" << *n.index << "])";
  }

  void visit_enum(const Enum &n) final {
    *this << "enum { ";
    for (const std::pair<std::string, location> &m : n.members) {
      *this << m.first << ", ";
    }
    *this << "}";
  }

  void visit_eq(const Eq &n) final {
    *this << "(" << *n.lhs << " == " << *n.rhs << ")";
  }

  void visit_errorstmt(const ErrorStmt &n) final {
    *this << "error(\"" << escape(n.message) << "\")";
  }

  void visit_exprid(const ExprID &n) final {
    *this << "(" << n.id << ")";
  }

  void visit_field(const Field &n) final {
    *this << "(" << *n.record << "." << n.field << ")";
  }

  void visit_function(const Function &n) final {
    *this << indentation();
    if (n.return_type == nullptr) {
      *this << "void";
    } else {
      *this << *n.return_type;
    }
    *this << " " << n.name << "(";
    bool first = true;
    for (const Ptr<VarDecl> &p : n.parameters) {
      if (!first) {
        *this << ", ";
      }
      *this << *p->type << " ";
      // if this is a var parameter, it needs to be a pointer
      if (!p->readonly) {
        *this << "*" << p->name << "_";
      } else {
        *this << p->name;
      }
      first = false;
    }
    *this << ") {\n";
    indent();
    // provide aliases of var parameters under their original name
    for (const Ptr<VarDecl> &p : n.parameters) {
      if (!p->readonly) {
        *this << "#define " << p->name << " (*" << p->name << "_)\n";
      }
    }
    for (const Ptr<Decl> &d : n.decls) {
      *this << *d;
    }
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    // clean up var aliases
    for (const Ptr<VarDecl> &p : n.parameters) {
      if (!p->readonly) {
        *this << "#undef " << p->name << "\n";
      }
    }
    dedent();
    *this << "}\n";
  }

  void visit_functioncall(const FunctionCall &n) final {
    *this << n.name << "(";
    assert(n.function != nullptr && "unresolved function call in AST");
    auto it = n.function->parameters.begin();
    bool first = true;
    for (const Ptr<Expr> &a : n.arguments) {
      if (!first) {
        *this << ", ";
      }
      if (!(*it)->readonly) {
        *this << "&";
      }
      *this << *a;
      first = false;
      it++;
    }
    *this << ")";
  }

  void visit_geq(const Geq &n) final {
    *this << "(" << *n.lhs << " >= " << *n.rhs << ")";
  }

  void visit_gt(const Gt &n) final {
    *this << "(" << *n.lhs << " > " << *n.rhs << ")";
  }

  void visit_if(const If &n) final {
    bool first = true;
    for (const IfClause &c : n.clauses) {
      if (first) {
        *this << indentation();
      } else {
        *this << " else ";
      }
      dispatch(c);
      first = false;
    }
    *this << "\n";
  }

  void visit_ifclause(const IfClause &n) final {
    if (n.condition != nullptr) {
      *this << "if " << *n.condition << " ";
    }
    *this << "{\n";
    indent();
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    dedent();
    *this << indentation() << "}";
  }

  void visit_implication(const Implication &n) final {
    *this << "(!" << *n.lhs << " || " << *n.rhs << ")";
  }

  void visit_isundefined(const IsUndefined&) final {
    // TODO: check and prevent instances of this from appearing at this point
  }

  void visit_leq(const Leq &n) final {
    *this << "(" << *n.lhs << " <= " << *n.rhs << ")";
  }

  void visit_lt(const Lt &n) final {
    *this << "(" << *n.lhs << " < " << *n.rhs << ")";
  }

  void visit_mod(const Mod &n) final {
    *this << "(" << *n.lhs << " % " << *n.rhs << ")";
  }

  void visit_mul(const Mul &n) final {
    *this << "(" << *n.lhs << " * " << *n.rhs << ")";
  }

  void visit_negative(const Negative &n) final {
    *this << "(-" << *n.rhs << ")";
  }

  void visit_neq(const Neq &n) final {
    *this << "(" << *n.lhs << " != " << *n.rhs << ")";
  }

  void visit_not(const Not &n) final {
    *this << "(!" << *n.rhs << ")";
  }

  void visit_number(const Number &n) final {
    *this << "(" << n.value.get_str() << ")";
  }

  void visit_or(const Or &n) final {
    *this << "(" << *n.lhs << " || " << *n.rhs << ")";
  }

  void visit_procedurecall(const ProcedureCall &n) final {
    *this << indentation() << n.call << ";\n";
  }

  void visit_put(const Put &n) final {
    *this << indentation() << "printf(";
    if (n.expr == nullptr) {
      *this << "\"%s\\n\", \"" << escape(n.value) << "\")";
    } else {
      *this << "\"%\" PRId64 \"\\n\", " << *n.expr << ")";
    }
    *this << ";\n";
  }

  void visit_range(const Range&) final {
    *this << "int64_t";
  }

  void visit_record(const Record &n) final {
    *this << "struct {\n";
    indent();
    for (const Ptr<VarDecl> &f : n.fields) {
      *this << indentation() << *f << ";\n";
    }
    dedent();
    *this << indentation() << "}";
  }

  void visit_return(const Return &n) final {
    *this << indentation() << "return";
    if (n.expr != nullptr) {
      *this << " " << *n.expr;
    }
    *this << ";\n";
  }

  void visit_scalarset(const Scalarset&) final {
    *this << "int64_t";
  }

  void visit_simplerule(const SimpleRule &n) final {
    // TODO: rules with non-symbol names
    *this << indentation() << "bool guard_" << n.name << "() {\n";
    indent();
    *this << indentation() << "return ";
    if (n.guard == nullptr) {
      *this << "true";
    } else {
      *this << *n.guard;
    }
    *this << ";\n";
    dedent();
    *this << indentation() << "}\n\n";

    *this << indentation() << "void rule_" << n.name << "() {\n";
    indent();
    for (const Ptr<Decl> &d : n.decls) {
      *this << *d;
    }
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    dedent();
    *this << indentation() << "}\n";
  }

  void visit_startstate(const StartState &n) final {
    // TODO: startstates with non-symbol names
    *this << indentation() << "void startstate_" << n.name << "() {\n";
    indent();
    for (const Ptr<Decl> &d : n.decls) {
      *this << *d;
    }
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    dedent();
    *this << indentation() << "}\n\n";
  }

  void visit_sub(const Sub &n) final {
    *this << "(" << *n.lhs << " - " << *n.rhs << ")";
  }

  void visit_switch(const Switch &n) final {
    // TODO: handle cases where expression or cases are not primitives
    *this << indentation() << "switch " << *n.expr << " {\n\n";
    indent();
    for (const SwitchCase &c : n.cases) {
      *this << c << "\n";
    }
    dedent();
    *this << indentation() << "}\n";
  }

  void visit_switchcase(const SwitchCase &n) final {
    if (n.matches.empty()) {
      *this << indentation() << "default:\n";
    } else {
      for (const Ptr<Expr> &m : n.matches) {
        *this << indentation() << "case " << *m << ":\n";
      }
    }
    indent();
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    *this << indentation() << "break;\n";
    dedent();
  }

  void visit_ternary(const Ternary &n) final {
    *this << "(" << *n.cond << " ? " << *n.lhs << " : " << *n.rhs << ")";
  }

  void visit_typedecl(const TypeDecl &n) final {
    *this << indentation() << "typedef " << *n.value << " " << n.name << ";\n";
  }

  void visit_typeexprid(const TypeExprID &n) final {
    *this << n.name;
  }

  void visit_vardecl(const VarDecl &n) final {
    *this << indentation() << *n.type << " " << n.name << ";\n";
  }

  void visit_while(const While &n) final {
    *this << indentation() << "while " << *n.condition << " {\n";
    indent();
    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }
    dedent();
    *this << indentation() << "}\n";
  }

  virtual ~CGenerator() = default;

 private:
  std::string indentation() const {
    return std::string(indent_level * 2, ' ');
  }

  void indent() {
    indent_level++;
  }

  void dedent() {
    assert(indent_level > 0 && "attempted negative indentation");
    indent_level--;
  }
};

}

void generate_c(const Node &n, std::ostream &out) {
  CGenerator gen(out);
  gen.dispatch(n);
}
