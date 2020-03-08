#include <cstddef>
#include "CLikeGenerator.h"
#include "generate_c.h"
#include <iostream>
#include "options.h"
#include "resources.h"
#include <rumur/rumur.h>
#include <string>

using namespace rumur;

namespace {

class CGenerator : public CLikeGenerator {

 public:
  CGenerator(std::ostream &out_, bool pack_): CLikeGenerator(out_, pack_) { }

  void visit_constdecl(const ConstDecl &n) final {
    *this << indentation() << "const ";
    if (n.type == nullptr) {
      *this << value_type;
    } else {
      *this << *n.type;
    }
    *this << " " << n.name << " = " << *n.value << ";\n";
  }

  void visit_function(const Function &n) final {
    *this << indentation();
    if (n.return_type == nullptr) {
      *this << "void";
    } else {
      *this << *n.return_type;
    }
    *this << " " << n.name << "(";
    if (n.parameters.empty()) {
      *this << "void";
    } else {
      std::string sep;
      for (const Ptr<VarDecl> &p : n.parameters) {
        *this << sep << *p->type << " ";
        // if this is a var parameter, it needs to be a pointer
        if (!p->readonly) {
          *this << "*" << p->name << "_";
        } else {
          *this << p->name;
        }
        sep = ", ";
      }
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

  void visit_propertyrule(const PropertyRule &n) final {

    // function prototype
    *this << indentation() << "bool " << n.name << "(";

    // parameters
    if (n.quantifiers.empty()) {
      *this << "void";
    } else {
      std::string sep;
      for (const Quantifier &q : n.quantifiers) {
        *this << sep;
        if (auto t = dynamic_cast<const TypeExprID*>(q.type.get())) {
          *this << t->name;
        } else {
          *this << value_type;
        }
        *this << " " << q.name;
        sep = ", ";
      }
    }

    *this << ") {\n";
    indent();

    // any aliases this property uses
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << *a;
    }

    *this << indentation() << "return " << *n.property.expr << ";\n";

    // clean up any aliases we defined
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << "#undef " << a->name << "\n";
    }

    dedent();
    *this << "}\n";
  }

  void visit_simplerule(const SimpleRule &n) final {
    *this << indentation() << "bool guard_" << n.name << "(";

    // parameters
    if (n.quantifiers.empty()) {
      *this << "void";
    } else {
      std::string sep;
      for (const Quantifier &q : n.quantifiers) {
        *this << sep;
        if (auto t = dynamic_cast<const TypeExprID*>(q.type.get())) {
          *this << t->name;
        } else {
          *this << value_type;
        }
        *this << " " << q.name;
        sep = ", ";
      }
    }

    *this << ") {\n";
    indent();

    // any aliases that are defined in an outer scope
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << *a;
    }

    *this << indentation() << "return ";
    if (n.guard == nullptr) {
      *this << "true";
    } else {
      *this << *n.guard;
    }
    *this << ";\n";

    // clean up aliases
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << "#undef " << a->name << "\n";
    }

    dedent();
    *this << indentation() << "}\n\n";

    *this << indentation() << "void rule_" << n.name << "(";

    // parameters
    if (n.quantifiers.empty()) {
      *this << "void";
    } else {
      std::string sep;
      for (const Quantifier &q : n.quantifiers) {
        *this << sep;
        if (auto t = dynamic_cast<const TypeExprID*>(q.type.get())) {
          *this << t->name;
        } else {
          *this << value_type;
        }
        *this << " " << q.name;
        sep = ", ";
      }
    }

    *this << ") {\n";
    indent();

    // aliases, variables, local types, etc.
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << *a;
    }
    for (const Ptr<Decl> &d : n.decls) {
      *this << *d;
    }

    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }

    // clean up any aliases we defined
    for (const Ptr<Decl> &d : n.decls) {
      if (auto a = dynamic_cast<const AliasDecl*>(d.get())) {
        *this << "#undef " << a->name << "\n";
      }
    }
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << "#undef " << a->name << "\n";
    }

    dedent();
    *this << indentation() << "}\n";
  }

  void visit_startstate(const StartState &n) final {
    *this << indentation() << "void startstate_" << n.name << "(";

    // parameters
    if (n.quantifiers.empty()) {
      *this << "void";
    } else {
      std::string sep;
      for (const Quantifier &q : n.quantifiers) {
        *this << sep;
        if (auto t = dynamic_cast<const TypeExprID*>(q.type.get())) {
          *this << t->name;
        } else {
          *this << value_type;
        }
        *this << " " << q.name;
        sep = ", ";
      }
    }

    *this << ") {\n";
    indent();

    // aliases, variables, local types, etc.
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << *a;
    }
    for (const Ptr<Decl> &d : n.decls) {
      *this << *d;
    }

    for (const Ptr<Stmt> &s : n.body) {
      *this << *s;
    }

    // clean up any aliases we defined
    for (const Ptr<Decl> &d : n.decls) {
      if (auto a = dynamic_cast<const AliasDecl*>(d.get())) {
        *this << "#undef " << a->name << "\n";
      }
    }
    for (const Ptr<AliasDecl> &a : n.aliases) {
      *this << "#undef " << a->name << "\n";
    }

    dedent();
    *this << indentation() << "}\n\n";
  }

  void visit_vardecl(const VarDecl &n) final {
    *this << indentation() << *n.type << " " << n.name << ";\n";
  }

  virtual ~CGenerator() = default;
};

}

void generate_c(const Node &n, bool pack, std::ostream &out) {

  // write the static prefix to the beginning of the source file
  for (size_t i = 0; i < resources_c_prefix_c_len; i++)
    out << (char)resources_c_prefix_c[i];

  CGenerator gen(out, pack);
  gen.dispatch(n);
}
