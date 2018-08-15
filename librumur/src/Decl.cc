#include <gmpxx.h>
#include <iostream>
#include "location.hh"
#include <memory>
#include <rumur/Decl.h>
#include <rumur/except.h>
#include <rumur/Expr.h>
#include <rumur/Node.h>
#include <string>

namespace rumur {

Decl::Decl(const std::string &name_, const location &loc_):
  Node(loc_), name(name_) {
}

Decl::~Decl() {
}

ConstDecl::ConstDecl(const std::string &name_, std::shared_ptr<Expr> value_,
  const location &loc_):
  Decl(name_, loc_), value(value_) {
  validate();
}

ConstDecl::ConstDecl(const std::string &name_, std::shared_ptr<Expr> value_,
  std::shared_ptr<TypeExpr> type_, const location &loc_):
  Decl(name_, loc_), value(value_), type(type_) {
  validate();
}

ConstDecl::ConstDecl(const ConstDecl &other):
  Decl(other), value(other.value->clone()), type(other.type) {
}

ConstDecl &ConstDecl::operator=(ConstDecl other) {
  swap(*this, other);
  return *this;
}

void swap(ConstDecl &x, ConstDecl &y) noexcept {
  using std::swap;
  swap(x.loc, y.loc);
  swap(x.name, y.name);
  swap(x.value, y.value);
  swap(x.type, y.type);
}

ConstDecl *ConstDecl::clone() const {
  return new ConstDecl(*this);
}

bool ConstDecl::operator==(const Node &other) const {
  auto o = dynamic_cast<const ConstDecl*>(&other);
  if (o == nullptr)
    return false;
  if (name != o->name)
    return false;
  if (*value != *o->value)
    return false;
  if (type == nullptr) {
    if (o->type != nullptr)
      return false;
  } else {
    if (o->type == nullptr)
      return false;
    if (*type != *o->type)
      return false;
  }
  return true;
}

void ConstDecl::validate() const {
  if (!value->constant())
    throw Error("const definition is not a constant", value->loc);
}

TypeDecl::TypeDecl(const std::string &name_, std::shared_ptr<TypeExpr> value_,
  const location &loc_):
  Decl(name_, loc_), value(value_) {
}

TypeDecl::TypeDecl(const TypeDecl &other):
  Decl(other), value(other.value->clone()) {
}

TypeDecl &TypeDecl::operator=(TypeDecl other) {
  swap(*this, other);
  return *this;
}

void swap(TypeDecl &x, TypeDecl &y) noexcept {
  using std::swap;
  swap(x.loc, y.loc);
  swap(x.name, y.name);
  swap(x.value, y.value);
}

TypeDecl *TypeDecl::clone() const {
  return new TypeDecl(*this);
}

#if 0
void TypeDecl::generate(std::ostream &out) const {
  out << "using ru_u_" << name << " = " << *value;
}
#endif

bool TypeDecl::operator==(const Node &other) const {
  auto o = dynamic_cast<const TypeDecl*>(&other);
  return o != nullptr && name == o->name && *value == *o->value;
}

VarDecl::VarDecl(const std::string &name_, std::shared_ptr<TypeExpr> type_,
  const location &loc_):
  Decl(name_, loc_), type(type_) {
}

VarDecl::VarDecl(const VarDecl &other):
  Decl(other), type(other.type->clone()), state_variable(other.state_variable),
  offset(other.offset) { }

VarDecl &VarDecl::operator=(VarDecl other) {
  swap(*this, other);
  return *this;
}

void swap(VarDecl &x, VarDecl &y) noexcept {
  using std::swap;
  swap(x.loc, y.loc);
  swap(x.name, y.name);
  swap(x.type, y.type);
  swap(x.state_variable, y.state_variable);
  swap(x.offset, y.offset);
}

VarDecl *VarDecl::clone() const {
  return new VarDecl(*this);
}

#if 0
void VarDecl::generate(std::ostream &out) const {
  if (state_variable) {
    out << "using ru_u_" << name << " = " << *type;
  } else {
    out << "auto ru_u_" << name << " = " << *type << "::make()";
  }
}
#endif

bool VarDecl::operator==(const Node &other) const {
  auto o = dynamic_cast<const VarDecl*>(&other);
  return o != nullptr && name == o->name && *type == *o->type
      && state_variable == o->state_variable && offset == o->offset;
}

mpz_class VarDecl::width() const {
  return type->width();
}

mpz_class VarDecl::count() const {
  return type->count();
}

void VarDecl::generate_print(std::ostream &out, const std::string &prefix,
  mpz_class preceding_offset) const {

  type->generate_print(out, prefix + name, preceding_offset);
}

}
