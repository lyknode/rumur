#include <cstddef>
#include <rumur/except.h>
#include <rumur/Node.h>
#include <rumur/SymContext.h>
#include <string>
#include <unordered_map>

namespace rumur {

SymContext::SymContext() {
  open_scope();
}

void SymContext::open_scope() {
  scope.push_back(std::unordered_map<size_t, std::string>{});
}

void SymContext::close_scope() {
  scope.pop_back();
  // TODO: we probably need to record symbols somewhere
}

std::string SymContext::register_symbol(size_t id) {
  // invent a new symbol and map this ID to it
  std::string s = make_symbol();
  scope.back()[id] = s;
  return s;
}

std::string SymContext::lookup_symbol(size_t id, const Node &origin) const {

  // lookup the symbol in enclosing scopes from innermost to outermost
  for (auto it = scope.rbegin(); it != scope.rend(); ++it) {
    auto it2 = it->find(id);
    if (it2 != it->end())
      return it2->second;
  }

  // we expect any symbol encountered in a well-formed AST to be associated with
  // a previously encountered definition
  throw Error("unknown symbol encountered; applying SMT translation to an "
    "unvalidated AST?", origin.loc);
}

std::string SymContext::make_symbol() {
  return "s" + std::to_string(counter++);
}

}
