#pragma once

#include <cstddef>
#include <rumur/Node.h>
#include <string>
#include <unordered_map>
#include <vector>

namespace rumur {

// Symbolic context, for maintaining a mapping between Murphi variables and
// external (generated) symbols. This has extremely limited functionality, only
// enough to support the translation to SMT (see smt.h).
class SymContext {

 private:
  // stack of symbol tables, mapping AST unique IDs to external names
  std::vector<std::unordered_map<size_t, std::string>> scope;

  // monotonic counter used for generating unique symbols
  size_t counter = 0;

 public:
  SymContext();

  // descend into or ascend from a variable scope
  void open_scope();
  void close_scope();

  /// add a new known symbol
  ///
  /// This registers the symbol in the current innermost scope.
  ///
  /// \param id Unique identifier of the source AST node
  /// \return A unique name created for this symbol
  std::string register_symbol(size_t id);

  /// lookup a previously registered symbol
  ///
  /// This lookup is performed in all known variable scopes, going from
  /// innermost to outermost in preference order
  ///
  /// \param id Unique identifier of the AST node being looked up
  /// \param origin The node that caused this lookup (used for error
  ///   diagnostics)
  /// \return The unique name this symbol maps to
  std::string lookup_symbol(size_t id, const Node &origin) const;

 private:
  std::string make_symbol();

};

}
