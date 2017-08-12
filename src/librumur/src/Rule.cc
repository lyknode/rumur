#include "location.hh"
#include <rumur/Decl.h>
#include <rumur/Expr.h>
#include <rumur/Rule.h>
#include <rumur/Stmt.h>
#include <string>
#include <vector>

using namespace rumur;
using namespace std;

Rule::Rule(const string &name, Expr *guard, vector<Decl*> &&decls,
  vector<Stmt*> &&body, const location &loc)
  : Node(loc), name(name), guard(guard), decls(decls), body(body) {
}

Rule::~Rule() {
    delete guard;
    for (Decl *d : decls)
        delete d;
    for (Stmt *s : body)
        delete s;
}

/* XXX: Why do we need the explicit moves here? I assumed that we could
 * transparently forward the rvalue references, but it seems they need to be
 * bound to lvalue references which does not happen automatically.
 */
StartState::StartState(const string &name, vector<Decl*> &&decls,
  vector<Stmt*> &&body, const location &loc)
  : Rule(name, nullptr, move(decls), move(body), loc) {
}
