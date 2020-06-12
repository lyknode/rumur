#include <cstddef>
#include <gmpxx.h>
#include "optimise-field-ordering.h"
#include <rumur/rumur.h>
#include <vector>

using namespace rumur;

// is this value a power of 2?
static bool is_onehot(mpz_class v) {

  if (v == 0)
    return false;

  return mpz_popcount(v.get_mpz_t()) == 1;
}

// compare two fields based on size
static bool comp(const Ptr<VarDecl> &a, const Ptr<VarDecl> &b) {

  mpz_class width_a = a->type->width();
  mpz_class width_b = b->type->width();

  // zero-width fields trump anything else
  if (width_a == 0) {
    return true;
  } else if (width_b == 0) {
    return false;
  }

  // power-of-2 fields trump non-power-of-2 fields
  if (is_onehot(width_a) && !is_onehot(width_b))
    return true;
  if (!is_onehot(width_a) && is_onehot(width_b))
    return false;

  // otherwise, order based on larger fields first
  return width_a > width_b;
}

// sort a collection of fields
static void sort(std::vector<Ptr<VarDecl>> &fields) {
  std::sort(fields.begin(), fields.end(), comp);
}

// a traversal that reorders fields
namespace { class Reorderer : public Traversal {

 public:
  void visit_model(Model &n) final {

    // first act on our children
    for (Ptr<Decl> &d : n.decls)
      dispatch(*d);
    for (Ptr<Function> &f : n.functions)
      dispatch(*f);
    for (Ptr<Rule> &r : n.rules)
      dispatch(*r);

    // separate our fields into VarDecls and the rest
    std::vector<Ptr<VarDecl>> vars;
    std::vector<Ptr<Decl>> other;
    for (Ptr<Decl> &d : n.decls) {
      if (auto v = dynamic_cast<VarDecl*>(d.get())) {
         auto vp = Ptr<VarDecl>::make(*v);
         vars.push_back(vp);
      } else {
        other.push_back(d);
      }
    }

    // sort the variables
    sort(vars);

    // the offset of each variable within the model state is now inaccurate, so
    // update this information
    mpz_class offset = 0;
    for (Ptr<VarDecl> &v : vars) {
      v->offset = offset;
      offset += v->type->width();
    }

    // overwrite our declarations with the new ordering
    other.insert(other.end(), vars.begin(), vars.end());
    n.decls = other;
  }

  void visit_record(Record &n) final {

    // first act on our children
    for (Ptr<VarDecl> &f : n.fields)
      dispatch(*f);

    // sort the fields of the record itself
    sort(n.fields);
  }
}; }

void optimise_field_ordering(Model &m) {
  Reorderer r;
  r.dispatch(m);
}
