// functionality related to interacting with a Satisfiability Modulo Theories
// solver

#pragma once

#include <cstddef>
#include <gmpxx.h>
#include <rumur/Expr.h>
#include <rumur/Node.h>
#include <rumur/Number.h>
#include <rumur/SymContext.h>
#include <string>
#include <unordered_map>

namespace rumur {

struct SMTConfig {

  // use bitvectors instead of integers for numeric values?
  bool prefer_bitvectors = false;

  // bit width to use to represent numerical values if using bitvectors
  size_t bitvector_width = 64;

  // various SMT operators whose selection is dependent on context
  std::string add (const Node &origin) const;
  std::string band(const Node &origin) const;
  std::string bnot(const Node &origin) const;
  std::string bor (const Node &origin) const;
  std::string bxor(const Node &origin) const;
  std::string div (const Node &origin) const;
  std::string geq (const Node &origin) const;
  std::string gt  (const Node &origin) const;
  std::string leq (const Node &origin) const;
  std::string lsh (const Node &origin) const;
  std::string lt  (const Node &origin) const;
  std::string mod (const Node &origin) const;
  std::string mul (const Node &origin) const;
  std::string neg (const Node &origin) const;
  std::string rsh (const Node &origin) const;
  std::string sub (const Node &origin) const;
  std::string numeric_literal(const mpz_class &value, const Number &origin) const;

};

// translate a given expression to SMTLIBv2
void to_smt(std::ostream &out, const Expr &n, SymContext &ctxt, SMTConfig &conf);

// wrapper around the above for when you do not need a long lived output buffer
std::string to_smt(const Expr &n, SymContext &ctxt, SMTConfig &conf);

}
