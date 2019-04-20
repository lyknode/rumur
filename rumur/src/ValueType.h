#pragma once

#include <cstddef>
#include <string>

// abstraction over the type used to represent scalar values during checking
struct ValueType {
  std::string c_type;  // C symbol that names the type
  std::string int_min; // equivalent of INT_MIN
  std::string int_max; // equivalent of INT_MAX
  std::string int_c;   // equivalent of INT_C
};

const ValueType &get_value_type(const std::string &name);
