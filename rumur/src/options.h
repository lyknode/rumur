#pragma once

#include <cstddef>
#include <cstdint>

enum tristate {
  OFF,
  ON,
  AUTO,
};

enum trace_category_t {
  TC_HANDLE_READS       =  0x1,
  TC_HANDLE_WRITES      =  0x2,
  TC_QUEUE              =  0x4,
  TC_SET                =  0x8,
  TC_SYMMETRY_REDUCTION = 0x10,
};

struct Options {
  bool overflow_checks;
  unsigned long threads;
  bool debug;
  size_t set_capacity;

  /* Limit (percentage occupancy) at which we expand the capacity of the state
   * set.
   */
  unsigned long set_expand_threshold;

  // Whether to use ANSI colour codes in the checker's output.
  tristate color;

  // Bitmask of enabled tracing
  uint64_t traces;

  // Deadlock detection enabled?
  bool deadlock_detection;

  // Symmetry reduction enabled?
  bool symmetry_reduction;

  // Use OS mechanisms to sandbox the checker?
  bool sandbox_enabled;

  // Number of errors to report before exiting.
  unsigned long max_errors;
};

extern Options options;