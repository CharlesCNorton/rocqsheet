// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Saturating integer arithmetic on int64_t.  The Coq model in
// theories/Saturation.v is point-wise equivalent to these inline
// definitions: addition, subtraction, multiplication clamp to
// INT64_MIN/INT64_MAX on overflow; division and modulo handle the
// INT64_MIN / -1 corner and divide-by-zero by returning 0 for the
// modulo and 0 / INT64_MIN for the div, matching the Saturation.v
// definitions.

#pragma once

#include <cstdint>

namespace rocqsheet {

inline int64_t sat_add(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_add_overflow(a, b, &r)) {
    return (a < 0) ? INT64_MIN : INT64_MAX;
  }
  return r;
}

inline int64_t sat_sub(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_sub_overflow(a, b, &r)) {
    return (a < 0) ? INT64_MIN : INT64_MAX;
  }
  return r;
}

inline int64_t sat_mul(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_mul_overflow(a, b, &r)) {
    return ((a < 0) != (b < 0)) ? INT64_MIN : INT64_MAX;
  }
  return r;
}

inline int64_t sat_div(int64_t a, int64_t b) {
  if (b == 0) return INT64_C(0);
  if (a == INT64_MIN && b == -1) return INT64_MIN;
  return a / b;
}

inline int64_t sat_mod(int64_t a, int64_t b) {
  if (b == 0) return INT64_C(0);
  if (a == INT64_MIN && b == -1) return INT64_C(0);
  return a % b;
}

}  // namespace rocqsheet
