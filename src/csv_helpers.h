// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Item 4: iterative driver for the CSV import scanner.  The Coq
// Fixpoint csv_run in theories/Csv.v stays as the executable spec;
// this loop applies the same per-character step without one extracted
// stack frame per input byte.

#ifndef ROCQSHEET_CSV_HELPERS_H
#define ROCQSHEET_CSV_HELPERS_H

#include <cstdint>
#include <utility>

namespace csv_helpers {

template <typename Cur, typename Step>
inline Cur run_impl(int64_t len, Cur cur, Step&& step) {
  while (cur.cc_next < len) {
    cur = step(std::move(cur));
  }
  return cur;
}

}  // namespace csv_helpers

#endif  // ROCQSHEET_CSV_HELPERS_H
