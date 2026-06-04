// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Iterative driver for the status-bar sheet aggregate.  The Coq
// Fixpoint in theories/Render.v stays as the executable spec; this
// loop applies the same per-cell step without one stack frame per
// grid cell (the extracted recursion segfaulted at GRID_SIZE depth).

#ifndef ROCQSHEET_STATUS_HELPERS_H
#define ROCQSHEET_STATUS_HELPERS_H

#include <cstdint>
#include <utility>

namespace status_helpers {

template <typename Agg, typename Step>
inline Agg aggregate_impl(int64_t grid_size, Agg acc, Step&& step) {
  for (int64_t i = 0; i < grid_size; ++i) {
    acc = step(std::move(acc), i);
  }
  return acc;
}

}  // namespace status_helpers

#endif  // ROCQSHEET_STATUS_HELPERS_H
