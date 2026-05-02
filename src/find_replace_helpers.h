// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Iterative find/replace for sheets, instantiated at the call site so
// the nested [Rocqsheet::Cell] / [Rocqsheet::Expr] types can stay
// opaque to this header.  The function is a template parameterized on
// the cell type and a per-cell rewriter callback; both are deduced
// where the call lands inside the extracted rocqsheet.cpp where the
// Rocqsheet types are fully visible.
//
// Replaces the deeply-recursive Coq-extracted [replace_in_sheet]
// (Fixpoint with nat fuel = 60000) whose tail recursion was not TCO'd
// by clang/gcc because the [persistent_array<Cell>] parameter has a
// non-trivial destructor (shared_ptr release), and therefore segfaulted
// on stacks of even a few thousand formula cells under -O3.

#ifndef INCLUDED_FIND_REPLACE_HELPERS
#define INCLUDED_FIND_REPLACE_HELPERS

#include <cstdint>
#include <utility>
#include <variant>

template <typename T> class persistent_array;

namespace find_replace_helpers {

template <typename Cell, typename Replace>
inline persistent_array<Cell> replace_in_sheet_impl(
    int64_t grid_size, persistent_array<Cell> sheet, Replace replace) {
  for (int64_t i = 0; i < grid_size; ++i) {
    Cell c = sheet.get(i);
    if (std::holds_alternative<typename Cell::CForm>(c.v())) {
      const auto& alt = std::get<typename Cell::CForm>(c.v());
      sheet = std::move(sheet).set(
          i, Cell::cform(replace(alt.d_a0)));
    }
  }
  return sheet;
}

}  // namespace find_replace_helpers

#endif  // INCLUDED_FIND_REPLACE_HELPERS
