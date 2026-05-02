// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Iterative find/replace for sheets, expanded at the call site so the
// nested [Rocqsheet::Sheet] / [Rocqsheet::Cell] / [Rocqsheet::Expr]
// types are visible without forcing this header to depend on the
// generated rocqsheet.h (which would create a cycle through Crane's
// `From` include directive).
//
// The Coq-extracted [replace_in_sheet] used to be a Fixpoint with
// nat fuel = 60000 that recursed once per cell, each frame holding a
// full [persistent_array<Cell>] by value.  The generated tail
// recursion was not actually TCO'd by clang/gcc because the parameter
// has a non-trivial destructor (shared_ptr release), so the call
// segfaulted on stacks of even a few thousand formula cells under -O3.
// The macro below expands to a single iterative loop that walks the
// sheet in place, exercising persistent_array's rvalue [set] overload
// for O(1) per-cell updates while we hold the unique handle.

#ifndef INCLUDED_FIND_REPLACE_HELPERS
#define INCLUDED_FIND_REPLACE_HELPERS

#include <cstdint>
#include <utility>
#include <variant>

#define ROCQSHEET_REPLACE_IN_SHEET(from_, to_, sheet_) \
  ([&]() -> ::Rocqsheet::Sheet { \
    int64_t _frep_from = static_cast<int64_t>(from_); \
    int64_t _frep_to = static_cast<int64_t>(to_); \
    ::Rocqsheet::Sheet _frep_s = (sheet_); \
    for (int64_t _frep_i = 0; \
         _frep_i < ::Rocqsheet::GRID_SIZE; ++_frep_i) { \
      ::Rocqsheet::Cell _frep_c = _frep_s.get(_frep_i); \
      if (std::holds_alternative< \
              typename ::Rocqsheet::Cell::CForm>(_frep_c.v())) { \
        const auto& _frep_alt = std::get< \
            typename ::Rocqsheet::Cell::CForm>(_frep_c.v()); \
        ::Rocqsheet::Expr _frep_new = \
            ::FindReplace::replace_int_in_expr( \
                _frep_from, _frep_to, _frep_alt.d_a0); \
        _frep_s = std::move(_frep_s).set( \
            _frep_i, ::Rocqsheet::Cell::cform(std::move(_frep_new))); \
      } \
    } \
    return _frep_s; \
  })()

#endif  // INCLUDED_FIND_REPLACE_HELPERS
