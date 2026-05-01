// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Tiny recursive-descent parser for spreadsheet formulas.  Produces an
// Expr value from the Crane-extracted [Rocqsheet] module.  Lives on
// the C++ side: the verified Rocq kernel is the evaluator, not the
// parser.

#pragma once

#include "rocqsheet.h"

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

namespace formula {

// Parse a formula source string.  Accepts:
//   * decimal integer literals (overflow into int64 is rejected)
//   * cell references: <letter(s)><1-based row>, bounds-checked
//     against the kernel grid
//   * binary operators + - * / with usual precedence
//   * parentheses, unary minus
//
// Returns std::nullopt on any malformed input or out-of-range literal.
std::optional<Rocqsheet::Expr> parse(std::string_view src);

// Parse a plain (possibly negative) integer literal with optional
// surrounding whitespace.  Rejects overflow into int64.  Returns true
// on success.
bool parse_int_literal(std::string_view src, int64_t& out);

// "<col><row+1>", e.g. (0, 0) -> "A1", (103, 99) -> "CZ100".
std::string label_of(int64_t col, int64_t row);

// Just the column letter(s), e.g. 0 -> "A", 26 -> "AA".
std::string col_label(int64_t col);

}  // namespace formula
