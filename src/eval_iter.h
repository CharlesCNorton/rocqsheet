// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Iterative C++ evaluator that mirrors the Rocq specification in
// theories/Rocqsheet.v.  Crane extracts [eval_expr] as native C++
// recursion, which blows the call stack on deep formulas; this
// implementation walks the same logic with an explicit heap-allocated
// continuation stack so the only growth is in std::vector.
//
// The Rocq side is the spec; this is the implementation.  They match
// step-for-step (visited-set cycle detection, signed Z arithmetic with
// saturation, divide-by-zero -> nullopt, empty/literal cells dispatched
// before recursion).

#pragma once

#include "rocqsheet.h"

#include <cstdint>
#include <optional>

namespace formula {

// Evaluate cell [ref] in [sheet], returning std::nullopt on cycle,
// divide-by-zero, or any other failure mode.  No fuel: termination
// is guaranteed by the visited-set bound and finite Expr depth.
std::optional<int64_t> eval_iter(
    const Rocqsheet::Sheet& sheet,
    const Rocqsheet::CellRef& ref);

}  // namespace formula
