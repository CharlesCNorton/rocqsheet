// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Forward-declared chart drawing helper.  The implementation lives in
// chart_helpers.cpp where it can include the generated rocqsheet.h
// for the full [List<int64_t>] body — this header keeps a forward
// declaration so the Crane-extracted side can call it without
// re-introducing a circular include.

#ifndef INCLUDED_CHART_HELPERS
#define INCLUDED_CHART_HELPERS

#include <cstdint>
#include <string>

template <typename T> struct List;

namespace chart_helpers {

void chart_render(int64_t kind, const List<int64_t>& values,
                  const std::string& title);

}  // namespace chart_helpers

#endif  // INCLUDED_CHART_HELPERS
