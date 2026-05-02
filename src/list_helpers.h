// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Generic [List<T>] -> [std::vector<T>] flattener for the Crane-extracted
// linked list representation.  Replaces the per-helper copies of the
// same five-line walk that lived in chart_helpers / pdf_helpers /
// tab_bar_helpers.  Lives in its own header so any new consumer of
// [List<U>] can include it without pulling in the rest of imgui_helpers.

#ifndef INCLUDED_LIST_HELPERS
#define INCLUDED_LIST_HELPERS

#include <variant>
#include <vector>

template <typename T> struct List;

namespace list_helpers {

template <typename T>
inline void list_to_vec(const List<T>& xs, std::vector<T>& out) {
  const List<T>* p = &xs;
  while (p &&
         std::holds_alternative<typename List<T>::Cons>(p->v())) {
    const auto& cell = std::get<typename List<T>::Cons>(p->v());
    out.push_back(cell.d_a0);
    p = cell.d_a1.get();
  }
}

}  // namespace list_helpers

#endif  // INCLUDED_LIST_HELPERS
