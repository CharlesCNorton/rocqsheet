// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Implementation of [imgui_helpers::tab_bar_select].  Lives in its own
// .cpp so the full body of [List<std::string>] is visible (the header
// only forward-declares the List template to avoid the
// [Rocqsheet::Cell] forward-declaration tangle).

#include "imgui_helpers.h"
#include "rocqsheet.h"

#include <imgui.h>

#include <cstdio>
#include <string>
#include <variant>
#include <vector>

namespace imgui_helpers {

int64_t tab_bar_select(const std::string& id,
                       const List<std::string>& names,
                       int64_t /*current*/) {
  std::vector<std::string> name_vec;
  const List<std::string>* p = &names;
  while (p &&
         std::holds_alternative<typename List<std::string>::Cons>(p->v())) {
    const auto& cell =
        std::get<typename List<std::string>::Cons>(p->v());
    name_vec.push_back(cell.d_a0);
    p = cell.d_a1.get();
  }

  int64_t result = 0;
  if (ImGui::BeginTabBar(id.c_str(), ImGuiTabBarFlags_Reorderable)) {
    int64_t num_tabs = static_cast<int64_t>(name_vec.size());
    if (num_tabs == 0) num_tabs = 16;
    for (int64_t i = 0; i < num_tabs; ++i) {
      std::string display = (i < static_cast<int64_t>(name_vec.size()) &&
                             !name_vec[static_cast<size_t>(i)].empty())
          ? name_vec[static_cast<size_t>(i)]
          : ("Sheet " + std::to_string(i + 1));
      char suffix[32];
      std::snprintf(suffix, sizeof(suffix), "###t%lld",
                    static_cast<long long>(i));
      std::string label = display + suffix;
      if (ImGui::BeginTabItem(label.c_str())) {
        result = i;
        ImGui::EndTabItem();
      }
    }
    ImGui::EndTabBar();
  }
  return result;
}

}  // namespace imgui_helpers
