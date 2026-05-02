// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.

#include "chart_helpers.h"
#include "rocqsheet.h"

#include <imgui.h>

#include <algorithm>
#include <cmath>
#include <vector>

namespace chart_helpers {

namespace {

void list_to_vec(const List<int64_t>& xs, std::vector<int64_t>& out) {
  const List<int64_t>* p = &xs;
  while (p && std::holds_alternative<typename List<int64_t>::Cons>(p->v())) {
    const auto& cell = std::get<typename List<int64_t>::Cons>(p->v());
    out.push_back(cell.d_a0);
    p = cell.d_a1.get();
  }
}

}  // namespace

void chart_render(int64_t kind, const List<int64_t>& values,
                  const std::string& title) {
  std::vector<int64_t> vs;
  list_to_vec(values, vs);

  ImVec2 pos = ImGui::GetCursorScreenPos();
  const ImVec2 size{320.0f, 160.0f};
  ImDrawList* dl = ImGui::GetWindowDrawList();
  dl->AddRectFilled(pos, {pos.x + size.x, pos.y + size.y},
                    IM_COL32(30, 30, 36, 255));
  dl->AddRect(pos, {pos.x + size.x, pos.y + size.y},
              IM_COL32(120, 120, 140, 255));

  if (vs.empty()) {
    if (!title.empty())
      dl->AddText({pos.x + 6, pos.y + 2},
                  IM_COL32(220, 220, 220, 255), title.c_str());
    ImGui::Dummy(size);
    return;
  }

  int64_t lo = vs[0], hi = vs[0];
  for (auto v : vs) {
    if (v < lo) lo = v;
    if (v > hi) hi = v;
  }
  if (lo == hi) hi = lo + 1;
  const float range = static_cast<float>(hi - lo);
  const ImVec2 inner_pos{pos.x + 6.0f, pos.y + 18.0f};
  const ImVec2 inner_size{size.x - 12.0f, size.y - 24.0f};

  switch (kind) {
    case 0: {
      if (vs.size() < 2) {
        float x = inner_pos.x + inner_size.x / 2;
        float y = inner_pos.y + inner_size.y / 2;
        dl->AddCircleFilled({x, y}, 3.0f, IM_COL32(120, 220, 120, 255));
      } else {
        for (size_t i = 1; i < vs.size(); ++i) {
          float x0 = inner_pos.x +
                     inner_size.x * (i - 1) / (vs.size() - 1);
          float x1 = inner_pos.x +
                     inner_size.x * i / (vs.size() - 1);
          float y0 = inner_pos.y +
                     inner_size.y * (1.0f - (vs[i - 1] - lo) / range);
          float y1 = inner_pos.y +
                     inner_size.y * (1.0f - (vs[i] - lo) / range);
          dl->AddLine({x0, y0}, {x1, y1},
                      IM_COL32(80, 200, 80, 255), 1.5f);
        }
      }
      break;
    }
    case 1: {
      float bw = inner_size.x / static_cast<float>(vs.size());
      for (size_t i = 0; i < vs.size(); ++i) {
        float x0 = inner_pos.x + bw * static_cast<float>(i) + 1;
        float x1 = inner_pos.x + bw * static_cast<float>(i + 1) - 1;
        float h = inner_size.y * (vs[i] - lo) / range;
        float y0 = inner_pos.y + inner_size.y - h;
        float y1 = inner_pos.y + inner_size.y;
        dl->AddRectFilled({x0, y0}, {x1, y1},
                          IM_COL32(80, 120, 220, 255));
      }
      break;
    }
    case 2: {
      double total = 0;
      for (auto v : vs) if (v > 0) total += static_cast<double>(v);
      if (total <= 0) break;
      double angle = -3.14159265 / 2;
      ImVec2 c{inner_pos.x + inner_size.x / 2,
               inner_pos.y + inner_size.y / 2};
      float r = std::min(inner_size.x, inner_size.y) / 2 - 4;
      for (size_t i = 0; i < vs.size(); ++i) {
        if (vs[i] <= 0) continue;
        double a2 = angle + 2 * 3.14159265 *
                    static_cast<double>(vs[i]) / total;
        const int N = 24;
        ImU32 col = IM_COL32(50 + (static_cast<int>(i) * 73) % 200,
                             100 + (static_cast<int>(i) * 111) % 150,
                             180 + (static_cast<int>(i) * 89) % 70, 255);
        for (int k = 0; k < N; ++k) {
          double t1 = angle + (a2 - angle) * k / N;
          double t2 = angle + (a2 - angle) * (k + 1) / N;
          dl->AddTriangleFilled(
              c,
              {c.x + r * static_cast<float>(std::cos(t1)),
               c.y + r * static_cast<float>(std::sin(t1))},
              {c.x + r * static_cast<float>(std::cos(t2)),
               c.y + r * static_cast<float>(std::sin(t2))},
              col);
        }
        angle = a2;
      }
      break;
    }
    case 3: {
      const float denom = static_cast<float>(std::max<size_t>(1, vs.size() - 1));
      for (size_t i = 0; i < vs.size(); ++i) {
        float x = inner_pos.x +
                  inner_size.x * static_cast<float>(i) / denom;
        float y = inner_pos.y +
                  inner_size.y * (1.0f - (vs[i] - lo) / range);
        dl->AddCircleFilled({x, y}, 3.0f,
                            IM_COL32(220, 180, 60, 255));
      }
      break;
    }
    default:
      break;
  }

  if (!title.empty())
    dl->AddText({pos.x + 6, pos.y + 2},
                IM_COL32(220, 220, 220, 255), title.c_str());
  ImGui::Dummy(size);
}

}  // namespace chart_helpers
