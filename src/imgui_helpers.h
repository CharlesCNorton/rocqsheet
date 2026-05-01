// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// C++ binding for the imguiE effect interface declared in
// theories/ImGuiE.v.

#ifndef INCLUDED_IMGUI_HELPERS
#define INCLUDED_IMGUI_HELPERS

#include <cstdint>
#include <string>

#include <imgui.h>
#include <imgui_impl_glfw.h>
#include <imgui_impl_opengl3.h>
#include <GLFW/glfw3.h>

namespace imgui_helpers {

// Process-global handles set by src/main.cpp at startup.
inline GLFWwindow* g_window = nullptr;
inline ImGuiListClipper g_clipper{};
inline bool g_clipper_active = false;

enum class cell_event { None, Selected, DoubleClicked };

// ----- Frame lifecycle --------------------------------------------------

inline bool should_close() {
  return g_window ? glfwWindowShouldClose(g_window) : true;
}
inline void poll_events() { glfwPollEvents(); }

inline void new_frame() {
  ImGui_ImplOpenGL3_NewFrame();
  ImGui_ImplGlfw_NewFrame();
  ImGui::NewFrame();
}

inline void render_frame() {
  ImGui::Render();
  int w = 0, h = 0;
  if (g_window) glfwGetFramebufferSize(g_window, &w, &h);
  glViewport(0, 0, w, h);
  glClearColor(0.10f, 0.10f, 0.12f, 1.0f);
  glClear(GL_COLOR_BUFFER_BIT);
  ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());
  if (g_window) glfwSwapBuffers(g_window);
}

inline void full_viewport() {
  ImGuiViewport* vp = ImGui::GetMainViewport();
  ImGui::SetNextWindowPos(vp->WorkPos);
  ImGui::SetNextWindowSize(vp->WorkSize);
}

// ----- Window scope -----------------------------------------------------

inline void begin_window(const std::string& name) {
  ImGui::Begin(name.c_str(), nullptr, ImGuiWindowFlags_NoCollapse);
}
inline void end_window() { ImGui::End(); }

// ----- Text -------------------------------------------------------------

inline void text(const std::string& s) {
  ImGui::TextUnformatted(s.c_str());
}
inline void text_err(const std::string& s) {
  ImGui::PushStyleColor(ImGuiCol_Text, IM_COL32(220, 80, 80, 255));
  ImGui::TextUnformatted(s.c_str());
  ImGui::PopStyleColor();
}
inline void separator() { ImGui::Separator(); }

// ----- Tables -----------------------------------------------------------

inline bool begin_table(const std::string& id, int64_t cols) {
  static const ImGuiTableFlags flags =
      ImGuiTableFlags_Resizable | ImGuiTableFlags_Borders |
      ImGuiTableFlags_RowBg | ImGuiTableFlags_ScrollX |
      ImGuiTableFlags_ScrollY | ImGuiTableFlags_SizingFixedFit;
  ImVec2 outer = ImGui::GetContentRegionAvail();
  return ImGui::BeginTable(id.c_str(), static_cast<int>(cols), flags, outer);
}
inline void end_table() { ImGui::EndTable(); }

inline void table_setup_freeze(int64_t cols, int64_t rows) {
  ImGui::TableSetupScrollFreeze(static_cast<int>(cols),
                                static_cast<int>(rows));
}
inline void table_setup_column(const std::string& label, int64_t width) {
  ImGui::TableSetupColumn(
      label.c_str(),
      ImGuiTableColumnFlags_WidthFixed | ImGuiTableColumnFlags_NoHide,
      static_cast<float>(width));
}
inline void table_headers_row() { ImGui::TableHeadersRow(); }
inline void table_next_row() { ImGui::TableNextRow(); }
inline void table_set_column_index(int64_t i) {
  ImGui::TableSetColumnIndex(static_cast<int>(i));
}

// ----- Clipper ----------------------------------------------------------
// One [ImGuiListClipper] reused frame-to-frame.  Caller invokes
// [clipper_begin] once, [clipper_step] in a loop, [clipper_end] once.

inline void clipper_begin(int64_t total_rows) {
  g_clipper = ImGuiListClipper{};
  g_clipper.Begin(static_cast<int>(total_rows));
  g_clipper_active = true;
}
inline bool clipper_step() {
  if (!g_clipper_active) return false;
  bool more = g_clipper.Step();
  if (!more) g_clipper_active = false;
  return more;
}
inline int64_t clipper_get_start() {
  return static_cast<int64_t>(g_clipper.DisplayStart);
}
inline int64_t clipper_get_end() {
  return static_cast<int64_t>(g_clipper.DisplayEnd);
}
inline void clipper_end() {
  if (g_clipper_active) {
    g_clipper.End();
    g_clipper_active = false;
  }
}

}  // namespace imgui_helpers

#endif  // INCLUDED_IMGUI_HELPERS
