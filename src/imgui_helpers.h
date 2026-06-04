// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// C++ binding for the imguiE effect interface declared in
// theories/ImGuiE.v.

#ifndef INCLUDED_IMGUI_HELPERS
#define INCLUDED_IMGUI_HELPERS

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <memory>
#include <unordered_map>
#include <utility>

#include <fcntl.h>
#include <unistd.h>

#include <imgui.h>
#include <imgui_impl_glfw.h>
#include <imgui_impl_opengl3.h>
#include <GLFW/glfw3.h>

// Forward declarations of out-of-line helpers.  Bodies live in
// src/chart_helpers.cpp / src/pdf_helpers.cpp where the full
// [List<...>] body is visible.  These declarations only mention
// primitive types or [List<int64_t>] / [List<pair<...>>] so they
// avoid touching the [Rocqsheet::Cell] forward-declaration tangle.
template <typename T> struct List;
namespace chart_helpers {
void chart_render(int64_t kind, const List<int64_t>& values,
                  const std::string& title);
}  // namespace chart_helpers
namespace pdf_helpers {
using PdfTextEntry = std::pair<std::pair<int64_t, int64_t>, std::string>;
using PdfPageEntries = List<PdfTextEntry>;
bool emit_pdf(const List<PdfPageEntries>& pages,
              const std::string& path);
}  // namespace pdf_helpers

namespace imgui_helpers {

// Process-global handles set by src/main.cpp at startup.
inline GLFWwindow* g_window = nullptr;
inline std::unique_ptr<ImGuiListClipper> g_clipper;
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

// next_window_menu_bar() sets a flag observed by the next
// begin_window().  Persists across the call boundary.
inline bool g_next_window_menu_bar = false;

inline void next_window_menu_bar() { g_next_window_menu_bar = true; }

// Pins the next [begin_window] to a bottom strip on the first launch
// so the floating "Charts" panel doesn't cover the upper rows of the
// grid.  Subsequent frames respect any user drag/resize because of
// [ImGuiCond_FirstUseEver].
inline void next_window_initial_pos_size(int64_t x, int64_t y,
                                         int64_t w, int64_t h) {
  ImGui::SetNextWindowPos(
      ImVec2(static_cast<float>(x), static_cast<float>(y)),
      ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(
      ImVec2(static_cast<float>(w), static_cast<float>(h)),
      ImGuiCond_FirstUseEver);
}

inline void begin_window(const std::string& name) {
  ImGuiWindowFlags flags = ImGuiWindowFlags_NoCollapse;
  if (g_next_window_menu_bar) {
    flags |= ImGuiWindowFlags_MenuBar;
    g_next_window_menu_bar = false;
  }
  ImGui::Begin(name.c_str(), nullptr, flags);
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
  g_clipper = std::make_unique<ImGuiListClipper>();
  g_clipper->Begin(static_cast<int>(total_rows));
  g_clipper_active = true;
}
inline bool clipper_step() {
  if (!g_clipper_active) return false;
  bool more = g_clipper->Step();
  if (!more) g_clipper_active = false;
  return more;
}
inline int64_t clipper_get_start() {
  return static_cast<int64_t>(g_clipper->DisplayStart);
}
inline int64_t clipper_get_end() {
  return static_cast<int64_t>(g_clipper->DisplayEnd);
}
inline void clipper_end() {
  if (g_clipper_active) {
    g_clipper->End(); g_clipper.reset();
    g_clipper_active = false;
  }
}

// ----- Cell selectables and inline edit ---------------------------------

// One per-cell widget call: hidden Selectable for hit-testing plus
// an overlay text rendering of the cell's display value.  Unique ID
// is established via PushID on the cell coordinates.
inline cell_event selectable_cell(int64_t c, int64_t r, bool selected,
                                  bool is_error, const std::string& display) {
  ImGui::PushID(static_cast<int>(c));
  ImGui::PushID(static_cast<int>(r));
  ImGuiSelectableFlags f = ImGuiSelectableFlags_AllowDoubleClick |
                           ImGuiSelectableFlags_AllowOverlap;
  ImVec2 size = {ImGui::GetContentRegionAvail().x,
                 ImGui::GetTextLineHeightWithSpacing()};
  ImVec2 start = ImGui::GetCursorScreenPos();
  bool clicked = ImGui::Selectable("##cell", selected, f, size);
  bool dbl =
      clicked && ImGui::IsMouseDoubleClicked(ImGuiMouseButton_Left);
  if (!display.empty()) {
    ImGui::SetCursorScreenPos(start);
    if (is_error)
      ImGui::PushStyleColor(ImGuiCol_Text, IM_COL32(220, 80, 80, 255));
    ImGui::TextUnformatted(display.c_str());
    if (is_error) ImGui::PopStyleColor();
  }
  ImGui::PopID();
  ImGui::PopID();
  if (dbl) return cell_event::DoubleClicked;
  if (clicked) return cell_event::Selected;
  return cell_event::None;
}

// Same as [selectable_cell] but applies the per-cell formatting:
// bold (FontStyle is approximated by colour boost since ImGui needs a
// preloaded bold font asset), packed RGB foreground colour
// (0xRRGGBB), border, and horizontal alignment (0=left, 1=center,
// 2=right).  When all attributes are at the defaults the rendering
// is byte-identical to [selectable_cell].
inline cell_event selectable_cell_formatted(
    int64_t c, int64_t r, bool selected, bool is_error,
    const std::string& display,
    bool bold, int64_t color_rgb, bool border, int64_t align) {
  ImGui::PushID(static_cast<int>(c));
  ImGui::PushID(static_cast<int>(r));
  ImGuiSelectableFlags f = ImGuiSelectableFlags_AllowDoubleClick |
                           ImGuiSelectableFlags_AllowOverlap;
  ImVec2 size = {ImGui::GetContentRegionAvail().x,
                 ImGui::GetTextLineHeightWithSpacing()};
  ImVec2 start = ImGui::GetCursorScreenPos();
  bool clicked = ImGui::Selectable("##cell_fmt", selected, f, size);
  bool dbl =
      clicked && ImGui::IsMouseDoubleClicked(ImGuiMouseButton_Left);
  if (border) {
    ImVec2 a = start;
    ImVec2 b{start.x + size.x, start.y + size.y};
    ImGui::GetWindowDrawList()->AddRect(
        a, b, IM_COL32(180, 180, 180, 220), 0.0f, 0, 1.0f);
  }
  if (!display.empty()) {
    float text_w = ImGui::CalcTextSize(display.c_str()).x;
    float dx = 0.0f;
    if (align == 1) dx = (size.x - text_w) * 0.5f;
    else if (align == 2) dx = size.x - text_w - 2.0f;
    if (dx < 0.0f) dx = 0.0f;
    ImGui::SetCursorScreenPos({start.x + dx, start.y});
    ImU32 col;
    if (is_error) {
      col = IM_COL32(220, 80, 80, 255);
    } else if (color_rgb == 0) {
      col = ImGui::GetColorU32(ImGuiCol_Text);
    } else {
      uint32_t v = static_cast<uint32_t>(color_rgb);
      col = IM_COL32((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF, 255);
    }
    ImGui::PushStyleColor(ImGuiCol_Text, col);
    if (bold) {
      ImVec2 p = ImGui::GetCursorScreenPos();
      ImGui::GetWindowDrawList()->AddText({p.x + 1.0f, p.y},
                                          col, display.c_str());
    }
    ImGui::TextUnformatted(display.c_str());
    ImGui::PopStyleColor();
  }
  ImGui::PopID();
  ImGui::PopID();
  if (dbl) return cell_event::DoubleClicked;
  if (clicked) return cell_event::Selected;
  return cell_event::None;
}

// Returns (current buffer contents after this frame, true iff Enter
// was pressed this frame).  When Enter is pressed the kernel-side
// driver should commit; otherwise it just stores the current buffer.
inline std::pair<std::string, bool> input_text(const std::string& id,
                                               const std::string& cur) {
  static thread_local std::string buf;
  buf = cur;
  buf.resize(buf.size() + 256);  // headroom for typing
  bool enter = ImGui::InputText(id.c_str(), buf.data(),
                                buf.size() + 1,
                                ImGuiInputTextFlags_EnterReturnsTrue);
  std::string out(buf.c_str());  // strip trailing zeros
  return {std::move(out), enter};
}

// ----- Tab bar ----------------------------------------------------------
// Forward declared here; the body lives in src/tab_bar_helpers.cpp
// where the full [List<std::string>] template body is visible.
int64_t tab_bar_select(const std::string& id,
                       const List<std::string>& names,
                       int64_t current);

// ----- Menu bar ---------------------------------------------------------

inline bool begin_menu_bar() { return ImGui::BeginMenuBar(); }
inline void end_menu_bar() { ImGui::EndMenuBar(); }
inline bool begin_menu(const std::string& label) {
  return ImGui::BeginMenu(label.c_str());
}
inline void end_menu() { ImGui::EndMenu(); }
inline bool menu_item(const std::string& label, bool enabled) {
  return ImGui::MenuItem(label.c_str(), nullptr, false, enabled);
}

// ----- Layout -----------------------------------------------------------

inline void same_line() { ImGui::SameLine(); }

// ----- File I/O ---------------------------------------------------------

inline std::pair<std::string, bool> file_read(const std::string& path) {
  std::ifstream f(path);
  if (!f) return {std::string{}, false};
  std::ostringstream ss;
  ss << f.rdbuf();
  return {ss.str(), true};
}

inline bool file_write(const std::string& path, const std::string& content) {
  std::ofstream f(path);
  if (!f) return false;
  f << content;
  return f.good();
}

// Rotate up to three numbered backups before writing a new save:
// <path>.bak.3 is deleted, <path>.bak.2 -> .bak.3, .bak.1 -> .bak.2,
// then <path> -> <path>.bak.1.  Missing files are silently skipped.
inline void rotate_bak(const std::string& path) {
  std::string b3 = path + ".bak.3";
  std::string b2 = path + ".bak.2";
  std::string b1 = path + ".bak.1";
  std::remove(b3.c_str());
  std::rename(b2.c_str(), b3.c_str());
  std::rename(b1.c_str(), b2.c_str());
  std::rename(path.c_str(), b1.c_str());
}

// Atomic save: write to <path>.tmp, fsync, rotate .bak.{1,2,3},
// rename <path>.tmp to <path>.  A crash between the open and the
// rename leaves the previous save intact.
inline bool file_save_atomic(const std::string& path,
                             const std::string& content) {
  std::string tmp_path = path + ".tmp";
  {
    std::ofstream f(tmp_path);
    if (!f) return false;
    f << content;
    if (!f.good()) return false;
  }
  // Best-effort fsync so the bytes are durable before we rename.
  int fd = ::open(tmp_path.c_str(), O_RDONLY);
  if (fd >= 0) {
    ::fsync(fd);
    ::close(fd);
  }
  rotate_bak(path);
  if (std::rename(tmp_path.c_str(), path.c_str()) != 0) {
    std::remove(tmp_path.c_str());
    return false;
  }
  return true;
}

// Acquire an advisory write lock on [path].  Closing the descriptor
// (process exit) releases it.  Subsequent calls for the same path
// return true without re-locking.  Returns false when another process
// holds the lock.
inline bool file_lock(const std::string& path) {
  static std::unordered_map<std::string, int> g_locks;
  auto it = g_locks.find(path);
  if (it != g_locks.end()) return true;
  int fd = ::open(path.c_str(), O_RDWR | O_CREAT, 0644);
  if (fd < 0) return false;
  struct flock fl{};
  fl.l_type   = F_WRLCK;
  fl.l_whence = SEEK_SET;
  fl.l_start  = 0;
  fl.l_len    = 0;
  if (::fcntl(fd, F_SETLK, &fl) != 0) {
    ::close(fd);
    return false;
  }
  g_locks.emplace(path, fd);
  return true;
}

// ----- Clipboard --------------------------------------------------------
//
// Item 102 (OS clipboard interop) — the GLFW ImGui backend's default
// clipboard handlers are `glfwGetClipboardString` / `glfwSetClipboardString`
// which sit directly on top of the OS clipboard (X11 selection / Wayland
// data device / macOS pasteboard / Win32 OpenClipboard).  So
// `do_copy` and `do_paste` already cross process boundaries — pasting
// into another application picks the cell text up, and pasting from
// another application drops its text into the formula bar.
//
// What's NOT yet done is the TSV-format part of item 102: when the
// selection is a multi-cell range, `do_copy` should emit tab-separated
// values so a paste into Excel / Numbers / LibreOffice unpacks into a
// matching range.  That work depends on item 59 (replace `ls_selected`
// with a (TL, BR) range) and is deferred here.

inline std::string clipboard_get() {
  const char* s = ImGui::GetClipboardText();
  return s ? std::string(s) : std::string{};
}
inline void clipboard_set(const std::string& s) {
  ImGui::SetClipboardText(s.c_str());
}

// ----- Keyboard shortcuts -----------------------------------------------
//
// Reports whether Ctrl+<key> was pressed this frame.  [k] must be a
// single-character string; a few well-known multi-char names map to
// special keys.

inline bool ctrl_key_pressed(const std::string& k) {
  if (!ImGui::GetIO().KeyCtrl) return false;
  if (ImGui::GetIO().KeyShift) return false;
  if (k == "`") return ImGui::IsKeyPressed(ImGuiKey_GraveAccent);
  if (k.size() == 1) {
    char c = k[0];
    if (c >= 'a' && c <= 'z') c -= 32;
    if (c >= 'A' && c <= 'Z') {
      ImGuiKey key = static_cast<ImGuiKey>(ImGuiKey_A + (c - 'A'));
      return ImGui::IsKeyPressed(key);
    }
  }
  return false;
}

inline bool ctrl_shift_key_pressed(const std::string& k) {
  if (!ImGui::GetIO().KeyCtrl)  return false;
  if (!ImGui::GetIO().KeyShift) return false;
  if (k.size() == 1) {
    char c = k[0];
    if (c >= 'a' && c <= 'z') c -= 32;
    if (c >= 'A' && c <= 'Z') {
      ImGuiKey key = static_cast<ImGuiKey>(ImGuiKey_A + (c - 'A'));
      return ImGui::IsKeyPressed(key);
    }
  }
  return false;
}

inline bool key_pressed(const std::string& k) {
  if (k == "Up")        return ImGui::IsKeyPressed(ImGuiKey_UpArrow);
  if (k == "Down")      return ImGui::IsKeyPressed(ImGuiKey_DownArrow);
  if (k == "Left")      return ImGui::IsKeyPressed(ImGuiKey_LeftArrow);
  if (k == "Right")     return ImGui::IsKeyPressed(ImGuiKey_RightArrow);
  if (k == "Tab")       return ImGui::IsKeyPressed(ImGuiKey_Tab);
  if (k == "Home")      return ImGui::IsKeyPressed(ImGuiKey_Home);
  if (k == "End")       return ImGui::IsKeyPressed(ImGuiKey_End);
  if (k == "PageUp")    return ImGui::IsKeyPressed(ImGuiKey_PageUp);
  if (k == "PageDown")  return ImGui::IsKeyPressed(ImGuiKey_PageDown);
  if (k == "Delete")    return ImGui::IsKeyPressed(ImGuiKey_Delete);
  if (k == "Enter")     return ImGui::IsKeyPressed(ImGuiKey_Enter);
  return false;
}

// Like [key_pressed] but checks that Ctrl is also held (and Shift is
// not).  Returns true only when the named arrow key was just pressed
// with Ctrl held.  Allows the navigation handler to bind Ctrl+arrow
// to a separate jump-to-edge action.
inline bool ctrl_arrow_pressed(const std::string& k) {
  if (!ImGui::GetIO().KeyCtrl) return false;
  if (ImGui::GetIO().KeyShift) return false;
  return key_pressed(k);
}

// ----- Formula bar reference label -------------------------------------
// Displays a small read-only label widget for the current selected
// cell ref (e.g. "A1") in the formula bar.

inline void fbar_ref_label(const std::string& s) {
  ImGui::SetNextItemWidth(80.0f);
  std::string buf = s;
  buf.resize(buf.size() + 16);
  ImGui::InputText("##ref", buf.data(), buf.size() + 1,
                   ImGuiInputTextFlags_ReadOnly);
}

}  // namespace imgui_helpers

#endif  // INCLUDED_IMGUI_HELPERS
