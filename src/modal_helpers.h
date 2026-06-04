// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// reusable ImGui modal-popup framework.  Popup visibility is
// owned by ImGui (OpenPopup / BeginPopupModal); per-modal text buffers
// are C++ statics here, mirroring the g_window / g_clipper pattern in
// imgui_helpers.  The Coq tree drives a modal as an effect that
// reports the user's committed answer on the frame it happens:
//   modal_helpers::open(id)        -- arm the popup named id
//   modal_helpers::confirm(id, m)  -- 0 pending/closed, 1 OK, 2 Cancel
//   modal_helpers::find_replace()  -- (done, (find_text, replace_text))
//
// Each render function must be called every frame from the same ImGui
// ID scope that called open() (the main window body), or the popup
// will never appear.

#ifndef ROCQSHEET_MODAL_HELPERS_H
#define ROCQSHEET_MODAL_HELPERS_H

#include <imgui.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <utility>

namespace modal_helpers {

// Deferred-open latch: open() may be called from any ImGui ID scope
// (the menu runs inside the main window, shortcuts run outside), but
// OpenPopup must execute in the same scope as BeginPopupModal.  The
// renderers below consume the latch at their fixed call site.
inline std::string g_pending_open;

inline void open(const std::string& id) {
  g_pending_open = id;
}

inline void consume_pending(const char* id) {
  if (g_pending_open == id) {
    ImGui::OpenPopup(id);
    g_pending_open.clear();
  }
}

// Generic confirm prompt.  Returns 1 on the OK frame, 2 on the
// Cancel frame, 0 otherwise.
inline int64_t confirm(const std::string& id, const std::string& msg) {
  int64_t result = 0;
  consume_pending(id.c_str());
  if (ImGui::BeginPopupModal(id.c_str(), nullptr,
                             ImGuiWindowFlags_AlwaysAutoResize)) {
    ImGui::TextUnformatted(msg.c_str());
    ImGui::Separator();
    if (ImGui::Button("OK", ImVec2(120, 0))) {
      result = 1;
      ImGui::CloseCurrentPopup();
    }
    ImGui::SetItemDefaultFocus();
    ImGui::SameLine();
    if (ImGui::Button("Cancel", ImVec2(120, 0))) {
      result = 2;
      ImGui::CloseCurrentPopup();
    }
    ImGui::EndPopup();
  }
  return result;
}

// three-button confirm.  Returns 1 / 2 / 3 on the frame the
// corresponding button is clicked, 0 otherwise.
inline int64_t confirm3(const std::string& id, const std::string& msg,
                        const std::string& b1, const std::string& b2,
                        const std::string& b3) {
  int64_t result = 0;
  consume_pending(id.c_str());
  if (ImGui::BeginPopupModal(id.c_str(), nullptr,
                             ImGuiWindowFlags_AlwaysAutoResize)) {
    ImGui::TextUnformatted(msg.c_str());
    ImGui::Separator();
    if (ImGui::Button(b1.c_str())) {
      result = 1;
      ImGui::CloseCurrentPopup();
    }
    ImGui::SetItemDefaultFocus();
    ImGui::SameLine();
    if (ImGui::Button(b2.c_str())) {
      result = 2;
      ImGui::CloseCurrentPopup();
    }
    ImGui::SameLine();
    if (ImGui::Button(b3.c_str())) {
      result = 3;
      ImGui::CloseCurrentPopup();
    }
    ImGui::EndPopup();
  }
  return result;
}

// Single-text-field prompt (sheet rename and future consumers).
// Returns (done, text); done is true exactly on the OK frame.
inline std::pair<bool, std::string> text_prompt(const std::string& id,
                                                const std::string& label) {
  static char buf[256] = "";
  bool done = false;
  std::string out;
  consume_pending(id.c_str());
  if (ImGui::BeginPopupModal(id.c_str(), nullptr,
                             ImGuiWindowFlags_AlwaysAutoResize)) {
    ImGui::InputText(label.c_str(), buf, sizeof buf);
    ImGui::Separator();
    if (ImGui::Button("OK", ImVec2(120, 0))) {
      done = true;
      out = buf;
      buf[0] = '\0';
      ImGui::CloseCurrentPopup();
    }
    ImGui::SameLine();
    if (ImGui::Button("Cancel", ImVec2(120, 0))) {
      buf[0] = '\0';
      ImGui::CloseCurrentPopup();
    }
    ImGui::EndPopup();
  }
  return {done, out};
}

// Find / Replace modal.  Two integer-literal fields; the
// pair is reported once, on the Replace All frame, with the buffers
// left intact for the next invocation.
inline std::pair<bool, std::pair<std::string, std::string>> find_replace() {
  static char find_buf[256] = "";
  static char repl_buf[256] = "";
  bool done = false;
  std::string find_text;
  std::string repl_text;
  consume_pending("Find / Replace");
  if (ImGui::BeginPopupModal("Find / Replace", nullptr,
                             ImGuiWindowFlags_AlwaysAutoResize)) {
    ImGui::InputText("Find (integer)", find_buf, sizeof find_buf);
    ImGui::InputText("Replace with", repl_buf, sizeof repl_buf);
    ImGui::Separator();
    if (ImGui::Button("Replace All", ImVec2(140, 0))) {
      done = true;
      find_text = find_buf;
      repl_text = repl_buf;
      ImGui::CloseCurrentPopup();
    }
    ImGui::SameLine();
    if (ImGui::Button("Cancel", ImVec2(120, 0))) {
      ImGui::CloseCurrentPopup();
    }
    ImGui::EndPopup();
  }
  return {done, {find_text, repl_text}};
}

}  // namespace modal_helpers

#endif  // ROCQSHEET_MODAL_HELPERS_H
