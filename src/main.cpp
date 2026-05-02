// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Binary entry point: GLFW + ImGui setup and teardown around a
// single call into the Rocq-extracted runtime.

#include "rocqsheet.h"
#include "imgui_helpers.h"

#include <imgui.h>
#include <imgui_impl_glfw.h>
#include <imgui_impl_opengl3.h>
#include <GLFW/glfw3.h>

#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>
#include <string>
#include <sys/stat.h>

namespace {

void glfw_error(int err, const char* desc) {
  std::fprintf(stderr, "GLFW %d: %s\n", err, desc);
}

bool file_exists(const char* path) {
  struct stat st{};
  return stat(path, &st) == 0;
}

bool slurp_file(const std::string& path, std::string& out) {
  std::ifstream f(path);
  if (!f) return false;
  std::ostringstream ss;
  ss << f.rdbuf();
  out = ss.str();
  return true;
}

// Build the start-of-session loop_state.  Replaces the previous
// `loop_state ls = initial_loop_state;` static-copy pattern so the
// workbook can be re-seeded inside the same process (e.g. once the
// app gains a "reset" command) without requiring a binary restart.
loop_state make_starting_loop_state() {
  return initial_loop_state;
}

// Apply a previously-saved file's contents on top of [ls] using the
// extracted [apply_load_lines] parser.  Returns the rehydrated state.
loop_state apply_save_blob(loop_state ls, const std::string& content) {
  int64_t len = static_cast<int64_t>(content.size());
  unsigned int fuel = static_cast<unsigned int>(len + 4);
  return apply_load_lines(std::move(ls), content, len, 0, fuel);
}

}  // namespace

int main(int argc, char** argv) {
  // --- CLI flags ------------------------------------------------------
  // --load <path> : pre-load the named save file before the GUI starts,
  //                 so headless smoke runs and pre-seeded sessions can
  //                 boot without driving the File > Open menu by hand.
  std::string load_path;
  bool load_explicit = false;
  for (int i = 1; i < argc; ++i) {
    if (std::strcmp(argv[i], "--load") == 0 && i + 1 < argc) {
      load_path = argv[++i];
      load_explicit = true;
    }
  }
  // Auto-load: if --load was not given but a [rocqsheet.txt] file
  // sits in the cwd, slurp it so saved sessions survive a restart
  // without needing Ctrl+O.
  if (!load_explicit && file_exists("rocqsheet.txt")) {
    load_path = "rocqsheet.txt";
  }

  glfwSetErrorCallback(glfw_error);
  if (!glfwInit()) return 1;

  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 3);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);

  GLFWwindow* win = glfwCreateWindow(1280, 800, "Rocqsheet", nullptr, nullptr);
  if (!win) { glfwTerminate(); return 1; }
  glfwMakeContextCurrent(win);
  glfwSwapInterval(1);

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImGui::StyleColorsDark();
  ImGui_ImplGlfw_InitForOpenGL(win, true);
  ImGui_ImplOpenGL3_Init("#version 330 core");

  imgui_helpers::g_window = win;

  // The Coq-side [run_app] is a [cofix] guarded by [Tau]; Crane
  // extracts it as a tail-recursive C++ function but the recursion
  // borrows into [res.second] across the call site, blocking the
  // compiler's TCO and overflowing the stack after a few thousand
  // frames.  Drive [process_frame] directly from a loop here.
  loop_state ls = make_starting_loop_state();
  if (!load_path.empty()) {
    std::string content;
    if (slurp_file(load_path, content)) {
      ls = apply_save_blob(std::move(ls), content);
      std::fprintf(stderr, "Loaded %s (%zu bytes)\n",
                   load_path.c_str(), content.size());
    } else {
      std::fprintf(stderr, "Could not read %s; starting empty\n",
                   load_path.c_str());
    }
  }

  while (true) {
    auto step = process_frame(std::move(ls));
    if (step.first) break;
    ls = std::move(step.second);
  }
  int exit_code = 0;

  imgui_helpers::g_clipper.reset();
  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImGui::DestroyContext();
  glfwDestroyWindow(win);
  glfwTerminate();
  return exit_code;
}
