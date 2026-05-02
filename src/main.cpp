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

namespace {

void glfw_error(int err, const char* desc) {
  std::fprintf(stderr, "GLFW %d: %s\n", err, desc);
}

}  // namespace

int main(int /*argc*/, char** /*argv*/) {
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

  int exit_code = rocqsheet_run();

  imgui_helpers::g_clipper.reset();
  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImGui::DestroyContext();
  glfwDestroyWindow(win);
  glfwTerminate();
  return exit_code;
}
