// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Binary entry point: GLFW + ImGui setup and teardown around a
// single call into the Rocq-extracted runtime.  Also exposes a
// [--headless] mode with [--eval], [--print-csv], and [--exec]
// query paths that bypass GLFW entirely so CI and integration tests
// can run without a display server.

#include "rocqsheet.h"
#include "imgui_helpers.h"
#include "eval_iter.h"
#include "do_op_helpers.h"

#include <imgui.h>
#include <imgui_impl_glfw.h>
#include <imgui_impl_opengl3.h>
#include <GLFW/glfw3.h>

#include <cctype>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <sys/stat.h>
#include <variant>

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
  return State::initial_loop_state;
}

// Apply a previously-saved file's contents on top of [ls] using the
// extracted [apply_load_lines] parser.  Returns the rehydrated state.
loop_state apply_save_blob(loop_state ls, const std::string& content) {
  int64_t len = static_cast<int64_t>(content.size());
  unsigned int fuel = static_cast<unsigned int>(len + 4);
  return SaveLoad::apply_load_lines(std::move(ls), content, len, 0, fuel);
}

// Parse a spreadsheet-style cell reference like "A1", "B5", "AA10"
// into a Rocqsheet::CellRef.  Returns false on syntactically invalid
// input or on out-of-bounds row/col.
bool parse_cell_ref(const std::string& s, Rocqsheet::CellRef& out) {
  size_t i = 0;
  int64_t col = 0;
  int letters = 0;
  while (i < s.size() && std::isalpha(static_cast<unsigned char>(s[i]))) {
    char c = static_cast<char>(std::toupper(static_cast<unsigned char>(s[i])));
    col = col * 26 + (c - 'A' + 1);
    ++i;
    ++letters;
  }
  if (letters == 0) return false;
  col -= 1;  // shift from 1-based letter encoding to 0-based index
  int64_t row = 0;
  int digits = 0;
  while (i < s.size() && std::isdigit(static_cast<unsigned char>(s[i]))) {
    row = row * 10 + (s[i] - '0');
    ++i;
    ++digits;
  }
  if (digits == 0 || i != s.size()) return false;
  if (row < 1) return false;
  row -= 1;  // shift from 1-based row to 0-based index
  if (col < 0 || col >= Rocqsheet::NUM_COLS) return false;
  if (row < 0 || row >= Rocqsheet::NUM_ROWS) return false;
  out = Rocqsheet::CellRef{col, row};
  return true;
}

// Produce a CSV-quoted version of [s] per RFC 4180: wrap in double
// quotes if the value contains a comma, double quote, or newline;
// double up any embedded double quotes.
std::string csv_quote(const std::string& s) {
  bool needs_quote = false;
  for (char c : s) {
    if (c == ',' || c == '"' || c == '\n' || c == '\r') {
      needs_quote = true;
      break;
    }
  }
  if (!needs_quote) return s;
  std::string out;
  out.reserve(s.size() + 4);
  out.push_back('"');
  for (char c : s) {
    if (c == '"') out.push_back('"');
    out.push_back(c);
  }
  out.push_back('"');
  return out;
}

// Produce the CSV cell text for the cell at [r] on [sheet]: literals
// stringify directly; formulas evaluate via formula::eval_iter and
// fall back to a parser-style "ERR" marker on failure; non-int cells
// (floats, strings, booleans) stringify by their static representation
// since eval_iter only carries integer results.
std::string csv_cell(const Rocqsheet::Sheet& sheet,
                     const Rocqsheet::CellRef& r) {
  Rocqsheet::Cell c = Rocqsheet::get_cell(sheet, r);
  if (std::holds_alternative<Rocqsheet::Cell::CEmpty>(c.v())) return "";
  if (std::holds_alternative<Rocqsheet::Cell::CLit>(c.v())) {
    return std::to_string(std::get<Rocqsheet::Cell::CLit>(c.v()).d_a0);
  }
  if (std::holds_alternative<Rocqsheet::Cell::CFloat>(c.v())) {
    return std::to_string(std::get<Rocqsheet::Cell::CFloat>(c.v()).d_a0);
  }
  if (std::holds_alternative<Rocqsheet::Cell::CStr>(c.v())) {
    return csv_quote(std::get<Rocqsheet::Cell::CStr>(c.v()).d_a0);
  }
  if (std::holds_alternative<Rocqsheet::Cell::CBool>(c.v())) {
    return std::get<Rocqsheet::Cell::CBool>(c.v()).d_a0 ? "TRUE" : "FALSE";
  }
  // CForm: evaluate via the iterative evaluator.
  auto v = formula::eval_iter(sheet, r);
  if (v.has_value()) return std::to_string(*v);
  return "#ERR";
}

// Headless --print-csv: walk the active sheet up to the last row that
// contains any data and emit RFC 4180 rows on stdout.
void print_csv(const loop_state& ls) {
  // Find the last non-empty row so we don't emit 200 trailing blank
  // rows on a sparsely-populated sheet.
  int64_t last_row = -1;
  for (int64_t r = 0; r < Rocqsheet::NUM_ROWS; ++r) {
    for (int64_t c = 0; c < Rocqsheet::NUM_COLS; ++c) {
      Rocqsheet::Cell cell =
          Rocqsheet::get_cell(ls.ls_sheet, Rocqsheet::CellRef{c, r});
      if (!std::holds_alternative<Rocqsheet::Cell::CEmpty>(cell.v())) {
        last_row = r;
        break;
      }
    }
  }
  // Find the last non-empty column similarly.
  int64_t last_col = -1;
  for (int64_t c = 0; c < Rocqsheet::NUM_COLS; ++c) {
    for (int64_t r = 0; r <= last_row; ++r) {
      Rocqsheet::Cell cell =
          Rocqsheet::get_cell(ls.ls_sheet, Rocqsheet::CellRef{c, r});
      if (!std::holds_alternative<Rocqsheet::Cell::CEmpty>(cell.v())) {
        if (c > last_col) last_col = c;
        break;
      }
    }
  }
  for (int64_t r = 0; r <= last_row; ++r) {
    std::string line;
    for (int64_t c = 0; c <= last_col; ++c) {
      if (c > 0) line.push_back(',');
      line += csv_cell(ls.ls_sheet, Rocqsheet::CellRef{c, r});
    }
    std::cout << line << '\n';
  }
}

int run_headless(const std::string& load_path,
                 const std::string& eval_ref,
                 bool print_csv_flag,
                 const std::string& exec_macro) {
  // Start from a fully clean active sheet so headless query results
  // are not contaminated by the GUI's demo content.  do_clear wipes
  // ls_sheet, the formula bar, and the parse-error / edit-buf state
  // but preserves ls_formats / ls_other_sheets / ls_charts (which
  // headless --eval and --print-csv don't read from anyway).
  loop_state ls = ::do_op_helpers::do_clear<
      loop_state, Rocqsheet::Sheet,
      List<std::pair<Rocqsheet::Sheet, std::string>>,
      List<std::pair<Rocqsheet::CellRef, std::string>>,
      List<Rocqsheet::CellRef>>(
        make_starting_loop_state(), Rocqsheet::new_sheet);
  if (!load_path.empty()) {
    std::string content;
    if (!slurp_file(load_path, content)) {
      std::fprintf(stderr, "headless: could not read %s\n",
                   load_path.c_str());
      return 1;
    }
    ls = apply_save_blob(std::move(ls), content);
  }
  if (!eval_ref.empty()) {
    Rocqsheet::CellRef r;
    if (!parse_cell_ref(eval_ref, r)) {
      std::fprintf(stderr, "headless: invalid cell ref %s\n",
                   eval_ref.c_str());
      return 2;
    }
    auto v = formula::eval_iter(ls.ls_sheet, r);
    if (v.has_value()) {
      std::cout << *v << '\n';
    } else {
      std::cout << "#ERR\n";
    }
    return 0;
  }
  if (print_csv_flag) {
    print_csv(ls);
    return 0;
  }
  if (!exec_macro.empty()) {
    std::fprintf(stderr,
                 "headless: --exec requires the macro engine "
                 "(see TODO item 96)\n");
    return 3;
  }
  // Plain --headless --load <path>: just verify the load round-trips.
  std::cout << "loaded ok\n";
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  // --- CLI flags ------------------------------------------------------
  // --headless         : skip GLFW/OpenGL bring-up and run a query path
  //                      instead of the GUI loop.
  // --load <path>      : pre-load the named save file before the GUI
  //                      starts (or, in --headless mode, before the
  //                      query runs).
  // --eval <CellRef>   : (headless) evaluate the named cell and print
  //                      its integer result, "#ERR" on failure.
  // --print-csv        : (headless) emit the active sheet as RFC 4180
  //                      CSV on stdout.
  // --exec <macro>     : (headless) execute a workbook macro by name;
  //                      requires the macro engine (TODO #96).
  std::string load_path;
  std::string eval_ref;
  std::string exec_macro;
  bool load_explicit = false;
  bool headless = false;
  bool print_csv_flag = false;
  for (int i = 1; i < argc; ++i) {
    if (std::strcmp(argv[i], "--headless") == 0) {
      headless = true;
    } else if (std::strcmp(argv[i], "--load") == 0 && i + 1 < argc) {
      load_path = argv[++i];
      load_explicit = true;
    } else if (std::strcmp(argv[i], "--eval") == 0 && i + 1 < argc) {
      eval_ref = argv[++i];
      headless = true;  // --eval implies headless
    } else if (std::strcmp(argv[i], "--print-csv") == 0) {
      print_csv_flag = true;
      headless = true;  // --print-csv implies headless
    } else if (std::strcmp(argv[i], "--exec") == 0 && i + 1 < argc) {
      exec_macro = argv[++i];
      headless = true;  // --exec implies headless
    }
  }
  // Auto-load: if --load was not given but a [rocqsheet.txt] file
  // sits in the cwd, slurp it so saved sessions survive a restart
  // without needing Ctrl+O.
  if (!load_explicit && file_exists("rocqsheet.txt")) {
    load_path = "rocqsheet.txt";
  }

  if (headless) {
    return run_headless(load_path, eval_ref, print_csv_flag, exec_macro);
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
