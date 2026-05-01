# Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
#
# C++ build for Rocqsheet.  Expects `make extract` (or equivalent) to
# have produced src/generated/rocqsheet.{h,cpp}.

cmake_minimum_required(VERSION 3.20)
project(rocqsheet CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

get_filename_component(REPO_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/.." ABSOLUTE)
set(CRANE_THEORIES_CPP "${REPO_ROOT}/crane/theories/cpp")
set(GEN_DIR "${CMAKE_CURRENT_SOURCE_DIR}/generated")

if(NOT EXISTS "${GEN_DIR}/rocqsheet.cpp")
  message(FATAL_ERROR
    "rocqsheet.cpp not found in ${GEN_DIR}.\n"
    "Run `make extract` from the repo root first.")
endif()

# --- Dependencies -----------------------------------------------------------

find_package(OpenGL REQUIRED)
find_package(PkgConfig REQUIRED)
pkg_check_modules(GLFW REQUIRED IMPORTED_TARGET glfw3)

include(FetchContent)
FetchContent_Declare(
  imgui
  GIT_REPOSITORY https://github.com/ocornut/imgui.git
  GIT_TAG        v1.91.5
  GIT_SHALLOW    TRUE)
FetchContent_MakeAvailable(imgui)

add_library(imgui STATIC
  ${imgui_SOURCE_DIR}/imgui.cpp
  ${imgui_SOURCE_DIR}/imgui_demo.cpp
  ${imgui_SOURCE_DIR}/imgui_draw.cpp
  ${imgui_SOURCE_DIR}/imgui_tables.cpp
  ${imgui_SOURCE_DIR}/imgui_widgets.cpp
  ${imgui_SOURCE_DIR}/backends/imgui_impl_glfw.cpp
  ${imgui_SOURCE_DIR}/backends/imgui_impl_opengl3.cpp)
target_include_directories(imgui PUBLIC
  ${imgui_SOURCE_DIR}
  ${imgui_SOURCE_DIR}/backends)
target_link_libraries(imgui PUBLIC PkgConfig::GLFW OpenGL::GL)

# --- Rocqsheet binary --------------------------------------------------------

add_executable(rocqsheet
  main.cpp
  formula.cpp
  ${GEN_DIR}/rocqsheet.cpp)
target_include_directories(rocqsheet PRIVATE
  ${GEN_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CRANE_THEORIES_CPP})
target_link_libraries(rocqsheet PRIVATE imgui)
target_compile_options(rocqsheet PRIVATE
  -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable)

# --- Tests ------------------------------------------------------------------

enable_testing()

add_executable(formula_test
  formula_test.cpp
  formula.cpp
  ${GEN_DIR}/rocqsheet.cpp)
target_include_directories(formula_test PRIVATE
  ${GEN_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}
  ${CRANE_THEORIES_CPP})
target_compile_options(formula_test PRIVATE
  -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable)
add_test(NAME formula_test COMMAND formula_test)

add_executable(kernel_test
  ${REPO_ROOT}/tests/kernel_test.cpp
  ${GEN_DIR}/rocqsheet.cpp)
target_include_directories(kernel_test PRIVATE
  ${GEN_DIR}
  ${CRANE_THEORIES_CPP})
target_compile_options(kernel_test PRIVATE
  -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable)
add_test(NAME kernel_test COMMAND kernel_test)
