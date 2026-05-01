# Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
#
# Top-level orchestrator.
#
#   make extract  -- build the Rocq theory and copy the extracted
#                    rocqsheet.{h,cpp} into src/generated/.
#   make          -- extract, configure cmake, and build the binary.
#   make run      -- build and launch.
#   make test     -- build, then run the parser unit tests.
#   make clean    -- nuke generated files and the cmake build dir.

CRANE_DIR  := crane
GEN_DIR    := src/generated
CMAKE_DIR  := _build/cmake
THEORY_DIR := _build/Rocqsheet

.PHONY: all extract check-crane configure build run test clean

all: build

check-crane:
	@test -d $(CRANE_DIR)/theories/cpp || \
	  (echo "error: Crane not found at ./$(CRANE_DIR)"; \
	   echo "Run: git submodule update --init"; \
	   exit 1)

extract: check-crane theories/Rocqsheet.v
	dune build theories/Rocqsheet.vo
	@mkdir -p $(GEN_DIR)
	cp $(THEORY_DIR)/rocqsheet.h $(THEORY_DIR)/rocqsheet.cpp $(GEN_DIR)/

configure: extract
	cmake -S src -B $(CMAKE_DIR) -G "Unix Makefiles"

build: configure
	cmake --build $(CMAKE_DIR) -j

run: build
	./$(CMAKE_DIR)/rocqsheet

test: build
	./$(CMAKE_DIR)/formula_test

clean:
	dune clean
	rm -rf $(GEN_DIR) $(CMAKE_DIR)
