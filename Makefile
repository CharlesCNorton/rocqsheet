# Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
#
# Top-level orchestrator.
#
#   make extract  -- build the Rocq theory and copy the extracted
#                    rocqsheet.{h,cpp} into src/generated/.
#   make          -- extract, configure cmake, and build the binary.
#   make run      -- build and launch.
#   make test     -- build, then run the parser and kernel tests.
#   make clean    -- nuke generated files and the cmake build dir.
#
# All steps are file-dependency-driven: re-running the same target
# without changes is a no-op.

CRANE_DIR  := crane
GEN_DIR    := src/generated
CMAKE_DIR  := _build/cmake
THEORY_DIR := _build/Rocqsheet

THEORY_VO  := _build/default/theories/Rocqsheet.vo
GEN_FILES  := $(GEN_DIR)/rocqsheet.h $(GEN_DIR)/rocqsheet.cpp
CMAKE_TAG  := $(CMAKE_DIR)/CMakeCache.txt

CXX_SOURCES := $(wildcard src/*.cpp src/*.h tests/*.cpp) src/CMakeLists.txt

.PHONY: all extract check-crane configure build run test clean update-crane install-deps

all: build

check-crane:
	@test -d $(CRANE_DIR)/theories/cpp || \
	  (echo "error: Crane not found at ./$(CRANE_DIR)"; \
	   echo "Run: git submodule update --init"; \
	   exit 1)

# Theory rebuild only when .v or dune metadata changes.
$(THEORY_VO): theories/Rocqsheet.v theories/dune dune-project | check-crane
	dune build theories/Rocqsheet.vo

# Generated header/source regen when the theory rebuilds.
$(GEN_FILES): $(THEORY_VO)
	@mkdir -p $(GEN_DIR)
	cp $(THEORY_DIR)/rocqsheet.h $(THEORY_DIR)/rocqsheet.cpp $(GEN_DIR)/

extract: $(GEN_FILES)

# Reconfigure cmake when CMakeLists or generated files change.
$(CMAKE_TAG): src/CMakeLists.txt $(GEN_FILES)
	cmake -S src -B $(CMAKE_DIR) -G "Unix Makefiles"

configure: $(CMAKE_TAG)

# cmake --build is itself incremental.
build: $(CMAKE_TAG) $(CXX_SOURCES)
	cmake --build $(CMAKE_DIR) -j

run: build
	./$(CMAKE_DIR)/rocqsheet

test: build
	./$(CMAKE_DIR)/formula_test
	./$(CMAKE_DIR)/kernel_test

clean:
	dune clean
	rm -rf $(GEN_DIR) $(CMAKE_DIR)

# One-shot dependency setup.  Pins Crane via opam and installs the
# system packages (apt on Linux, brew on macOS).  Re-runnable; opam pin
# is idempotent.
install-deps: check-crane
	@uname_s=$$(uname -s); \
	if [ "$$uname_s" = "Linux" ]; then \
	  echo "==> apt-get install"; \
	  sudo apt-get update -y && \
	  sudo apt-get install -y clang pkg-config cmake libglfw3-dev libgl-dev; \
	elif [ "$$uname_s" = "Darwin" ]; then \
	  echo "==> brew install"; \
	  brew install glfw cmake pkg-config; \
	else \
	  echo "Unsupported platform: $$uname_s"; \
	  exit 1; \
	fi
	opam pin add -y rocq-crane ./crane

# Pull the latest Crane HEAD on the tracked branch into the submodule.
# After this you typically need to re-pin opam: `opam pin add rocq-crane ./crane`.
update-crane:
	git submodule update --remote crane
	@echo
	@echo "Submodule moved to: $$(cd crane && git rev-parse HEAD)"
	@echo "Re-pin opam if the Crane API moved:"
	@echo "  opam pin add -y rocq-crane ./crane"
