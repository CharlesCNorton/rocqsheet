# rocq-crane-imgui

Reusable Crane Coq bindings for Dear ImGui — the `imguiE` effect
interface (in `theories/ImGuiE.v`) and its hand-written C++ helper
header (in `include/imgui_helpers.h`).  The layout mirrors joom's
`rocq-crane-sdl2`.

## Layout

```
rocq-crane-imgui/
├── dune-project           ; standalone Coq+dune project metadata
├── rocq-crane-imgui.opam  ; opam package for `opam pin add`
├── theories/
│   ├── dune               ; coq.theory stanza, package = rocq-crane-imgui
│   └── ImGuiE.v           ; the effect interface + Crane Extract Inductive
└── include/
    └── imgui_helpers.h    ; the C++ helper bodies referenced by the Crane
                          ; `Extract Inlined Constant ... From "imgui_helpers.h"`
                          ; directives in ImGuiE.v
```

## Status

The directory layout, `dune-project`, `theories/dune`, and `.opam` file
are in place; the live `theories/ImGuiE.v` and `src/imgui_helpers.h`
in the parent rocqsheet repo are mirrored here.  Two remaining
manual steps before this can replace the in-tree copies:

1. Push this directory to its own GitHub repo (e.g.
   `CharlesCNorton/rocq-crane-imgui`) and add it back to rocqsheet
   as a git submodule (`git submodule add <url> rocq-crane-imgui`).
2. `opam pin add -y rocq-crane-imgui ./rocq-crane-imgui`, add
   `rocq-crane-imgui` to rocqsheet's `dune-project` package
   `depends:`, swap `theories/dune`'s `(theories ... ImGuiE ...)`
   over to `(theories ... RocqCraneImGui ...)`, and update
   `src/CMakeLists.txt` to add `${REPO_ROOT}/rocq-crane-imgui/include`
   to the `target_include_directories`.

After that, the in-tree `theories/ImGuiE.v` and `src/imgui_helpers.h`
can be deleted and the parent build will pull them from the pinned
package.
