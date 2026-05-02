# Rocqsheet TODO

1. **Insert / delete row or column with formula updates.** Data-level
   smokes are in `Shift.v`; remaining is the formula-ref shifting and
   `insert ∘ delete = id` on the inverse position.
   *Theorems:* `formulas updated consistently with shifts`,
   `insert ∘ delete = id` on the inverse position.

2. **Full sort by column.** Row-swap building block plus
   per-swap permutation are in `Sorting.v`; the full insertion or
   bubble sort plus monotonic-after-sort theorems remain.
   *Theorems:* `sort_is_permutation`, `sorted_after_sort`.

3. **Save / load round-trip on the full sheet.** `Persistence.v`
   covers CLit cells and PCell type-level round-trip; full Sheet
   round-trip across all cell variants is the residual.
   *Theorems:* `load (save s) = s` over arbitrary sheets;
   `save_then_load_then_eval` correspondence.

4. **PDF export.** CSV export is implemented; PDF requires a
   printing/typesetting layer.

5. **Connect `formula::eval_iter` to the Rocq spec.** Empirical
   correspondence in `tests/kernel_test.cpp` does not cover all
   inputs.
   *Theorems:* `eval_iter_correspondence`: for every `s, r`,
   `formula::eval_iter s r` matches `eval_cell DEFAULT_FUEL s r`
   (modulo error-type collapse). Requires either a Coq small-step
   semantics for `eval_iter` plus a simulation argument, or a
   handwritten C++ replacement whose Coq model is auditable.

6. **Extract ImGui bindings into a reusable `rocq-crane-imgui`
   package.** `ImGuiE.v` plus `imgui_helpers.h` are inlined in
   this repo and cannot be consumed by other Rocq projects
   targeting ImGui.
   *Cure:* split into a stand-alone repo, add `opam pin add
   rocq-crane-imgui ./rocq-crane-imgui` to the install script,
   replace the inlined module with a submodule.

7. **Finish splitting theorems into `RocqsheetProofs.v`.**
   `RocqsheetProofs.v` exists with a small starter set; the bulk
   of `Rocqsheet.v`'s theorems still live alongside the kernel
   definitions and would benefit from migration.

8. **Add runtime tests for the newer theory modules.**
   `kernel_test.cpp` and `formula_test.cpp` exercise the kernel
   evaluator and the parser; `Filter`, `Comments`, `Date`,
   `NamedRanges`, `FindReplace`, `Shift`, `Csv`, `Merges`,
   `Sorting`, `Persistence`, `PersistentSheet`, `Dirty`,
   `Effects`, `Macros`, `Concurrent`, `Formatting`, `NumberFormat`,
   `Charts`, `Conditional` are not exercised in C++ once they are
   wired in.
