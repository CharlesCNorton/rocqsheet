# Rocqsheet TODO

1. **Multiple sheets / workbooks.** `CellRef` gains a sheet id.
   *Theorems:* `set_on_sheet_a_doesnt_change_sheet_b`,
   `cross_sheet_eval_factors_through`, sheet-scoped name lookup.

2. **Insert / delete row or column.** Shifts cell refs across
   formulas.
   *Theorems:* `insert_row r preserves rows < r`, `insert_row r
   shifts refs ≥ r by +1`, `delete_row r drops r and shifts > r
   by -1`, `formulas updated consistently with shifts`,
   `insert ∘ delete = id` on the inverse position.

3. **Sort by column.** Reorders rows.
   *Theorems:* `sort_is_permutation`, `sorted_after_sort` (column
   monotonic), `formulas_with_relative_refs_track_sort` (or fail
   loudly).

4. **Save / load round-trip on the kernel state.** Currently
   serialises edit-buffer text, not the `Sheet`.
   *Theorems:* `load (save s) ≈ s` up to non-edit-buffer fields,
   idempotence on no-change, `save_then_load_then_eval = eval
   directly`.

5. **PDF export.** CSV export is implemented; PDF requires a
   printing/typesetting layer.

6. Cell formatting (bold, color, borders, alignment).

7. Number formatting (decimals, currency, percent); the
   `format_then_parse = original` round-trip lemma would apply if
   a parser is added.

8. Charts.

9. Conditional formatting.

10. **Connect `formula::eval_iter` to the Rocq spec.** Empirical
    correspondence in `tests/kernel_test.cpp` does not cover all
    inputs.
    *Theorems:* `eval_iter_correspondence`: for every `s, r`,
    `formula::eval_iter s r` matches `eval_cell DEFAULT_FUEL s r`
    (modulo error-type collapse). Requires either a Coq small-step
    semantics for `eval_iter` plus a simulation argument, or a
    handwritten C++ replacement whose Coq model is auditable.

11. **Add `move_selection` bounds-respect.** Clamping logic exists
    in code but is not proved.
    *Theorems:* `move_selection_in_bounds`: for any `dc, dr, ls`,
    the resulting selection (when present) satisfies `valid_ref`.

12. **State `run_app` productivity.** The cofix is guarded by
    construction but no theorem characterises the per-frame outcome.
    *Theorems:* `run_app_either_quits_or_progresses`: at each step,
    `process_frame ls` either signals quit or yields a
    `pure_edit_step` successor.

13. **Extract ImGui bindings into a reusable `rocq-crane-imgui`
    package.** `ImGuiE.v` plus `imgui_helpers.h` are inlined in
    this repo and cannot be consumed by other Rocq projects
    targeting ImGui.
    *Cure:* split into a stand-alone repo, add `opam pin add
    rocq-crane-imgui ./rocq-crane-imgui` to the install script,
    replace the inlined module with a submodule.

14. **Split theorems into a separate `RocqsheetProofs.v`.**
    `Rocqsheet.v` interleaves definitions and theorems and has
    grown past comfortable read length.

15. **Add runtime tests for the newer theory modules.**
    `kernel_test.cpp` and `formula_test.cpp` exercise the kernel
    evaluator and the parser; `Filter`, `Comments`, `Date`,
    `NamedRanges`, `FindReplace`, `Shift`, `Csv` are not exercised
    once they are wired in.
