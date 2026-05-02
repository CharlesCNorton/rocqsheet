# Rocqsheet TODO

1. **Save / load round-trip on the full sheet.** `Persistence.v`
   covers CLit cells and PCell type-level round-trip; full Sheet
   round-trip across all cell variants (including formula cells)
   is the residual.
   *Theorems:* `load (save s) = s` over arbitrary sheets;
   `save_then_load_then_eval` correspondence.

2. **Connect `formula::eval_iter` to the Rocq spec.** Empirical
   correspondence in `tests/kernel_test.cpp` does not cover all
   inputs.
   *Theorems:* `eval_iter_correspondence`: for every `s, r`,
   `formula::eval_iter s r` matches `eval_cell DEFAULT_FUEL s r`
   (modulo error-type collapse). Requires either a Coq small-step
   semantics for `eval_iter` plus a simulation argument, or a
   handwritten C++ replacement whose Coq model is auditable.

3. **Complete the `rocq-crane-imgui` package split.** A skeleton
   directory with a README is in place at `rocq-crane-imgui/`;
   the migration of `theories/ImGuiE.v` and `src/imgui_helpers.h`
   into it, plus the opam pin and submodule conversion, remain.

4. **Finish migrating theorems into `RocqsheetProofs.v`.**
   `RocqsheetProofs.v` exists with a starter set; the bulk of
   `Rocqsheet.v`'s theorems still live alongside the kernel
   definitions and would benefit from migration.

5. **Add runtime tests for the newer theory modules.**
   `kernel_test.cpp` and `formula_test.cpp` exercise the kernel
   evaluator and the parser; the newer theory modules (`Filter`,
   `Comments`, `Date`, `NamedRanges`, `FindReplace`, `Shift`, `Csv`,
   `Merges`, `Sorting`, `Persistence`, `PersistentSheet`, `Dirty`,
   `Effects`, `Macros`, `Concurrent`, `Formatting`, `NumberFormat`,
   `Charts`, `Conditional`, `InsertDelete`, `InsertionSort`, `Pdf`)
   are not exercised in C++ once they are wired in.

6. **Sheet-level integration of `InsertionSort`.** The list-level
   isort plus permutation theorem is in `InsertionSort.v`; tying it
   to a column-extraction-and-rebuild operation on `Sheet`, plus
   `sorted_after_sort` on the resulting sheet column, is the
   residual.

7. **Formula-ref shifting on insert/delete.** `InsertDelete.v`
   has `shift_ref_if_above` and an inverse smoke; the full
   sheet-wide application, where every formula cell's refs at or
   above the affected row are shifted, is the residual.
