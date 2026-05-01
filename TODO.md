# Rocqsheet TODO

1. **Float / decimal cells.** Extend `Cell` with `CFloat (r : R)` and
   `Expr` with `EFloat`, plus float arithmetic.
   *Theorems:* `eval_float_add_zero` (`a + 0 = a` modulo NaN),
   `eval_float_mul_zero`, NaN-propagation lemmas (`x op NaN = NaN`
   for any op), `commutativity_of_float_add` over non-NaN inputs,
   signed-zero equality.

2. **String / text cells.** Add `Cell::CStr`, `Expr::EStr`, plus
   `EConcat`, `ELen`, `ESubstr`.
   *Theorems:* `len (concat a b) = len a + len b`, `concat_assoc`,
   `concat_empty_l`, `concat_empty_r`, `substr_full = id`,
   `len_substr_le_len`.

3. **Boolean cells distinct from 0/1.** Currently comparisons return
   `Z`; a real boolean type would be cleaner.
   *Theorems:* `not_not b = b`, `and_comm`, `or_comm`, De Morgan,
   `if_true_then`, `if_false_else`.

4. **Aggregations (MIN, MAX) and parser support.** SUM, AVG, COUNT
   are implemented in the kernel; AVG and COUNT have parser tokens
   but no `parse_factor` arms yet, and SUM has no parser support.
   MIN and MAX are not in `Expr` and require new walkers in the
   mutual fixpoint.
   *Theorems:* `min_in_range`, `max_ge_min` for MIN/MAX; the SUM/
   AVG/COUNT theorems are mostly already discharged by the
   compositional and `vm_compute` smoke layer.

5. **Multiple sheets / workbooks.** `CellRef` gains a sheet id.
   *Theorems:* `set_on_sheet_a_doesnt_change_sheet_b`,
   `cross_sheet_eval_factors_through`, sheet-scoped name lookup.

6. **Insert / delete row or column.** Shifts cell refs across
   formulas.
   *Theorems:* `insert_row r preserves rows < r`, `insert_row r
   shifts refs ≥ r by +1`, `delete_row r drops r and shifts > r
   by -1`, `formulas updated consistently with shifts`,
   `insert ∘ delete = id` on the inverse position.

7. **Merge cells.** Visually one cell, internally many.
   *Theorems:* `eval_merged_region_at_top_left = eval_underlying`,
   `unmerge ∘ merge = id`, set on a merged region writes only the
   top-left.

8. **Sort by column.** Reorders rows.
   *Theorems:* `sort_is_permutation`, `sorted_after_sort` (column
   monotonic), `formulas_with_relative_refs_track_sort` (or fail
   loudly).

9. **Save / load round-trip on the kernel state.** Currently
   serialises edit-buffer text, not the `Sheet`.
   *Theorems:* `load (save s) ≈ s` up to non-edit-buffer fields,
   idempotence on no-change, `save_then_load_then_eval = eval
   directly`.

10. **PDF export.** CSV export is implemented; PDF requires a
    printing/typesetting layer.

11. **Dirty-tracking dependency graph.** Currently every visible
    cell re-evaluates every frame.
    *Theorems:* `dirty_set_after_set s r c = closure_of_dependents
    r`, `eval_only_dirty = eval_all` on the dirty cells,
    `clean_after_eval`.

12. **`set_cell` on a shared sheet copies the whole vector.**  At
    grid sizes above 50k cells the latency becomes visible.
    *Theorems:* would shift to a tree-shaped persistent structure
    (e.g. Hash Array Mapped Trie) with `get_set_eq` and `get_set_neq`
    re-proved.

13. **TODAY, NOW, RAND.** Non-deterministic / time-dependent.
    *Theorems:* requires an effect type (`clockE`, `randE` as ITree
    events) and lemmas about determinism modulo the effect
    interpreter; `TODAY ≤ NOW` after epoch, `RAND in [0, 1)`.

14. **Macros / embedded scripting.** Adds a sublanguage to the
    kernel.
    *Theorems:* macro semantics deterministic given input state,
    soundness with respect to direct user actions, sandbox boundary
    (no escape to host).

15. **Concurrent edits / collaboration.** Multi-user.
    *Theorems:* serialisability of operations, conflict resolution
    (CRDT lemmas), monotonicity of merge.

16. Cell formatting (bold, color, borders, alignment).

17. Number formatting (decimals, currency, percent); the
    `format_then_parse = original` round-trip lemma would apply if
    a parser is added.

18. Charts.

19. Conditional formatting.

20. **Wire `HiddenSet` into evaluation.** `Filter.v` defines a
    hidden set but `eval_cell` never consults it; the existing
    `filter_preserves_underlying_eval` is reflexivity over a
    signature that does not mention `HiddenSet`.
    *Theorems:* a `view : Sheet -> HiddenSet -> Sheet` (or per-cell
    wrapper), then `eval_cell f (view s hs) r = eval_cell f s r`
    when `r` is not in `hs`, plus an eval-suppressed lemma when it
    is.

21. **Wire `CommentMap` into a sheet wrapper.** `Comments.v` carries
    the same tautological `eval_cell f s r = eval_cell f s r`
    statement.
    *Theorems:* extend the sheet record to `{ cells; comments }`,
    then `eval_cell f (with_comment r c s) r' = eval_cell f s r'`,
    plus `lookup_comment` round-trip across sheet operations.

22. **Wire named ranges into `Expr`.** `NamedRanges.v` defines a
    `NameMap` but `Expr` has no `ENamed` constructor and
    `eval_expr` never resolves names.
    *Theorems:* `Expr ::= ... | ENamed (n : string)`; an
    `eval_with_names (nm : NameMap)` variant; `eval_named_eq`:
    `lookup_name nm n = Some r -> eval_with_names nm s (ENamed n)
    = eval_at_ref f visited s r`.

23. **Wire dates into `Cell` and `Expr`.** `Date.v` defines arithmetic
    that nothing reaches; `Cell` has no `CDate`, `Expr` has no
    `EAddDays` / `ESubDays` / `EWeekday`.
    *Theorems:* `Cell ::= ... | CDate`, `Expr ::= ... | EAddDays |
    ESubDays | EWeekday`, plus the existing `add_days_zero`,
    `sub_days_self`, `weekday_add_seven` lifted into `eval_expr`
    results.

24. **Add CSV theorems.** `Csv.v` has zero theorems.
    *Theorems:* `cell_to_csv (CLit n) = string_of_z n`,
    `cell_to_csv CEmpty = ""`, row-length and separator-count
    invariants, `parse_csv (to_csv s) = s` on the `CEmpty + CLit`
    subset, plus a decision for formula cells.

25. **Add eval-correspondence to `replace_int_in_expr`.**
    `FindReplace.v` only proves syntactic idempotence when
    `from = to`.
    *Theorems:* `replace_eval_commute`: evaluating the rewritten
    tree equals lifting `replace_int` over the original eval result;
    general idempotence for repeated replacement.

26. **Add compose and bounds theorems to `Shift.v`.** Only
    `shift_refs 0 0 e = e` is currently proved.
    *Theorems:* `shift_refs_compose`: `shift_refs dc1 dr1
    (shift_refs dc2 dr2 e) = shift_refs (dc1+dc2) (dr1+dr2) e`;
    `shift_refs_preserves_valid` when destination stays in-grid;
    eval correspondence under a co-shifted sheet.

27. **Add length and membership theorems to `Range.v`.** Only
    closed-input smoke theorems exist.
    *Theorems:* `length_range_cells lo hi = (cols × rows)` when
    `lo ≤ hi`; `mem_range_iff_in_rectangle`; connection between
    `range_cells` and the mutual fixpoint `sum_rows` / `sum_cols`.

28. **Connect cofix evaluator to fuel evaluator.**
    `RocqsheetCofix.v` is a parallel spec with no link back to
    `eval_expr`.
    *Theorems:* `eval_co_correspondence`:
    `(exists n, run_n n (eval_cell_co s r) = Some (Some v))` iff
    `(exists fuel, eval_cell fuel s r = EVal v)`.

29. **Connect `formula::eval_iter` to the Rocq spec.** Empirical
    correspondence in `tests/kernel_test.cpp` does not cover all
    inputs.
    *Theorems:* `eval_iter_correspondence`: for every `s, r`,
    `formula::eval_iter s r` matches `eval_cell DEFAULT_FUEL s r`
    (modulo error-type collapse). Requires either a Coq small-step
    semantics for `eval_iter` plus a simulation argument, or a
    handwritten C++ replacement whose Coq model is auditable.

30. **Connect `Saturation.v` lemmas to the Crane Extract overrides.**
    The `Z.add` / `Z.sub` / `Z.mul` overrides paste an inline
    `__builtin_*_overflow` lambda; `sat_add_correct` and friends
    are proved about a separate `sat_add` definition that the
    overrides do not call.
    *Cure:* either redirect overrides through a named C++ function
    whose Coq model is `sat_add`, or prove the inline lambda
    equivalent to `sat_add` via a Coq model of
    `__builtin_add_overflow`.

31. **Add a `pure_edit_step` inductive.** The set of legal
    `commit_to` / `do_undo` / `do_redo` / `do_clear` / `select_cell`
    transitions is implicit in code rather than stated as a
    relation.
    *Theorems:* `pure_edit_step ls ls' -> well_formed_sheet
    (ls_sheet ls')`; per-handler preservation lemmas.

32. **Add undo / redo round-trip.** No theorem links `do_undo` and
    `do_redo`.
    *Theorems:* when `ls_undo ls = prev :: _`, `do_redo (do_undo ls)`
    recovers `ls_sheet ls` and stack invariants.

33. **Add `move_selection` bounds-respect.** Clamping logic exists
    in code but is not proved.
    *Theorems:* `move_selection_in_bounds`: for any `dc, dr, ls`,
    the resulting selection (when present) satisfies `valid_ref`.

34. **Add `do_clear` invariant.** No theorem says `do_clear`
    produces a fresh state.
    *Theorems:* `do_clear_state`: `ls_selected = None`,
    `ls_edit_buf = nil`, `ls_parse_errs = nil`.

35. **Add `well_formed_loop_state`.** No predicate captures the
    invariants the handlers preserve.
    *Theorems:* the predicate plus `pure_edit_step` preservation;
    `well_formed_loop_state initial_loop_state`.

36. **State `run_app` productivity.** The cofix is guarded by
    construction but no theorem characterises the per-frame outcome.
    *Theorems:* `run_app_either_quits_or_progresses`: at each step,
    `process_frame ls` either signals quit or yields a
    `pure_edit_step` successor.

37. **Extract ImGui bindings into a reusable `rocq-crane-imgui`
    package.** `ImGuiE.v` plus `imgui_helpers.h` are inlined in
    this repo and cannot be consumed by other Rocq projects
    targeting ImGui.
    *Cure:* split into a stand-alone repo, add `opam pin add
    rocq-crane-imgui ./rocq-crane-imgui` to the install script,
    replace the inlined module with a submodule.

38. **Split theorems into a separate `RocqsheetProofs.v`.**
    `Rocqsheet.v` interleaves definitions and theorems and has
    grown past comfortable read length.

39. **Add runtime tests for the newer theory modules.**
    `kernel_test.cpp` and `formula_test.cpp` exercise the kernel
    evaluator and the parser; `Filter`, `Comments`, `Date`,
    `NamedRanges`, `FindReplace`, `Shift`, `Csv` are not exercised
    once they are wired in.
