# Rocqsheet TODO

Functionality gaps to close and the theorems each one brings.

> **Feature.** What it adds.
> *Theorems:* the proof obligations the addition creates.

---

## Cell types

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

4. **Date / time cells.** Days-since-epoch as `Z` plus arithmetic.
   *Theorems:* `add_days_zero = id`, `sub_days_self = 0`,
   `weekday (add_days d 7) = weekday d`, no overflow within range.

---

## Operators

5. **IFERROR / error-handling functions.** Let formulas trap `None`.
   *Theorems:* `eval_iferror_some_eq_first`,
   `eval_iferror_none_eq_fallback`, idempotence on already-non-None
   values.

---

## Ranges and aggregation

6. **Range references (`A1:A10`).** Add `Expr::ERange (CellRef ×
   CellRef)`.
   *Theorems:* `range_singleton (r, r) = [r]`,
   `range_inverted = nil`, `length_range = (cols × rows)`,
   `mem_range_iff_in_rectangle`.

7. **Aggregations (SUM, AVG, MIN, MAX, COUNT).** Operate on ranges.
   *Theorems:* `sum_empty = 0`, `sum_singleton = cell_value`,
   `sum_split (concat a b) = sum a + sum b`,
   `avg = sum / count`, `min_in_range`, `max_ge_min`,
   `count_eq_length`.

---

## Sheet structure

8. **Multiple sheets / workbooks.** `CellRef` gains a sheet id.
   *Theorems:* `set_on_sheet_a_doesnt_change_sheet_b`,
   `cross_sheet_eval_factors_through`, sheet-scoped name lookup.

9. **Insert / delete row or column.** Shifts cell refs across
   formulas.
   *Theorems:* `insert_row r preserves rows < r`, `insert_row r
   shifts refs ≥ r by +1`, `delete_row r drops r and shifts > r
   by -1`, `formulas updated consistently with shifts`,
   `insert ∘ delete = id` on the inverse position.

10. **Merge cells.** Visually one cell, internally many.
    *Theorems:* `eval_merged_region_at_top_left = eval_underlying`,
    `unmerge ∘ merge = id`, set on a merged region writes only the
    top-left.

11. **Larger / parameterised grid.** Currently 260×200; the
    `cell_index_in_grid` proof uses literal constants.
    *Theorems:* Generalise the bound proof so it holds for any
    chosen `NUM_COLS`/`NUM_ROWS` without re-proving.

---

## Editing

12. **Sort by column.** Reorders rows.
    *Theorems:* `sort_is_permutation`, `sorted_after_sort` (column
    monotonic), `formulas_with_relative_refs_track_sort` (or fail
    loudly).

13. **Filter.** UI-only hide; cells still eval.
    *Theorems:* `filter_preserves_underlying`,
    `unfilter ∘ filter = id`.

14. **Find / replace.** Bulk rewrite over cell sources.
    *Theorems:* `replace_idempotent_on_no_match`, `replace_then_replace`
    composition, `count_after_replace = 0` for the searched pattern.

15. **Auto-fill (drag a formula across a range).** Adjusts refs by
    offset.
    *Theorems:* `fill (r1..r2) e shifts refs in e by (r' - r1) for
    each r'`, `fill_singleton = set_cell`, `fill ∘ fill_inverse =
    id`.

16. **Named ranges.** Alias for a `CellRef` or range.
    *Theorems:* `eval_named_ref = eval_underlying_ref`,
    `lookup_after_define = Some`, `define_then_undefine = original`.

17. **Cell comments / metadata.** Non-evaluating annotation.
    *Theorems:* `eval_with_comment = eval_without`,
    `comment_round_trip_through_save_load`.

18. **Multi-cell selection + copy/paste with relative ref shift.**
    Current copy/paste is single-cell.
    *Theorems:* `paste_at_offset (dx, dy) shifts refs by (dx, dy)`,
    `copy then paste at original location = identity`,
    `paste preserves cell types`.

---

## Persistence and export

19. **Save / load round-trip on the kernel state.** Currently
    serialises edit-buffer text, not the `Sheet`.
    *Theorems:* `load (save s) ≈ s` up to non-edit-buffer fields,
    idempotence on no-change, `save_then_load_then_eval = eval
    directly`.

20. **CSV / PDF export.** String formatting layer.
    *Theorems:* `csv_round_trip` (`parse_csv (to_csv s) = s` on
    representable subsets), `cell_value_appears_in_csv_at_correct_
    position`.

---

## Verification gaps within current functionality

21. **Universal theorems for arithmetic.** Closed-input lifts are in
    place (`eval_add_lit`, `eval_sub_lit`, `eval_mul_lit`,
    `eval_eq_lit`, `eval_lt_lit`, commutativity, identity).  The
    universal forall-eval statement remains.
    *Theorems:* `forall a b, eval_expr (EAdd (EInt a) (EInt b)) ≈
    Z.add a b` (with sufficient fuel), `eval_expr_compositional`,
    plus algebraic laws (associativity, distributivity) lifted from
    `Z`.

22. **Saturation correctness.** The C++ `sat_add` / `sat_sub` /
    `sat_mul` correspond to overrides on `Z.add` / `Z.sub` / `Z.mul`,
    but no proof.
    *Theorems:* `sat_add_correct: sat_add a b = a + b OR
    (a + b > MAX AND result = MAX) OR (a + b < MIN AND result =
    MIN)`, similar for sub/mul.

---

## Performance and runtime

23. **Dirty-tracking dependency graph.** Currently every visible
    cell re-evaluates every frame.
    *Theorems:* `dirty_set_after_set s r c = closure_of_dependents
    r`, `eval_only_dirty = eval_all` on the dirty cells,
    `clean_after_eval`.

24. **`set_cell` on a shared sheet copies the whole vector.**  At
    grid sizes above 50k cells the latency becomes visible.
    *Theorems:* would shift to a tree-shaped persistent structure
    (e.g. Hash Array Mapped Trie) with `get_set_eq` and `get_set_neq`
    re-proved.

---

## Effectful additions

25. **TODAY, NOW, RAND.** Non-deterministic / time-dependent.
    *Theorems:* requires an effect type (`clockE`, `randE` as ITree
    events) and lemmas about determinism modulo the effect
    interpreter; `TODAY ≤ NOW` after epoch, `RAND in [0, 1)`.

26. **Macros / embedded scripting.** Adds a sublanguage to the
    kernel.
    *Theorems:* macro semantics deterministic given input state,
    soundness with respect to direct user actions, sandbox boundary
    (no escape to host).

27. **Concurrent edits / collaboration.** Multi-user.
    *Theorems:* serialisability of operations, conflict resolution
    (CRDT lemmas), monotonicity of merge.

---

## UI-only (no kernel theorems)

28. Cell formatting (bold, color, borders, alignment).
29. Number formatting (decimals, currency, percent) — display layer
    only; the `format_then_parse = original` round-trip lemma would
    apply if a parser is added.
30. Charts.
31. Conditional formatting.
