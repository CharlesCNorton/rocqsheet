# Rocqsheet TODO

1. **Render formatting metadata in the ImGui frontend.** `Formatting.v`
   and `NumberFormat.v` carry bold / colour / border / alignment /
   decimal precision; the renderer ignores them.  Wire `lookup_format`
   into `cell_display`.

2. **Sheet-tab UI consuming the Workbook layer.** `Workbook` and
   `WorkbookRef` exist Coq-side; the GUI shows one sheet.  Add tabs,
   carry the current sheet id in `loop_state`, and switch the render
   path to `(sheet_id, CellRef)`.

3. **Chart rendering.** `Charts.v` defines `ChartKind`; nothing
   draws.  Hook a `render_charts` step into `process_frame` with
   line / bar / pie / scatter primitives over ImGui's draw list.

4. **Wire editing operators into the menu and keyboard handler.**
   `Sorting`, `InsertDelete`, `Merges`, and `FindReplace` extract
   but are not user-reachable.  Add menu entries and key bindings
   that call them.

5. **PDF byte-stream emitter.** `Pdf.v` defines `PdfDoc`; no
   serialiser.  Add a C++ helper that consumes the extracted
   document and emits a minimal PDF 1.4 stream.

6. **Move `rocq-crane-imgui` into a stand-alone repository.**
   `rocq-crane-imgui/` holds the migrated files; create the GitHub
   repo, add an opam file, pin via `opam pin add rocq-crane-imgui`,
   replace the in-tree directory with a submodule.

7. **`formula::eval_iter` formal correspondence.** `EvalIterSpec.v`
   exposes `spec_value`; the simulation argument requires either a
   Coq small-step model of `formula::eval_iter` or a C++
   replacement whose Coq model is auditable.
   *Theorems:* `eval_iter_correspondence`: for every `s, r`,
   `formula::eval_iter s r = spec_value s r`.

8. **Hash-chained edit log.** Extend `Concurrent.OpLog` with a
   per-op hash of `(prev_hash, op, payload)`.
   *Theorems:* chain non-malleability under a collision-resistance
   assumption; replay from genesis reconstructs the current sheet;
   any tamper changes the chain head.

9. **Per-cell pre/postconditions.** A cell carries a Coq `Prop`
    over its result type; `commit_to` rejects writes that
    invalidate the predicate.
    *Theorems:* invariant preservation across the `pure_edit_step`
    relation; rejected writes leave `loop_state` unchanged.

10. **Unit-typed cells.** Add `Cell::CUnit` carrying `(Unit, Z)`
    over a finite tag set (`USD`, `EUR`, `GBP`, `M`, `S`, `BPS`).
    Arithmetic across mismatched units returns `EErr`.
    *Theorems:* `unit_safety` (no add/sub across distinct tags
    yields a non-`EErr` value); `conversion_round_trip` for
    explicit casts.

11. **Bit-identical cross-platform determinism.**
    *Theorems:* `forall w, eval_workbook w` is independent of host
    platform, given `PrimFloat` IEEE conformance and the saturating
    `Z` overrides.

12. **Verified financial primitives.** `BLACK_SCHOLES`, `PV`, `IRR`,
    Greeks (`Delta`, `Gamma`, `Vega`, `Theta`, `Rho`), Black-76,
    swaption pricing.
    *Theorems:* `put_call_parity`, `vega_monotone_in_vol`,
    `gamma_convex_in_strike`, `IRR_NPV_zero`.

13. **Snapshot-indexed history.** `HIST(r, t)` reads cell `r` at
    timestamp `t` from the audit log.
    *Theorems:* `HIST(r, current) = eval r`; `HIST(r, t)`
    factors through the `OpLog` prefix at `t`.

14. **Dependency-graph latency bound.** Bound the propagation depth
    after a single edit.
    *Theorems:* `forall s r c, depth (dirty_set_after_set s r c) <= N`
    when `s` satisfies a stated sparsity invariant.

15. **Inline contract checking in the formula bar.** Each column
    declares an invariant; on commit the kernel attempts to
    discharge the formula's obligation against it; failure is
    rendered as a red marker.
    *Theorems:* the discharge procedure is sound (no formula passes
    that invalidates the column invariant on any input).

16. **Sheet-level dependent types.** Column `B` declared as
    `Vector R (length A)` indexes `B` by `A`'s row count.
    *Theorems:* well-typedness preserved by every `pure_edit_step`.

17. **Sandboxed scripting language.** Extend `Macros.v` to a typed
    expression language whose effects appear only as documented
    event constructors.
    *Theorems:* `macro_pure` (no effect constructor reached) implies
    sheet-only effect; `sandbox_total` (every macro terminates).

18. **Property-based regressions on save.** Per-column `Prop`s
    sampled across the sheet via QuickChick; counter-examples
    surface as marked cells.
    *Theorems:* every supported `Prop` is decidable on closed cell
    values.

19. **Per-cell provenance hashes.** `value_hash r = H(formula,
    inputs_hashes)`.
    *Theorems:* identical workbooks under identical inputs produce
    identical hashes; collision-resistance reduction to the
    underlying digest.

20. **CRDT convergence proof for the operation log.** Merge over
    `Concurrent.OpLog`.
    *Theorems:* `merge_commutative`, `merge_associative`,
    `merge_idempotent`.

21. **Trade-ticket schema with round-trip.** Record `TradeTicket`
    with field-level invariants (`notional > 0`, `maturity >
    value_date`, `currency` in a finite set).
    *Theorems:* `book_to_sheet_to_book = id`; schema invariants
    preserved by every `pure_edit_step`.

22. **Static error-reachability analysis.** `analyze_workbook : Sheet
    -> list (CellRef * ErrorClass)` over `EErr` paths,
    divide-by-zero witnesses, and `NaN` producers.
    *Theorems:* `analysis_complete` (any cell that evaluates to
    `EErr` appears in the list); `analysis_sound` (every listed
    cell has an input that drives it to its listed class).
