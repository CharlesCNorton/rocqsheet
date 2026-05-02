# Rocqsheet TODO

## Runtime and UI gaps

1. **Render formatting in the ImGui frontend.** `Formatting.v` and
   `NumberFormat.v` carry the metadata; the renderer ignores it.
   Wire `lookup_format` into `cell_display` so bold / color /
   borders / alignment / decimal-precision actually appear.

2. **Add sheet-tab UI for the Workbook layer.** `Workbook` and
   `WorkbookRef` are Coq-side; the GUI still shows one sheet.
   Tabs at the top, current-sheet state in `loop_state`, and the
   render path takes `(sheet_id, CellRef)` instead of `CellRef`.

3. **Render charts.** `Charts.v` defines `ChartKind` and `Chart`;
   the GUI does not draw them.  Hook `render_charts` into the
   per-frame procedure with line / bar / pie / scatter primitives
   on top of ImGui's draw list.

4. **Wire editing operators into the GUI.** `Sorting`, `InsertDelete`,
   `Merges`, `FindReplace` all extract; menu entries (Edit -> Sort
   Column, Edit -> Insert Row, Edit -> Merge Selection, Edit -> Find
   and Replace) and the keyboard handler need to call them.

5. **PDF byte-stream emitter.** `Pdf.v` defines `PdfDoc` and
   `append_page`; nothing renders the document to bytes.  Add a C++
   helper consuming the extracted document and emitting a minimal
   PDF 1.4 stream, or shell out to a typesetting tool.

6. **Lift smoke theorems to universal forms.** Many theorems land
   as `*_smoke` (closed-form `vm_compute` on specific inputs).
   Promote at least the algebraic laws (`eval_add_comm`,
   `eval_mul_assoc`, `eval_iferror_traps_cycle`, `concat_assoc`,
   `negb_involutive`, `andb_comm` over `EBool`) to universally
   quantified versions where the kernel actually supports it.

7. **Complete the `rocq-crane-imgui` repository split.**
   `rocq-crane-imgui/` has the migrated `ImGuiE.v` and
   `imgui_helpers.h`; create the stand-alone GitHub repo, add an
   opam file, pin via `opam pin add rocq-crane-imgui ./...`, and
   replace the in-tree directory with a submodule.

8. **`formula::eval_iter` formal correspondence.** `EvalIterSpec.v`
   exposes `spec_value`; the simulation argument requires either
   modelling `formula::eval_iter`'s small-step semantics in Coq
   or replacing the C++ implementation with one whose Coq model
   is auditable.

## Verified-finance feature surface

9. **Cryptographic audit chain.** Every cell edit signed and
   hash-chained.  The existing `Concurrent.OpLog` is one commit
   from being a Merkle log.  Add a chain-link record and a Coq
   theorem that the chain is non-malleable, that replay from
   genesis yields the current sheet, and that any tampering
   visibly breaks the chain hash.

10. **Cell-level pre/postconditions.** A cell carries a Coq `Prop`
    over its result (e.g. `A1 >= 0`, `row_total = SUM row`),
    checked on every edit; the kernel rejects invalidating writes.
    Refinement types for cells.  Excel's data validation is
    string comparison, not propositional.

11. **Unit-typed cells.** `USD`, `EUR`, meters, ms, basis-points
    as types. `USD + EUR` is a type error.  Static guarantee that
    closes the JPMorgan-London-Whale class of dimensional
    confusion.

12. **Bit-identical determinism across sites.** State and prove
    that the same workbook in NYC and Tokyo produces byte-identical
    floats.  Reachable because `PrimFloat` (IEEE) plus saturating
    `Z` overrides are both deterministic; the theorem captures it.

13. **Verified financial primitives.** `BLACK_SCHOLES`, `PV`,
    `IRR`, `BS_VEGA`, full Greeks, swaption pricing, Black-76, etc.
    Each with proven properties: put-call parity, monotonicity in
    volatility, convexity bounds.  Excel ships these as opaque
    DLLs that have been quietly patched for years.

14. **Time travel as a value.** `HIST(A1, "2024-Q3")` as a
    function over the snapshot ledger.  Combined with the audit
    chain (item 9), trace any current value back to the specific
    signed edit that produced it.

15. **Dependency-graph SLO proof.** "After this market-data update,
    no cell takes more than N ticks to converge" stated and proved
    against the `Dirty.v` machinery.

16. **Live proof obligation in the formula bar.** Type a formula;
    the system attempts to discharge its contract against the
    column's declared invariant; failure is shown inline.  TS for
    spreadsheets has nothing like this since TS lacks decision
    procedures.

17. **Sheet-level dependent types.** "Column B has type
    `Vector A.length R`" — cells indexed by other cells,
    automatic recomputation, well-typedness enforced.

18. **Verified macros / scripting sandbox.** `Macros.v` already
    factors through `set_cell` with a soundness theorem.  Extend
    to a small total scripting language (no `Eval`, no host escape,
    no DLL injection) where every macro is type-checked and is
    provably either pure or accesses a documented effect.

19. **Property-based regression on save.** "For any sample of 10
    rows, this column equals SUM of the others" is automatically
    QuickChick-tested when the sheet changes; counterexamples
    surface as red cells.

20. **Non-bypassable provenance.** Each cell value carries a
    hash of `(formula, inputs, prior values)`.  Two analysts on
    the same workbook with the same inputs produce identical
    hashes.  Auditors verify a regulatory filing was produced
    from a specific dataset by hash without seeing the dataset.

21. **CRDT collaboration with proven convergence.** Multi-user
    editing where the merge function has a Coq commutativity /
    associativity proof; the existing LWW `OpLog` is the starting
    point.  Google Sheets has convergence empirically; this
    delivers it formally.

22. **Trade-ticket round-trip with the book of record.** Schema
    with Coq invariants (`notional > 0`, `maturity > value_date`,
    `currency in {USD, EUR, GBP}`), verified round-trip to the
    trading book, plus a proof that the spreadsheet view never
    desynchronises.

23. **Formal model-risk analysis.** Static analysis of a workbook
    listing every cell's worst-case error path (`EErr`
    reachability), divide-by-zero possibilities with witnesses,
    and which formulas can produce `NaN`.  Closes the manual
    model-risk audit pass that banks run today.
