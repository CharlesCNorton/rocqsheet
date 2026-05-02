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

6. **Bit-identical cross-platform determinism.**
    *Theorems:* `forall w, eval_workbook w` is independent of host
    platform, given `PrimFloat` IEEE conformance and the saturating
    `Z` overrides.

7. **Verified financial primitives.** `BLACK_SCHOLES`, `PV`, `IRR`,
    Greeks (`Delta`, `Gamma`, `Vega`, `Theta`, `Rho`), Black-76,
    swaption pricing.
    *Theorems:* `put_call_parity`, `vega_monotone_in_vol`,
    `gamma_convex_in_strike`, `IRR_NPV_zero`.

8. **Inline contract checking in the formula bar.** Each column
    declares an invariant; on commit the kernel attempts to
    discharge the formula's obligation against it; failure is
    rendered as a red marker.
    *Theorems:* the discharge procedure is sound (no formula passes
    that invalidates the column invariant on any input).

9. **Sheet-level dependent types.** Column `B` declared as
    `Vector R (length A)` indexes `B` by `A`'s row count.
    *Theorems:* well-typedness preserved by every `pure_edit_step`.

10. **Sandboxed scripting language.** Extend `Macros.v` to a typed
    expression language whose effects appear only as documented
    event constructors.
    *Theorems:* `macro_pure` (no effect constructor reached) implies
    sheet-only effect; `sandbox_total` (every macro terminates).

11. **Property-based regressions on save.** Per-column `Prop`s
    sampled across the sheet via QuickChick; counter-examples
    surface as marked cells.
    *Theorems:* every supported `Prop` is decidable on closed cell
    values.

12. **Static error-reachability analysis.** `analyze_workbook : Sheet
    -> list (CellRef * ErrorClass)` over `EErr` paths,
    divide-by-zero witnesses, and `NaN` producers.
    *Theorems:* `analysis_complete` (any cell that evaluates to
    `EErr` appears in the list); `analysis_sound` (every listed
    cell has an input that drives it to its listed class).
