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

6. **Static error-reachability analysis.** `analyze_workbook : Sheet
    -> list (CellRef * ErrorClass)` over `EErr` paths,
    divide-by-zero witnesses, and `NaN` producers.
    *Theorems:* `analysis_complete` (any cell that evaluates to
    `EErr` appears in the list); `analysis_sound` (every listed
    cell has an input that drives it to its listed class).
