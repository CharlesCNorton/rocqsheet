# Rocqsheet TODO

1. **Wire editing operators into the menu and keyboard handler.**
   `Sorting`, `InsertDelete`, `Merges`, and `FindReplace` extract
   but are not user-reachable.  Add menu entries and key bindings
   that call them.

2. **PDF byte-stream emitter.** `Pdf.v` defines `PdfDoc`; no
   serialiser.  Add a C++ helper that consumes the extracted
   document and emits a minimal PDF 1.4 stream.
