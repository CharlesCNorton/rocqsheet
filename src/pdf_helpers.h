// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Forward-declared PDF emitter.  The body in pdf_helpers.cpp pulls
// in the generated rocqsheet.h for the full [List<...>] body; this
// header keeps a forward declaration so the Crane-extracted code
// can resolve the symbol via the same include it already pulls in
// for [imgui_helpers].
//
// The Coq side flattens each page into a list of (x, y, text)
// tuples — that way this header never has to mention [Cell] /
// [CellRef] / [persistent_array], side-stepping the nested-type
// forward-declaration problem with Crane's [struct Rocqsheet].

#ifndef INCLUDED_PDF_HELPERS
#define INCLUDED_PDF_HELPERS

#include <cstdint>
#include <string>
#include <utility>

template <typename T> struct List;

namespace pdf_helpers {

using PdfTextEntry = std::pair<std::pair<int64_t, int64_t>, std::string>;
using PdfPageEntries = List<PdfTextEntry>;

bool emit_pdf(const List<PdfPageEntries>& pages,
              const std::string& path);

}  // namespace pdf_helpers

#endif  // INCLUDED_PDF_HELPERS
