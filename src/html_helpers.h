// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// HTML-entity escaping for the [theories/Html.v] export path.  Living
// outside the Coq axiom string keeps the implementation editable
// without fighting Coq's `""`-doubling.

#ifndef INCLUDED_HTML_HELPERS
#define INCLUDED_HTML_HELPERS

#include <string>

namespace html_helpers {

inline std::string escape(const std::string& s) {
  std::string out;
  out.reserve(s.size());
  for (char c : s) {
    switch (c) {
      case '<':  out += "&lt;";   break;
      case '>':  out += "&gt;";   break;
      case '&':  out += "&amp;";  break;
      case '"':  out += "&quot;"; break;
      default:   out.push_back(c);
    }
  }
  return out;
}

}  // namespace html_helpers

#endif  // INCLUDED_HTML_HELPERS
