// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Implementation of [recent_helpers::list].  Lives in its own .cpp so
// the full body of [List<std::string>] is visible (the header only
// forward-declares the List template; the generated header includes
// recent_helpers.h before the List template is defined).

#include "recent_helpers.h"
#include "rocqsheet.h"

#include <memory>
#include <string>
#include <utility>

namespace recent_helpers {

::List<std::string> list() {
  auto xs = read_lines();
  if (xs.size() > MAX_RECENT) xs.resize(MAX_RECENT);
  ::List<std::string> out = ::List<std::string>::nil();
  for (auto it = xs.rbegin(); it != xs.rend(); ++it) {
    out = ::List<std::string>::cons(*it, std::move(out));
  }
  return out;
}

}  // namespace recent_helpers
