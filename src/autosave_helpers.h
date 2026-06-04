// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// the autosave cadence timer and the crash-recovery file
// probes.  The 30-second window lives on a C++ monotonic clock so the
// Coq tree needs no notion of wall time.

#ifndef ROCQSHEET_AUTOSAVE_HELPERS_H
#define ROCQSHEET_AUTOSAVE_HELPERS_H

#include <chrono>
#include <filesystem>
#include <string>
#include <system_error>

namespace autosave_helpers {

// True at most once per 30-second window, measured from process
// start / the previous true.
inline bool due() {
  using clock = std::chrono::steady_clock;
  static clock::time_point last = clock::now();
  const auto now = clock::now();
  if (now - last >= std::chrono::seconds(30)) {
    last = now;
    return true;
  }
  return false;
}

// True when [a] exists and is newer than [b] (or [b] is missing).
inline bool newer(const std::string& a, const std::string& b) {
  std::error_code ec;
  const auto ta = std::filesystem::last_write_time(a, ec);
  if (ec) return false;  // no autosave file
  const auto tb = std::filesystem::last_write_time(b, ec);
  if (ec) return true;   // autosave exists, base save does not
  return ta > tb;
}

inline void remove_file(const std::string& p) {
  std::error_code ec;
  std::filesystem::remove(p, ec);
}

}  // namespace autosave_helpers

#endif  // ROCQSHEET_AUTOSAVE_HELPERS_H
