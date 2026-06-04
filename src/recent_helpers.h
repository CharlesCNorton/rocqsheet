// per-user "Open Recent" history persisted at
// ~/.config/rocqsheet/recent (one path per line, newest first).
// recent_helpers::record(path) prepends `path`, dedupes, caps the
// list at MAX_RECENT, atomically rewrites the file via tmp + rename.
// recent_helpers::list() returns the current vector.
//
// Backed by std::filesystem.  No locking: this file is single-user.

#ifndef ROCQSHEET_RECENT_HELPERS_H
#define ROCQSHEET_RECENT_HELPERS_H

#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <filesystem>
#include <system_error>

template <typename T> struct List;

namespace recent_helpers {

constexpr std::size_t MAX_RECENT = 10;

inline std::filesystem::path config_dir() {
  const char* xdg = std::getenv("XDG_CONFIG_HOME");
  std::filesystem::path base;
  if (xdg && *xdg) {
    base = xdg;
  } else {
    const char* home = std::getenv("HOME");
    if (home && *home) {
      base = std::filesystem::path(home) / ".config";
    } else {
      base = std::filesystem::temp_directory_path();
    }
  }
  return base / "rocqsheet";
}

inline std::filesystem::path recent_path() {
  return config_dir() / "recent";
}

inline std::vector<std::string> read_lines() {
  std::vector<std::string> out;
  std::ifstream in(recent_path());
  if (!in.is_open()) return out;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) out.push_back(line);
    if (out.size() >= MAX_RECENT * 2) break;
  }
  return out;
}

inline bool write_lines_atomic(const std::vector<std::string>& xs) {
  std::error_code ec;
  std::filesystem::create_directories(config_dir(), ec);
  if (ec) return false;
  auto target = recent_path();
  auto tmp = target;
  tmp += ".tmp";
  {
    std::ofstream out(tmp, std::ios::binary | std::ios::trunc);
    if (!out.is_open()) return false;
    for (const auto& s : xs) {
      out << s << '\n';
    }
    out.flush();
  }
  std::filesystem::rename(tmp, target, ec);
  return !ec;
}

inline void record(const std::string& path) {
  if (path.empty()) return;
  auto xs = read_lines();
  std::vector<std::string> next;
  next.reserve(xs.size() + 1);
  next.push_back(path);
  for (const auto& s : xs) {
    if (s != path) next.push_back(s);
    if (next.size() >= MAX_RECENT) break;
  }
  write_lines_atomic(next);
}

// Defined in recent_helpers.cpp where the full [List<std::string>]
// template body is visible (this header is included by the generated
// code before the List template is defined).
::List<std::string> list();

}  // namespace recent_helpers

#endif  // ROCQSHEET_RECENT_HELPERS_H
