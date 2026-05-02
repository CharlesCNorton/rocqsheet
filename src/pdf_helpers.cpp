// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.

#include "pdf_helpers.h"
#include "rocqsheet.h"

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

namespace pdf_helpers {

namespace {

constexpr double PAGE_W = 612.0;
constexpr double PAGE_H = 792.0;
constexpr double FONT_SIZE = 9.0;

template <typename T>
void list_to_vec(const List<T>& xs, std::vector<T>& out) {
  const List<T>* p = &xs;
  while (p && std::holds_alternative<typename List<T>::Cons>(p->v())) {
    const auto& cell = std::get<typename List<T>::Cons>(p->v());
    out.push_back(cell.d_a0);
    p = cell.d_a1.get();
  }
}

std::string pdf_escape(const std::string& s) {
  std::string out;
  out.reserve(s.size() + 4);
  for (char c : s) {
    if (c == '\\' || c == '(' || c == ')') {
      out.push_back('\\');
      out.push_back(c);
    } else if (static_cast<unsigned char>(c) >= 32 &&
               static_cast<unsigned char>(c) < 127) {
      out.push_back(c);
    }
  }
  return out;
}

std::string build_content_stream(const PdfPageEntries& page) {
  std::vector<PdfTextEntry> entries;
  list_to_vec(page, entries);
  std::ostringstream s;
  s << "BT\n/F1 " << FONT_SIZE << " Tf\n";
  double last_x = 0.0;
  double last_y = 0.0;
  bool first = true;
  for (const auto& e : entries) {
    int64_t x = e.first.first;
    int64_t y = e.first.second;
    const std::string& text = e.second;
    if (text.empty()) continue;
    double dx = static_cast<double>(x) - (first ? 0.0 : last_x);
    double dy = static_cast<double>(y) - (first ? 0.0 : last_y);
    s << dx << " " << dy << " Td\n("
      << pdf_escape(text) << ") Tj\n";
    last_x = static_cast<double>(x);
    last_y = static_cast<double>(y);
    first = false;
  }
  s << "ET\n";
  return s.str();
}

}  // namespace

bool emit_pdf(const List<PdfPageEntries>& pages_list,
              const std::string& path) {
  std::vector<PdfPageEntries> pages;
  list_to_vec(pages_list, pages);
  if (pages.empty()) return false;

  std::ofstream f(path, std::ios::binary);
  if (!f) return false;

  std::vector<std::string> content_streams;
  for (const auto& p : pages)
    content_streams.push_back(build_content_stream(p));

  std::vector<std::streampos> offsets;
  auto record = [&]() { offsets.push_back(f.tellp()); };

  f << "%PDF-1.4\n%\xE2\xE3\xCF\xD3\n";

  record();
  f << "1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n";

  record();
  f << "2 0 obj\n<< /Type /Pages /Kids [";
  for (size_t i = 0; i < pages.size(); ++i)
    f << (4 + 2 * i) << " 0 R ";
  f << "] /Count " << pages.size() << " >>\nendobj\n";

  record();
  f << "3 0 obj\n<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica "
       "/Encoding /WinAnsiEncoding >>\nendobj\n";

  for (size_t i = 0; i < pages.size(); ++i) {
    record();
    f << (4 + 2 * i)
      << " 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 "
      << PAGE_W << " " << PAGE_H
      << "] /Resources << /Font << /F1 3 0 R >> >> /Contents "
      << (5 + 2 * i) << " 0 R >>\nendobj\n";

    record();
    const std::string& cs = content_streams[i];
    f << (5 + 2 * i) << " 0 obj\n<< /Length " << cs.size()
      << " >>\nstream\n" << cs << "endstream\nendobj\n";
  }

  std::streampos xref_offset = f.tellp();
  size_t total_objects = 3 + 2 * pages.size();
  f << "xref\n0 " << (total_objects + 1) << "\n";
  f << "0000000000 65535 f \n";
  for (auto off : offsets) {
    char buf[24];
    std::snprintf(buf, sizeof(buf), "%010lld 00000 n \n",
                  static_cast<long long>(off));
    f << buf;
  }

  f << "trailer\n<< /Size " << (total_objects + 1)
    << " /Root 1 0 R >>\nstartxref\n"
    << static_cast<long long>(xref_offset) << "\n%%EOF\n";

  return f.good();
}

}  // namespace pdf_helpers
