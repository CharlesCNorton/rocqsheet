// Copyright (c) 2026 CharlesCNorton.  Licensed under the MIT License.
//
// Display-layer number formatting (currency / decimal / percent / plain
// integer) bound to the [NumberFormat] inductive in
// [theories/NumberFormat.v].  The function is a template so the
// [Rocqsheet::NumberFormat] nested type can stay opaque to this header
// — instantiation happens at the call site (inside the extracted
// rocqsheet.cpp) where the full type is visible.

#ifndef INCLUDED_NUMBER_FORMAT_HELPERS
#define INCLUDED_NUMBER_FORMAT_HELPERS

#include <cstdint>
#include <sstream>
#include <string>
#include <variant>

namespace number_format_helpers {

template <typename NumFormat>
inline std::string format_z(int64_t value, const NumFormat& fmt) {
  using Integer  = typename NumFormat::NFInteger;
  using Decimal  = typename NumFormat::NFDecimal;
  using Currency = typename NumFormat::NFCurrency;
  using Percent  = typename NumFormat::NFPercent;

  if (std::holds_alternative<Integer>(fmt.v())) {
    return std::to_string(value);
  }
  if (std::holds_alternative<Decimal>(fmt.v())) {
    const auto& d = std::get<Decimal>(fmt.v());
    int64_t digits = d.d_a0;
    std::ostringstream oss;
    oss << value;
    if (digits > 0) {
      oss << ".";
      for (int64_t i = 0; i < digits; ++i) oss << "0";
    }
    return oss.str();
  }
  if (std::holds_alternative<Currency>(fmt.v())) {
    std::ostringstream oss;
    if (value < 0) {
      oss << "-$" << -value;
    } else {
      oss << "$" << value;
    }
    return oss.str();
  }
  if (std::holds_alternative<Percent>(fmt.v())) {
    std::ostringstream oss;
    oss << (value * 100) << "%";
    return oss.str();
  }
  return std::to_string(value);
}

template <typename NumFormat>
inline std::string format_float(double value, const NumFormat& fmt) {
  using Integer  = typename NumFormat::NFInteger;
  using Decimal  = typename NumFormat::NFDecimal;
  using Currency = typename NumFormat::NFCurrency;
  using Percent  = typename NumFormat::NFPercent;

  if (std::holds_alternative<Decimal>(fmt.v())) {
    const auto& d = std::get<Decimal>(fmt.v());
    int64_t digits = d.d_a0;
    std::ostringstream oss;
    oss.precision(digits < 0 ? 0 : static_cast<int>(digits));
    oss.setf(std::ios::fixed);
    oss << value;
    return oss.str();
  }
  if (std::holds_alternative<Currency>(fmt.v())) {
    std::ostringstream oss;
    oss.precision(2);
    oss.setf(std::ios::fixed);
    if (value < 0) {
      oss << "-$" << -value;
    } else {
      oss << "$" << value;
    }
    return oss.str();
  }
  if (std::holds_alternative<Percent>(fmt.v())) {
    std::ostringstream oss;
    oss.precision(2);
    oss.setf(std::ios::fixed);
    oss << (value * 100.0) << "%";
    return oss.str();
  }
  // Integer / fallback for floats: just stringify.
  if (std::holds_alternative<Integer>(fmt.v())) {
    return std::to_string(value);
  }
  return std::to_string(value);
}

}  // namespace number_format_helpers

#endif  // INCLUDED_NUMBER_FORMAT_HELPERS
