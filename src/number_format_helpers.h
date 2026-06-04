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

// Floored division/modulo matching Coq's Z.div / Z.modulo, so the
// date rendering below mirrors the proven [days_to_date] exactly.
inline int64_t nf_floordiv(int64_t a, int64_t b) {
  int64_t q = a / b;
  int64_t r = a % b;
  return (r != 0 && ((r < 0) != (b < 0))) ? q - 1 : q;
}

// Transcription of [Rocqsheet.date_to_string]: Hinnant's
// civil-from-days over floored division, then "Y-MM-DD".  The
// torture suite cross-checks this against the extracted
// [Rocqsheet::date_to_string].
inline std::string format_days_as_date(int64_t z) {
  const int64_t zp  = z + 719468;
  const int64_t era = nf_floordiv(zp < 0 ? zp - 146096 : zp, 146097);
  const int64_t doe = zp - era * 146097;
  const int64_t yoe =
      nf_floordiv(doe - nf_floordiv(doe, 1460) + nf_floordiv(doe, 36524) -
                      nf_floordiv(doe, 146096),
                  365);
  const int64_t y0  = yoe + era * 400;
  const int64_t doy =
      doe - (365 * yoe + nf_floordiv(yoe, 4) - nf_floordiv(yoe, 100));
  const int64_t mp  = nf_floordiv(5 * doy + 2, 153);
  const int64_t d   = doy - nf_floordiv(153 * mp + 2, 5) + 1;
  const int64_t m   = mp + (mp < 10 ? 3 : -9);
  const int64_t y   = (m <= 2) ? y0 + 1 : y0;
  std::ostringstream oss;
  oss << y << "-";
  if (m < 10) oss << "0";
  oss << m << "-";
  if (d < 10) oss << "0";
  oss << d;
  return oss.str();
}

template <typename NumFormat>
inline std::string format_z(int64_t value, const NumFormat& fmt) {
  using Integer  = typename NumFormat::NFInteger;
  using Decimal  = typename NumFormat::NFDecimal;
  using Currency = typename NumFormat::NFCurrency;
  using Percent  = typename NumFormat::NFPercent;
  using Date     = typename NumFormat::NFDate;

  if (std::holds_alternative<Integer>(fmt.v())) {
    return std::to_string(value);
  }
  if (std::holds_alternative<Date>(fmt.v())) {
    return format_days_as_date(value);
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
  using Date     = typename NumFormat::NFDate;

  if (std::holds_alternative<Date>(fmt.v())) {
    // A float under a date format truncates to whole epoch days.
    return format_days_as_date(static_cast<int64_t>(value));
  }
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
