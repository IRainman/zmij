// A double-to-string conversion library: https://github.com/vitaut/zmij/
//
// Copyright (c) 2025 - present, Victor Zverovich
// Distributed under the MIT license (see LICENSE) or alternatively
// the Boost Software License, Version 1.0.

#ifndef ZMIJ_TO_CHARS_H_
#define ZMIJ_TO_CHARS_H_

#include <stddef.h>  // size_t
#include <string.h>  // memcpy

#include <system_error>  // std::errc

#include "zmij.h"

namespace zmij {

/// Like std::to_chars_result, but available without C++17.
struct to_chars_result {
  char* ptr;
  std::errc ec;
};

/// Like std::chars_format, but available without C++17.
using chars_format = format;

namespace detail {

// Writes `value` in hexadecimal floating-point notation (see write_hex) without
// the "0x" prefix, to match std::to_chars. A negative `precision` selects the
// shortest form; otherwise the fraction has exactly `precision` hex digits.
template <typename Float>
auto to_chars_hex(char* first, char* last, Float value, int precision)
    -> to_chars_result {
  size_t cap = size_t(last - first);
  size_t size = 0;
  if (precision >= 0) {
    size = write_hex(value, precision, first, cap, /*prefix=*/false);
  } else {
    char buffer[buffer_sizes<Float>::hex];
    size = size_t(write_hex(value, buffer, /*prefix=*/false) - buffer);
    memcpy(first, buffer, size < cap ? size : cap);
  }
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}

// Writes `value` in its shortest form to `buffer` in `scientific`, `general`
// (printf %g rule), or `fixed` notation, and returns a pointer past the last
// character written. Requires buffer_sizes<double>::fixed capacity for `fixed`
// and buffer_sizes<double>::scientific otherwise.
inline auto to_chars(double value, char* buffer, chars_format fmt) noexcept
    -> char* {
  dec_fp dec = to_decimal(value);
  if (dec.negative) *buffer++ = '-';
  if (dec.exp == non_finite_exp) {
    memcpy(buffer, dec.sig != 0 ? "nan" : "inf", 3);
    return buffer + 3;
  }
  if (dec.sig == 0) {
    *buffer++ = '0';
    return fmt == chars_format::scientific ? write_big_exp(buffer, 0) : buffer;
  }

  char buf[20];
  char* digits = buf + sizeof(buf);
  int num_digits = 0;
  for (unsigned long long sig = dec.sig; sig != 0; sig /= 10, ++num_digits)
    *--digits = char('0' + sig % 10);
  int lead_exp = dec.exp + num_digits - 1;  // leading digit's decimal exponent
  while (digits[num_digits - 1] == '0') --num_digits;  // strip trailing zeros

  // Fixed for `fixed`, or for `general` when the leading exponent fits [-4,
  // num_digits); otherwise scientific.
  bool fixed = fmt == chars_format::fixed ||
               (fmt == chars_format::general && lead_exp >= -4 &&
                lead_exp < num_digits);
  if (!fixed) {
    // Scientific: leading digit, then '.' and the remaining significant digits.
    *buffer++ = digits[0];
    if (num_digits > 1) {
      *buffer++ = '.';
      memcpy(buffer, digits + 1, size_t(num_digits - 1));
      buffer += num_digits - 1;
    }
    return write_big_exp(buffer, lead_exp);
  }

  // Fixed: the integer part (or a single 0) padded with trailing zeros, then
  // the fractional digits prefixed with leading zeros for magnitudes below 1.
  int num_int_digits = lead_exp >= 0 ? lead_exp + 1 : 0;
  int int_sig = num_int_digits < num_digits ? num_int_digits : num_digits;
  if (num_int_digits == 0) *buffer++ = '0';
  memcpy(buffer, digits, size_t(int_sig));
  buffer += int_sig;
  for (int z = int_sig; z < num_int_digits; ++z) *buffer++ = '0';
  if (int_sig < num_digits) {
    *buffer++ = '.';
    for (int z = lead_exp; z < -1; ++z) *buffer++ = '0';
    memcpy(buffer, digits + int_sig, size_t(num_digits - int_sig));
    buffer += num_digits - int_sig;
  }
  return buffer;
}

template <typename Float>
auto to_chars(char* first, char* last, Float value, chars_format fmt,
              int precision) -> to_chars_result {
  // Match printf: a negative precision defaults to 6, and `general` uses at
  // least one significant digit.
  if (precision < 0)
    precision = 6;
  else if (precision == 0 && fmt == chars_format::general)
    precision = 1;
  size_t cap = size_t(last - first);

  // Scientific counts fractional digits, so 18 would need 19 significant.
  int max_precision = fmt == chars_format::scientific ? 17 : 18;
  if (precision > max_precision) {
    size_t size = write_big(value, precision, first, cap, fmt);
    if (size > cap) return {last, std::errc::value_too_large};
    return {first + size, {}};
  }

  using bs = buffer_sizes<Float>;
  size_t max_size = fmt == chars_format::fixed ? bs::fixed : bs::scientific;
  char buffer[bs::fixed];
  char* dst = cap >= max_size ? first : buffer;
  char* end;
  if (fmt == chars_format::scientific)
    end = write_scientific(value, precision + 1, dst);
  else if (fmt == chars_format::fixed)
    end = write_fixed(value, precision, dst);
  else
    end = write_general(value, precision, dst);
  if (dst == first) return {end, {}};  // Wrote directly into the output.
  size_t size = size_t(end - buffer);
  memcpy(first, buffer, size < cap ? size : cap);
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}

}  // namespace detail

/// Writes the shortest correctly rounded decimal representation of `value` to
/// [`first`, `last`), without a null terminator, like std::to_chars.
///
/// Returns:
/// - {ptr, std::errc()} on success, with ptr past the last character written;
/// - {last, std::errc::value_too_large} if the output does not fit, after
///   writing a truncated result to [`first`, `last`).
inline auto to_chars(char* first, char* last, float value) -> to_chars_result {
  if (size_t(last - first) >= float_buffer_size)
    return {detail::write(value, first), {}};
  char buffer[float_buffer_size];
  size_t cap = size_t(last - first);
  size_t size = size_t(detail::write(value, buffer) - buffer);
  memcpy(first, buffer, size < cap ? size : cap);
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}
inline auto to_chars(char* first, char* last, double value) -> to_chars_result {
  if (size_t(last - first) >= double_buffer_size)
    return {detail::write(value, first), {}};
  char buffer[double_buffer_size];
  size_t cap = size_t(last - first);
  size_t size = size_t(detail::write(value, buffer) - buffer);
  memcpy(first, buffer, size < cap ? size : cap);
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}
inline auto to_chars(char* first, char* last, long double value)
    -> to_chars_result {
#if LDBL_MANT_DIG == DBL_MANT_DIG
  return to_chars(first, last, double(value));
#else
  size_t cap = size_t(last - first);
  size_t size = detail::write_big(value, first, cap);
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
#endif
}

/// Writes the shortest representation of `value` in the given `fmt` to
/// [`first`, `last`), like std::to_chars with a format but no precision.
///
/// For `double` all formats are implemented (`hex` in shortest form without the
/// 0x prefix); the float and long double decimal formats return
/// {first, not_supported}.
///
/// Returns:
/// - {ptr, std::errc()} on success, with ptr past the last character written;
/// - {last, std::errc::value_too_large} if the output does not fit, after
///   writing a truncated result to [`first`, `last`).
inline auto to_chars(char* first, char* last, float value, chars_format fmt)
    -> to_chars_result {
  if (fmt == chars_format::hex)
    return detail::to_chars_hex(first, last, double(value), /*precision=*/-1);
  return {first, std::errc::not_supported};
}
inline auto to_chars(char* first, char* last, double value, chars_format fmt)
    -> to_chars_result {
  if (fmt == chars_format::hex)
    return detail::to_chars_hex(first, last, value, /*precision=*/-1);
  using bs = buffer_sizes<double>;
  size_t max_size = fmt == chars_format::fixed ? bs::fixed : bs::scientific;
  size_t cap = size_t(last - first);
  char buffer[bs::fixed];
  char* dst = cap >= max_size ? first : buffer;
  char* end = detail::to_chars(value, dst, fmt);
  if (dst == first) return {end, {}};
  size_t size = size_t(end - buffer);
  memcpy(first, buffer, size < cap ? size : cap);
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}
inline auto to_chars(char* first, char* last, long double value,
                     chars_format fmt) -> to_chars_result {
  if (fmt == chars_format::hex)
    return detail::to_chars_hex(first, last, value, /*precision=*/-1);
  return {first, std::errc::not_supported};
}

/// Writes `value` to [`first`, `last`) in the given `fmt` with `precision`
/// digits, like std::to_chars with a format and precision. `precision` counts
/// fractional digits for `fixed` and `scientific` and significant digits for
/// `general`, and fractional hex digits for `hex`. Matching printf, a negative
/// `precision` defaults to 6 and `general` treats 0 as 1; for `hex` a negative
/// `precision` selects the shortest form. `hex` omits the 0x prefix, e.g.
/// 1.8p+1.
///
/// Returns:
/// - {ptr, std::errc()} on success, with ptr past the last character written;
/// - {last, std::errc::value_too_large} if the output does not fit, after
///   writing a truncated result to [`first`, `last`).
inline auto to_chars(char* first, char* last, float value, chars_format fmt,
                     int precision) -> to_chars_result {
  return fmt == chars_format::hex
             ? detail::to_chars_hex(first, last, double(value), precision)
             : detail::to_chars(first, last, value, fmt, precision);
}
inline auto to_chars(char* first, char* last, double value, chars_format fmt,
                     int precision) -> to_chars_result {
  return fmt == chars_format::hex
             ? detail::to_chars_hex(first, last, value, precision)
             : detail::to_chars(first, last, value, fmt, precision);
}

/// Writes `value` to [`first`, `last`) in the given `fmt` with `precision`
/// digits, like std::to_chars with a format and precision. `precision` counts
/// fractional digits for `fixed` and `scientific` and significant digits for
/// `general`, and fractional hex digits for `hex`. Matching printf, a negative
/// `precision` defaults to 6 and `general` treats 0 as 1; for `hex` a negative
/// `precision` selects the shortest form. `hex` omits the 0x prefix, e.g.
/// 1.8p+1.
///
/// Returns:
/// - {ptr, std::errc()} on success, with ptr past the last character written;
/// - {last, std::errc::value_too_large} if the output does not fit, after
///   writing a truncated result to [`first`, `last`);
/// - {last, std::errc::not_enough_memory} on allocation failure (only possible
///   for an extended long double).
inline auto to_chars(char* first, char* last, long double value,
                     chars_format fmt, int precision) -> to_chars_result {
  if (double(value) == value)
    return to_chars(first, last, double(value), fmt, precision);
  if (fmt == chars_format::hex)
    return detail::to_chars_hex(first, last, value, precision);
  // Match printf: a negative precision defaults to 6, and `general` uses at
  // least one significant digit.
  if (precision < 0)
    precision = 6;
  else if (precision == 0 && fmt == chars_format::general)
    precision = 1;
  size_t cap = size_t(last - first);
  size_t size = detail::write_big(value, precision, first, cap, fmt);
  if (size == 0) return {first, std::errc::not_enough_memory};
  if (size > cap) return {last, std::errc::value_too_large};
  return {first + size, {}};
}

}  // namespace zmij

#endif  // ZMIJ_TO_CHARS_H_
