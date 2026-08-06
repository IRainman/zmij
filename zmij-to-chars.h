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

/// Like std::chars_format, but available without C++17 (hex is unsupported).
using chars_format = format;

namespace detail {

template <typename Float>
inline auto to_chars(char* first, char* last, Float value, chars_format fmt,
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

/// Writes `value` to [`first`, `last`) in the given `fmt` with `precision`
/// digits, like std::to_chars with a format and precision. `precision` counts
/// fractional digits for `fixed` and `scientific` and significant digits for
/// `general`. Matching printf, a negative `precision` defaults to 6 and
/// `general` treats 0 as 1.
///
/// Returns:
/// - {ptr, std::errc()} on success, with ptr past the last character written;
/// - {last, std::errc::value_too_large} if the output does not fit, after
///   writing a truncated result to [`first`, `last`).
inline auto to_chars(char* first, char* last, float value, chars_format fmt,
                     int precision) -> to_chars_result {
  return detail::to_chars(first, last, value, fmt, precision);
}
inline auto to_chars(char* first, char* last, double value, chars_format fmt,
                     int precision) -> to_chars_result {
  return detail::to_chars(first, last, value, fmt, precision);
}

}  // namespace zmij

#endif  // ZMIJ_TO_CHARS_H_
