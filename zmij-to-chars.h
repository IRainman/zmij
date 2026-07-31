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

// Like std::to_chars_result, but available without C++17.
struct to_chars_result {
  char* ptr;
  std::errc ec;
};

// Like std::chars_format, but available without C++17 (hex is unsupported).
// The values match std::chars_format so general == fixed | scientific.
enum class chars_format {
  scientific = 1,
  fixed = 2,
  general = 3,
};

/// Writes the shortest correctly rounded decimal representation of `value` to
/// [`first`, `last`) without a null terminator, like std::to_chars. On success
/// returns {ptr, std::errc()} with ptr past the last character written; if the
/// output is too small returns {last, std::errc::value_too_large} and writes
/// nothing.
inline auto to_chars(char* first, char* last, float value) -> to_chars_result {
  if (size_t(last - first) >= float_buffer_size)
    return {detail::write(value, first), {}};
  char buffer[float_buffer_size];
  size_t size = size_t(detail::write(value, buffer) - buffer);
  if (size > size_t(last - first)) return {last, std::errc::value_too_large};
  memcpy(first, buffer, size);
  return {first + size, {}};
}
inline auto to_chars(char* first, char* last, double value) -> to_chars_result {
  if (size_t(last - first) >= double_buffer_size)
    return {detail::write(value, first), {}};
  char buffer[double_buffer_size];
  size_t size = size_t(detail::write(value, buffer) - buffer);
  if (size > size_t(last - first)) return {last, std::errc::value_too_large};
  memcpy(first, buffer, size);
  return {first + size, {}};
}

/// Writes `value` in the given `fmt` with `precision` digits (fractional digits
/// for `fixed`, significant digits otherwise) to [`first`, `last`), like
/// std::to_chars with a format and precision. `precision` must be in the
/// supported range ([0, 18] for `fixed`, [1, 18] otherwise); otherwise returns
/// {first, std::errc::invalid_argument} and writes nothing. On success returns
/// {ptr, std::errc()}; if the output does not fit returns
/// {last, std::errc::value_too_large} and writes nothing.
inline auto to_chars(char* first, char* last, float value, chars_format fmt,
                     int precision) -> to_chars_result {
  int min_precision = fmt == chars_format::fixed ? 0 : 1;
  if (precision < min_precision || precision > 18)
    return {first, std::errc::invalid_argument};
  size_t cap = size_t(last - first);
  char buffer[float_fixed_buffer_size];
  char* end;
  if (fmt == chars_format::fixed) {
    if (cap >= float_fixed_buffer_size)
      return {detail::write_fixed(value, precision, first), {}};
    end = detail::write_fixed(value, precision, buffer);
  } else if (fmt == chars_format::scientific) {
    if (cap >= float_precision_buffer_size)
      return {detail::write_scientific(value, precision, first), {}};
    end = detail::write_scientific(value, precision, buffer);
  } else {
    if (cap >= float_precision_buffer_size)
      return {detail::write_general(value, precision, first), {}};
    end = detail::write_general(value, precision, buffer);
  }
  size_t size = size_t(end - buffer);
  if (size > cap) return {last, std::errc::value_too_large};
  memcpy(first, buffer, size);
  return {first + size, {}};
}
inline auto to_chars(char* first, char* last, double value, chars_format fmt,
                     int precision) -> to_chars_result {
  int min_precision = fmt == chars_format::fixed ? 0 : 1;
  if (precision < min_precision || precision > 18)
    return {first, std::errc::invalid_argument};
  size_t cap = size_t(last - first);
  char buffer[double_fixed_buffer_size];
  char* end;
  if (fmt == chars_format::fixed) {
    if (cap >= double_fixed_buffer_size)
      return {detail::write_fixed(value, precision, first), {}};
    end = detail::write_fixed(value, precision, buffer);
  } else if (fmt == chars_format::scientific) {
    if (cap >= double_precision_buffer_size)
      return {detail::write_scientific(value, precision, first), {}};
    end = detail::write_scientific(value, precision, buffer);
  } else {
    if (cap >= double_precision_buffer_size)
      return {detail::write_general(value, precision, first), {}};
    end = detail::write_general(value, precision, buffer);
  }
  size_t size = size_t(end - buffer);
  if (size > cap) return {last, std::errc::value_too_large};
  memcpy(first, buffer, size);
  return {first + size, {}};
}

}  // namespace zmij

#endif  // ZMIJ_TO_CHARS_H_
