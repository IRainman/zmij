// A double-to-string conversion library: https://github.com/vitaut/zmij/
//
// Copyright (c) 2025 - present, Victor Zverovich
// Distributed under the MIT license (see LICENSE) or alternatively
// the Boost Software License, Version 1.0.

#ifndef ZMIJ_H_
#define ZMIJ_H_

#include <float.h>   // DBL_MANT_DIG, LDBL_MANT_DIG
#include <stddef.h>  // size_t
#include <string.h>  // memcpy

namespace zmij {

// Floating-point formatting style. Values match std::chars_format (hex is
// unsupported), so general == fixed | scientific.
enum class format {
  scientific = 1,
  fixed = 2,
  general = 3,
};

namespace detail {

template <typename Float>
auto write(Float value, char* buffer) noexcept -> char*;

template <typename Float>
auto write_big(Float value, int precision, char* out, size_t n,
               format fmt) noexcept -> char*;
template <>
inline auto write_big(float value, int precision, char* out, size_t n,
                      format fmt) noexcept -> char* {
  return write_big(double(value), precision, out, n, fmt);
}
#if LDBL_MANT_DIG == DBL_MANT_DIG
template <>
inline auto write_big(long double value, int precision, char* out, size_t n,
                      format fmt) noexcept -> char* {
  return write_big(double(value), precision, out, n, fmt);
}
#endif

template <typename Float>
auto write_scientific(Float value, int precision, char* buffer) noexcept
    -> char*;

template <typename Float>
auto write_general(Float value, int precision, char* buffer) noexcept -> char*;

template <typename Float>
auto write_fixed(Float value, int precision, char* buffer) noexcept -> char*;

}  // namespace detail

enum {
  non_finite_exp = int(~0u >> 1),
};

// A decimal floating-point number sig * pow(10, exp).
// If exp is non_finite_exp then the number is a NaN or an infinity.
struct dec_fp {
  long long sig;  // significand
  int exp;        // exponent
  bool negative;
};

/// Converts `value` into the shortest correctly rounded decimal representation.
/// Usage:
///   auto [sig, exp, negative] = to_decimal(6.62607015e-34);
auto to_decimal(double value) noexcept -> dec_fp;

enum {
  float_buffer_size = 17,   // shortest (write)
  double_buffer_size = 34,  // shortest (write)
};

/// Buffer sizes for the write* functions, usable in generic code as
/// buffer_sizes<Float>::shortest, ::scientific, and ::fixed.
template <typename Float> struct buffer_sizes;

template <> struct buffer_sizes<float> {
  static constexpr size_t shortest = float_buffer_size;  // write
  static constexpr size_t scientific = 24;  // write_scientific (and general)
  static constexpr size_t fixed = 59;       // write_fixed
};
template <> struct buffer_sizes<double> {
  static constexpr size_t shortest = double_buffer_size;  // write
  static constexpr size_t scientific = 25;  // write_scientific (and general)
  static constexpr size_t fixed = 329;      // write_fixed
};

/// Writes the shortest correctly rounded decimal representation of `value` to
/// `out` without a null terminator. Returns a pointer past the last character
/// written; if the representation exceeds `n` characters, only the first `n`
/// are written.
inline auto write(char* out, size_t n, float value) noexcept -> char* {
  if (n >= float_buffer_size) return detail::write(value, out);
  char buffer[float_buffer_size];
  size_t size = detail::write(value, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes the shortest correctly rounded decimal representation of `value` to
/// `out` without a null terminator. Returns a pointer past the last character
/// written; if the representation exceeds `n` characters, only the first `n`
/// are written.
inline auto write(char* out, size_t n, double value) noexcept -> char* {
  if (n >= double_buffer_size) return detail::write(value, out);
  char buffer[double_buffer_size];
  size_t size = detail::write(value, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with `precision` digits after the
/// decimal point (e.g. 1.234e+05) to `out` without a null terminator, like
/// printf's %e. Returns a pointer past the last character written; if the
/// representation exceeds `n` characters, only the first `n` are written.
/// A negative `precision` defaults to 6, matching printf.
inline auto write_scientific(char* out, size_t n, float value,
                             int precision) noexcept -> char* {
  if (precision < 0) precision = 6;
  if (precision >= 18)
    return detail::write_big(value, precision, out, n, format::scientific);
  if (n >= buffer_sizes<float>::scientific)
    return detail::write_scientific(value, precision + 1, out);
  char buffer[buffer_sizes<float>::scientific];
  size_t size = detail::write_scientific(value, precision + 1, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with `precision` digits after the
/// decimal point (e.g. 1.234e+05) to `out` without a null terminator, like
/// printf's %e. Returns a pointer past the last character written; if the
/// representation exceeds `n` characters, only the first `n` are written.
/// A negative `precision` defaults to 6, matching printf.
inline auto write_scientific(char* out, size_t n, double value,
                             int precision) noexcept -> char* {
  if (precision < 0) precision = 6;
  if (precision >= 18)
    return detail::write_big(value, precision, out, n, format::scientific);
  if (n >= buffer_sizes<double>::scientific)
    return detail::write_scientific(value, precision + 1, out);
  char buffer[buffer_sizes<double>::scientific];
  size_t size = detail::write_scientific(value, precision + 1, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with `precision` digits after the
/// decimal point (e.g. 1.234e+05) to `out` without a null terminator, like
/// printf's %e. Returns a pointer past the last character written; if the
/// representation exceeds `n` characters, only the first `n` are written.
/// A negative `precision` defaults to 6, matching printf.
inline auto write_scientific(char* out, size_t n, long double value,
                             int precision) noexcept -> char* {
  if (precision < 0) precision = 6;
  return detail::write_big(value, precision, out, n, format::scientific);
}

/// Writes `value` in general format with up to `precision` significant digits
/// and no trailing zeros (e.g. 1.5 or 1.5e+20) to `out` without a null
/// terminator. Fixed notation is used when `value`'s decimal exponent is in
/// [-4, precision), and scientific otherwise. Returns a pointer past the last
/// character written; if the representation exceeds `n` characters, only the
/// first `n` are written. A negative `precision` defaults to 6 and zero is
/// treated as 1, matching printf.
inline auto write_general(char* out, size_t n, float value,
                          int precision) noexcept -> char* {
  if (precision <= 1) precision = precision < 0 ? 6 : 1;
  if (precision > 18)
    return detail::write_big(value, precision, out, n, format::general);
  if (n >= buffer_sizes<float>::scientific)
    return detail::write_general(value, precision, out);
  char buffer[buffer_sizes<float>::scientific];
  size_t size = detail::write_general(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in general format with up to `precision` significant digits
/// and no trailing zeros (e.g. 1.5 or 1.5e+20) to `out` without a null
/// terminator. Fixed notation is used when `value`'s decimal exponent is in
/// [-4, precision), and scientific otherwise. Returns a pointer past the last
/// character written; if the representation exceeds `n` characters, only the
/// first `n` are written. A negative `precision` defaults to 6 and zero is
/// treated as 1, matching printf.
inline auto write_general(char* out, size_t n, double value,
                          int precision) noexcept -> char* {
  if (precision <= 1) precision = precision < 0 ? 6 : 1;
  if (precision > 18)
    return detail::write_big(value, precision, out, n, format::general);
  if (n >= buffer_sizes<double>::scientific)
    return detail::write_general(value, precision, out);
  char buffer[buffer_sizes<double>::scientific];
  size_t size = detail::write_general(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in fixed notation with exactly `precision` digits after the
/// decimal point (e.g. 1.500), to `out` without a null terminator. The result
/// is the exact value correctly rounded to the given precision (ties to even),
/// matching printf's %f. Returns a pointer past the last character written; if
/// the representation exceeds `n` characters, only the first `n` are written.
/// A negative `precision` defaults to 6, matching printf.
inline auto write_fixed(char* out, size_t n, float value,
                        int precision) noexcept -> char* {
  if (precision < 0) precision = 6;
  if (precision > 18)
    return detail::write_big(value, precision, out, n, format::fixed);
  if (n >= buffer_sizes<float>::fixed)
    return detail::write_fixed(value, precision, out);
  char buffer[buffer_sizes<float>::fixed];
  size_t size = detail::write_fixed(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in fixed notation with exactly `precision` digits after the
/// decimal point (e.g. 1.500), to `out` without a null terminator. The result
/// is the exact value correctly rounded to the given precision (ties to even),
/// matching printf's %f. Returns a pointer past the last character written; if
/// the representation exceeds `n` characters, only the first `n` are written.
/// A negative `precision` defaults to 6, matching printf.
inline auto write_fixed(char* out, size_t n, double value,
                        int precision) noexcept -> char* {
  if (precision < 0) precision = 6;
  if (precision > 18)
    return detail::write_big(value, precision, out, n, format::fixed);
  if (n >= buffer_sizes<double>::fixed)
    return detail::write_fixed(value, precision, out);
  char buffer[buffer_sizes<double>::fixed];
  size_t size = detail::write_fixed(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

}  // namespace zmij

#endif  // ZMIJ_H_
