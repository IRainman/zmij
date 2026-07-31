// A double-to-string conversion library: https://github.com/vitaut/zmij/
//
// Copyright (c) 2025 - present, Victor Zverovich
// Distributed under the MIT license (see LICENSE) or alternatively
// the Boost Software License, Version 1.0.

#ifndef ZMIJ_H_
#define ZMIJ_H_

#include <stddef.h>  // size_t
#include <string.h>  // memcpy

namespace zmij {
namespace detail {

template <typename Float>
auto write(Float value, char* buffer) noexcept -> char*;

template <typename Float>
auto write_scientific(Float value, int precision, char* buffer) noexcept
    -> char*;

template <typename Float>
auto write_scientific_big(Float value, int precision, char* out,
                          size_t n) noexcept -> char*;

template <typename Float>
auto write_general(Float value, int precision, char* buffer) noexcept -> char*;

template <typename Float>
auto write_fixed(Float value, int precision, char* buffer) noexcept -> char*;

/// Clamps `precision` to the supported range [1, 18].
inline auto clamp_precision(int precision) noexcept -> int {
  if (precision < 1) return 1;
  if (precision > 18) return 18;
  return precision;
}

/// Clamps `precision` to the range [0, 18] supported by write_fixed.
inline auto clamp_fixed_precision(int precision) noexcept -> int {
  if (precision < 0) return 0;
  if (precision > 18) return 18;
  return precision;
}

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

/// Writes `value` in scientific format with exactly `precision` significant
/// digits (e.g. 1.234e+05) to `out` without a null terminator. Returns a
/// pointer past the last character written; if the representation exceeds `n`
/// characters, only the first `n` are written. `precision` must be at least 1;
/// values below 1 are clamped to 1.
inline auto write_scientific(char* out, size_t n, float value,
                             int precision) noexcept -> char* {
  if (precision < 1) precision = 1;
  if (precision > 18)
    return detail::write_scientific_big(value, precision, out, n);
  if (n >= buffer_sizes<float>::scientific)
    return detail::write_scientific(value, precision, out);
  char buffer[buffer_sizes<float>::scientific];
  size_t size = detail::write_scientific(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with exactly `precision` significant
/// digits (e.g. 1.234e+05) to `out` without a null terminator. Returns a
/// pointer past the last character written; if the representation exceeds `n`
/// characters, only the first `n` are written. `precision` must be at least 1;
/// values below 1 are clamped to 1.
inline auto write_scientific(char* out, size_t n, double value,
                             int precision) noexcept -> char* {
  if (precision < 1) precision = 1;
  if (precision > 18)
    return detail::write_scientific_big(value, precision, out, n);
  if (n >= buffer_sizes<double>::scientific)
    return detail::write_scientific(value, precision, out);
  char buffer[buffer_sizes<double>::scientific];
  size_t size = detail::write_scientific(value, precision, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in general format with up to `precision` significant digits
/// and no trailing zeros (e.g. 1.5 or 1.5e+20) to `out` without a null
/// terminator. Fixed notation is used when `value`'s decimal exponent is in
/// [-4, precision), and scientific otherwise. Returns a pointer past the last
/// character written; if the representation exceeds `n` characters, only the
/// first `n` are written. `precision` must be in [1, 18]; out-of-range values
/// are clamped.
inline auto write_general(char* out, size_t n, float value,
                          int precision) noexcept -> char* {
  precision = detail::clamp_precision(precision);
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
/// first `n` are written. `precision` must be in [1, 18]; out-of-range values
/// are clamped.
inline auto write_general(char* out, size_t n, double value,
                          int precision) noexcept -> char* {
  precision = detail::clamp_precision(precision);
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
/// matching printf's %f for every finite input. Returns a pointer past the last
/// character written; if the representation exceeds `n` characters, only the
/// first `n` are written. `precision` must be in [0, 18]; out-of-range values
/// are clamped.
inline auto write_fixed(char* out, size_t n, float value,
                        int precision) noexcept -> char* {
  precision = detail::clamp_fixed_precision(precision);
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
/// matching printf's %f for every finite input. Returns a pointer past the last
/// character written; if the representation exceeds `n` characters, only the
/// first `n` are written. `precision` must be in [0, 18]; out-of-range values
/// are clamped.
inline auto write_fixed(char* out, size_t n, double value,
                        int precision) noexcept -> char* {
  precision = detail::clamp_fixed_precision(precision);
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
