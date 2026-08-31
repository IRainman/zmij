// A double-to-string conversion library: https://github.com/vitaut/zmij/
//
// Copyright (c) 2025 - present, Victor Zverovich
// Distributed under the MIT license (see LICENSE) or alternatively
// the Boost Software License, Version 1.0.

#ifndef ZMIJ_C_H_
#define ZMIJ_C_H_

#include <stddef.h>  // size_t
#include <string.h>  // memcpy

// Implementation details, use zmij_write_* instead.
char* zmij_detail_write_float(float value, char* buffer);
char* zmij_detail_write_double(double value, char* buffer);
char* zmij_detail_write_scientific_float(float value, char* buffer,
                                         int num_digits);
char* zmij_detail_write_scientific_double(double value, char* buffer,
                                          int num_digits);
size_t zmij_detail_write_scientific_big(char* out, size_t n, double value,
                                        int precision);

enum {
  // Minimum buffer sizes for the shortest zmij_write_*.
  zmij_float_buffer_size = 17,
  zmij_double_buffer_size = 34,
  // Buffer sizes that always suffice for zmij_write_scientific_* with
  // precision up to 17; higher precision needs `precision + 8` bytes.
  zmij_float_scientific_buffer_size = 24,
  zmij_double_scientific_buffer_size = 25,
};

/// Writes the shortest correctly rounded decimal representation of `value` to
/// `out` without a null terminator. Returns a pointer past the last character
/// written; if the representation exceeds `n` characters, only the first `n`
/// are written.
static inline char* zmij_write_float(char* out, size_t n, float value) {
  if (n >= zmij_float_buffer_size) return zmij_detail_write_float(value, out);
  char buffer[zmij_float_buffer_size];
  size_t size = zmij_detail_write_float(value, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes the shortest correctly rounded decimal representation of `value` to
/// `out` without a null terminator. Returns a pointer past the last character
/// written; if the representation exceeds `n` characters, only the first `n`
/// are written.
static inline char* zmij_write_double(char* out, size_t n, double value) {
  if (n >= zmij_double_buffer_size) return zmij_detail_write_double(value, out);
  char buffer[zmij_double_buffer_size];
  size_t size = zmij_detail_write_double(value, buffer) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with `precision` digits after the
/// decimal point (e.g. 1.234e+05) to `out`, without a null terminator, like
/// printf's %e. A negative `precision` defaults to 6.
///
/// Returns a pointer past the last character written; if the representation
/// exceeds `n` characters, only the first `n` are written.
static inline char* zmij_write_scientific_float(char* out, size_t n,
                                                float value, int precision) {
  if (precision < 0) precision = 6;
  if (precision >= 18) {
    // A float is exact as a double, so both produce the same digits.
    size_t size =
        zmij_detail_write_scientific_big(out, n, (double)value, precision);
    return out + (size < n ? size : n);
  }
  if (n >= zmij_float_scientific_buffer_size)
    return zmij_detail_write_scientific_float(value, out, precision + 1);
  char buffer[zmij_float_scientific_buffer_size];
  size_t size =
      zmij_detail_write_scientific_float(value, buffer, precision + 1) - buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

/// Writes `value` in scientific format with `precision` digits after the
/// decimal point (e.g. 1.234e+05) to `out`, without a null terminator, like
/// printf's %e. A negative `precision` defaults to 6.
///
/// Returns a pointer past the last character written; if the representation
/// exceeds `n` characters, only the first `n` are written.
static inline char* zmij_write_scientific_double(char* out, size_t n,
                                                 double value, int precision) {
  if (precision < 0) precision = 6;
  if (precision >= 18) {
    size_t size = zmij_detail_write_scientific_big(out, n, value, precision);
    return out + (size < n ? size : n);
  }
  if (n >= zmij_double_scientific_buffer_size)
    return zmij_detail_write_scientific_double(value, out, precision + 1);
  char buffer[zmij_double_scientific_buffer_size];
  size_t size =
      zmij_detail_write_scientific_double(value, buffer, precision + 1) -
      buffer;
  if (size > n) size = n;
  memcpy(out, buffer, size);
  return out + size;
}

#endif  // ZMIJ_C_H_
