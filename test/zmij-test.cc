// Tests for https://github.com/vitaut/zmij/.
//
// Copyright (c) 2025 - present, Victor Zverovich
// Distributed under the MIT license (see LICENSE).

#ifndef ZMIJ_C
#  include "zmij.h"

#  include "zmij-to-chars.h"
#  define ZMIJ_C 0
#else
extern "C" {
#  include "zmij-c.h"
}

namespace zmij {
enum {
  float_buffer_size = zmij_float_buffer_size,
  double_buffer_size = zmij_double_buffer_size,
};

auto write(char* out, size_t n, double value) noexcept -> char* {
  return zmij_write_double(out, n, value);
}
auto write(char* out, size_t n, float value) noexcept -> char* {
  return zmij_write_float(out, n, value);
}
}  // namespace zmij
#endif

#include <gtest/gtest.h>
#include <stdint.h>  // uint64_t
#include <stdio.h>   // snprintf
#include <stdlib.h>  // atoi

#include <limits>  // std::numeric_limits
#include <string>  // std::string

#include "dragonbox/dragonbox_to_chars.h"
#include "fmt/format.h"

auto to_shortest(double value) -> std::string {
  char buffer[zmij::double_buffer_size + 1] = {};
  memset(buffer, '?', sizeof(buffer));
  auto end = zmij::write(buffer + 1, sizeof(buffer), value);
  if (buffer[0] != '?') throw std::runtime_error("buffer underrun");
  return {buffer + 1, end};
}

auto to_shortest(float value) -> std::string {
  char buffer[zmij::float_buffer_size] = {};
  auto end = zmij::write(buffer, sizeof(buffer), value);
  return {buffer, end};
}

TEST(float_test, normal) {
  EXPECT_EQ(to_shortest(6.62607e-34f), "6.62607e-34");
  EXPECT_EQ(to_shortest(1.342178e+08f), "1.342178e+08");
  EXPECT_EQ(to_shortest(1.3421781e+08f), "1.3421781e+08");
}

TEST(float_test, subnormal) {
  EXPECT_EQ(to_shortest(std::numeric_limits<float>::denorm_min()), "1e-45");
}

TEST(float_test, no_overrun) {
  char buffer[zmij::float_buffer_size + 1];
  memset(buffer, '?', sizeof(buffer));
  auto end = zmij::write(buffer, zmij::float_buffer_size, -1.00000005e+15f);
  EXPECT_EQ(std::string(buffer, end), std::string("-1.00000005e+15"));
  EXPECT_EQ(buffer[zmij::float_buffer_size], '?');
}

TEST(float_test, no_buffer) {
  float value = 6.62607e-34;
  char buffer[zmij::float_buffer_size];
  auto end = zmij::write(buffer, sizeof(buffer), value);
  std::string result(buffer, end);
  EXPECT_EQ(result, "6.62607e-34");
}

TEST(float_test, fixed_with_zeros) {
  EXPECT_EQ(to_shortest(43210.0f), "43210");
  EXPECT_EQ(to_shortest(43210.1f), "43210.1");
  EXPECT_EQ(to_shortest(10000.f), "10000");
}

#if !ZMIJ_C
// Writes `value` with `precision` digits after the point in scientific format.
static auto to_scientific(float value, int precision) -> std::string {
  char buffer[zmij::buffer_sizes<float>::scientific];
  return {buffer,
          zmij::write_scientific(buffer, sizeof(buffer), value, precision)};
}
static auto to_scientific(double value, int precision) -> std::string {
  char buffer[zmij::buffer_sizes<double>::scientific];
  return {buffer,
          zmij::write_scientific(buffer, sizeof(buffer), value, precision)};
}

// Writes `value` with up to `precision` significant digits in general format.
static auto to_general(float value, int precision) -> std::string {
  char buffer[zmij::buffer_sizes<float>::scientific];
  return {buffer,
          zmij::write_general(buffer, sizeof(buffer), value, precision)};
}
static auto to_general(double value, int precision) -> std::string {
  char buffer[zmij::buffer_sizes<double>::scientific];
  return {buffer,
          zmij::write_general(buffer, sizeof(buffer), value, precision)};
}

TEST(float_test, to_chars) {
  char buffer[zmij::float_buffer_size];
  auto result = zmij::to_chars(buffer, buffer + sizeof(buffer), 6.62607e-34f);
  EXPECT_EQ(result.ec, std::errc());
  EXPECT_EQ(std::string(buffer, result.ptr), "6.62607e-34");

  // Too small: truncated output, ptr == last, value_too_large.
  char small[3] = {'?', '?', '?'};
  result = zmij::to_chars(small, small + 2, 1.25f);
  EXPECT_EQ(result.ec, std::errc::value_too_large);
  EXPECT_EQ(result.ptr, small + 2);
  EXPECT_EQ(std::string(small, sizeof(small)), "1.?");
}

TEST(float_test, to_chars_format) {
  char buffer[zmij::buffer_sizes<float>::fixed];
  auto result = zmij::to_chars(buffer, buffer + sizeof(buffer), 1.5f,
                               zmij::chars_format::scientific, 2);
  EXPECT_EQ(result.ec, std::errc());
  EXPECT_EQ(std::string(buffer, result.ptr), "1.50e+00");

  // Precision out of range: nothing written, ptr == first, invalid_argument.
  // Scientific caps at 17 fractional digits (18 significant).
  char small[4] = {'?', '?', '?', '?'};
  result = zmij::to_chars(small, small + sizeof(small), 1.5f,
                          zmij::chars_format::scientific, 18);
  EXPECT_EQ(result.ec, std::errc::invalid_argument);
  EXPECT_EQ(result.ptr, small);
  EXPECT_EQ(std::string(small, sizeof(small)), "????");
}

TEST(float_test, write_precision) {
  EXPECT_EQ(to_scientific(1.5f, 1), "1.5e+00");
  EXPECT_EQ(to_scientific(9.99f, 1), "1.0e+01");   // carry
  EXPECT_EQ(to_scientific(2.5f, 0), "2e+00");      // round half to even
  EXPECT_EQ(to_scientific(-1.5f, 1), "-1.5e+00");  // sign preserved
  EXPECT_EQ(to_scientific(std::numeric_limits<float>::denorm_min(), 0),
            "1e-45");  // subnormal path
  EXPECT_EQ(to_scientific(std::numeric_limits<float>::max(), 8),
            "3.40282347e+38");
}

// Big precision (> 18) routes write_scientific, write_general, and write_fixed
// through write_big; all must match printf's %e, %g, and %f.
TEST(float_test, write_big) {
  auto check = [](float value, int precision) {
    char buf[200], ref[200];
    char* end = zmij::write_scientific(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*e", precision, double(value));
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "scientific value=" << value << " precision=" << precision;
    end = zmij::write_general(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*g", precision, double(value));
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "general value=" << value << " precision=" << precision;
    end = zmij::write_fixed(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*f", precision, double(value));
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "fixed value=" << value << " precision=" << precision;
  };
  const float values[] = {1.0f, 0.1f, 1.5f, 3.14159f, 3.4028235e38f, 1.4e-45f};
  for (float value : values) {
    for (int precision : {19, 20, 30, 50, 100}) check(value, precision);
  }
}
#endif  // !ZMIJ_C

TEST(double_test, normal) {
  EXPECT_EQ(to_shortest(6.62607015e-34), "6.62607015e-34");

  // Exact half-ulp tie when rounding to nearest integer.
  EXPECT_EQ(to_shortest(5.444310685350916e+14), "544431068535091.6");
}

TEST(double_test, subnormal) {
  EXPECT_EQ(to_shortest(std::numeric_limits<double>::denorm_min()), "5e-324");
  EXPECT_EQ(to_shortest(1e-323), "1e-323");
  EXPECT_EQ(to_shortest(1.2e-322), "1.2e-322");
  EXPECT_EQ(to_shortest(1.5e-323), "1.5e-323");
  EXPECT_EQ(to_shortest(1.24e-322), "1.24e-322");
  EXPECT_EQ(to_shortest(1.234e-320), "1.234e-320");
  EXPECT_EQ(to_shortest(2.2250738585072004e-308), "2.2250738585072004e-308");
}

TEST(double_test, irregular) {
  const char* fixed[] = {"0.0001220703125",
                         "0.000244140625",
                         "0.00048828125",
                         "0.0009765625",
                         "0.001953125",
                         "0.00390625",
                         "0.0078125",
                         "0.015625",
                         "0.03125",
                         "0.0625",
                         "0.125",
                         "0.25",
                         "0.5"};
  for (uint64_t exp = 1; exp < 0x3ff; ++exp) {
    uint64_t bits = exp << 52;
    double value = 0;
    memcpy(&value, &bits, sizeof(double));

    int fixed_start = 1010, fixed_end = 1022;
    if (exp >= fixed_start && exp <= fixed_end) {
      EXPECT_EQ(to_shortest(value), fixed[exp - fixed_start]);
      continue;
    }

    char expected[32] = {};
    *jkj::dragonbox::to_chars(value, expected) = '\0';

    EXPECT_EQ(to_shortest(value), expected) << exp;
  }
}

TEST(double_test, exponents) {
  const char* fixed[] = {"0.00012207031250000003", "0.00024414062500000005",
                         "0.0004882812500000001",  "0.0009765625000000002",
                         "0.0019531250000000004",  "0.003906250000000001",
                         "0.007812500000000002",   "0.015625000000000003",
                         "0.03125000000000001",    "0.06250000000000001",
                         "0.12500000000000003",    "0.25000000000000006",
                         "0.5000000000000001",     "1.0000000000000002"};
  for (uint64_t exp = 0; exp <= 0x3ff; ++exp) {
    uint64_t bits = (exp << 52) | 1;
    double value = 0;
    memcpy(&value, &bits, sizeof(double));

    int fixed_start = 1010, fixed_end = 1023;
    if (exp >= fixed_start && exp <= fixed_end) {
      EXPECT_EQ(to_shortest(value), fixed[exp - fixed_start]);
      continue;
    }

    char expected[32] = {};
    *jkj::dragonbox::to_chars(value, expected) = '\0';

    EXPECT_EQ(to_shortest(value), expected) << exp;
  }
}

TEST(double_test, small_int) { EXPECT_EQ(to_shortest(1.0), "1"); }

TEST(double_test, zero) {
  EXPECT_EQ(to_shortest(0.0), "0");
  EXPECT_EQ(to_shortest(-0.0), "-0");
}

TEST(double_test, inf) {
  EXPECT_EQ(to_shortest(std::numeric_limits<double>::infinity()), "inf");
}

TEST(double_test, nan) {
  EXPECT_EQ(to_shortest(-std::numeric_limits<double>::quiet_NaN()), "-nan");
}

TEST(double_test, shorter) {
  // A possibly shorter underestimate is picked (u' in Schubfach).
  EXPECT_EQ(to_shortest(-4.932096661796888e-226), "-4.932096661796888e-226");

  // A possibly shorter overestimate is picked (w' in Schubfach).
  EXPECT_EQ(to_shortest(3.439070283483335e+35), "3.439070283483335e+35");
}

TEST(double_test, single_candidate) {
  // Only an underestimate is in the rounding region (u in Schubfach).
  EXPECT_EQ(to_shortest(6.606854224493745e-17), "6.606854224493745e-17");

  // Only an overestimate is in the rounding region (w in Schubfach).
  EXPECT_EQ(to_shortest(6.079537928711555e+61), "6.079537928711555e+61");
}

// Rounding-boundary doubles enumerated by verify.py (see --dump-boundaries).
// boundary-bits.h is a bare initializer list, one bit pattern per line.
static const uint64_t boundary_bits[] = {
#include "boundary-bits.h"
};

// Check zmij against dragonbox on every rounding-boundary double verify.py
// enumerates, using dragonbox's to_decimal as an independent oracle.
TEST(double_test, boundaries) {
  auto to_string = [](uint64_t sig, int dec_exp) -> std::string {
    std::string digits = std::to_string(sig);
    int num_digits = int(digits.size());
    dec_exp += num_digits - 1;           // exponent of the leading digit
    if (dec_exp < -4 || dec_exp > 15) {  // scientific
      std::string sig_str = num_digits == 1
                                ? digits
                                : digits.substr(0, 1) + "." + digits.substr(1);
      return sig_str + fmt::format("e{:+03d}", dec_exp);
    }
    int point = dec_exp + 1;  // digits left of the decimal point
    if (point <= 0) return "0." + std::string(-point, '0') + digits;
    if (point >= num_digits)
      return digits + std::string(point - num_digits, '0');
    return digits.substr(0, point) + "." + digits.substr(point);
  };

  for (uint64_t bits : boundary_bits) {
    double value = 0;
    memcpy(&value, &bits, sizeof(value));
    auto ref = jkj::dragonbox::to_decimal(value);
    EXPECT_EQ(to_shortest(value), to_string(ref.significand, ref.exponent))
        << "bits=" << bits;
  }
}

TEST(double_test, fixed_with_zeros) {
  EXPECT_EQ(to_shortest(43210.0), "43210");
  EXPECT_EQ(to_shortest(43210.1), "43210.1");
  EXPECT_EQ(to_shortest(10000.0), "10000");
  EXPECT_EQ(to_shortest(-5942736479622170.0), "-5942736479622170");
}

TEST(double_test, no_overrun) {
  char buffer[zmij::double_buffer_size + 1];
  memset(buffer, '?', sizeof(buffer));
  auto end =
      zmij::write(buffer, zmij::double_buffer_size, -1.2345678901234567e+123);
  EXPECT_EQ(std::string(buffer, end), std::string("-1.2345678901234567e+123"));
  EXPECT_EQ(buffer[zmij::double_buffer_size], '?');
}

TEST(double_test, no_underrun) { to_shortest(9.061488e+15); }

TEST(double_test, no_buffer) {
  double value = 6.62607015e-34;
  char buffer[zmij::double_buffer_size];
  auto end = zmij::write(buffer, sizeof(buffer), value);
  std::string result(buffer, end);
  EXPECT_EQ(result, "6.62607015e-34");
}

#if !ZMIJ_C
TEST(double_test, to_chars) {
  char buffer[zmij::double_buffer_size];
  auto result = zmij::to_chars(buffer, buffer + sizeof(buffer), 6.62607015e-34);
  EXPECT_EQ(result.ec, std::errc());
  EXPECT_EQ(std::string(buffer, result.ptr), "6.62607015e-34");

  // Exact fit succeeds ("1.25" is 4 characters).
  result = zmij::to_chars(buffer, buffer + 4, 1.25);
  EXPECT_EQ(result.ec, std::errc());
  EXPECT_EQ(std::string(buffer, result.ptr), "1.25");

  // Too small: truncated output, ptr == last, value_too_large.
  char small[3] = {'?', '?', '?'};
  result = zmij::to_chars(small, small + 2, 1.25);
  EXPECT_EQ(result.ec, std::errc::value_too_large);
  EXPECT_EQ(result.ptr, small + 2);
  EXPECT_EQ(std::string(small, sizeof(small)), "1.?");
}

TEST(double_test, to_chars_format) {
  char buffer[zmij::buffer_sizes<double>::fixed];
  auto fmt = [&](zmij::chars_format f, int precision, double value) {
    auto r =
        zmij::to_chars(buffer, buffer + sizeof(buffer), value, f, precision);
    EXPECT_EQ(r.ec, std::errc());
    return std::string(buffer, r.ptr);
  };
  EXPECT_EQ(fmt(zmij::chars_format::fixed, 2, 1.5), "1.50");
  EXPECT_EQ(fmt(zmij::chars_format::fixed, 0, 2.5), "2");  // ties to even
  EXPECT_EQ(fmt(zmij::chars_format::scientific, 4, 1234.5678), "1.2346e+03");
  EXPECT_EQ(fmt(zmij::chars_format::scientific, 0, 2.5), "2e+00");
  EXPECT_EQ(fmt(zmij::chars_format::general, 6, 1234.5678), "1234.57");

  // Precision out of range: nothing written, ptr == first, invalid_argument.
  // Scientific caps at 17 fractional digits (18 significant).
  char small[8];
  memset(small, '?', sizeof(small));
  auto result = zmij::to_chars(small, small + sizeof(small), 1.5,
                               zmij::chars_format::scientific, 18);
  EXPECT_EQ(result.ec, std::errc::invalid_argument);
  EXPECT_EQ(result.ptr, small);
  result = zmij::to_chars(small, small + sizeof(small), 1.5,
                          zmij::chars_format::fixed, 19);
  EXPECT_EQ(result.ec, std::errc::invalid_argument);
  EXPECT_EQ(std::string(small, sizeof(small)), "????????");

  // Output too small: truncated result, ptr == last, value_too_large.
  result =
      zmij::to_chars(small, small + 3, 1234.5678, zmij::chars_format::fixed, 2);
  EXPECT_EQ(result.ec, std::errc::value_too_large);
  EXPECT_EQ(result.ptr, small + 3);
  EXPECT_EQ(std::string(small, 3), "123");  // "1234.57" truncated to 3 chars
}

TEST(double_test, to_decimal) {
  zmij::dec_fp dec = zmij::to_decimal(6.62607015e-34);
  EXPECT_EQ(dec.sig, 66260701500000000);
  EXPECT_EQ(dec.exp, -50);
  EXPECT_EQ(dec.negative, false);

  dec = zmij::to_decimal(-6.62607015e-34);
  EXPECT_EQ(dec.sig, 66260701500000000);
  EXPECT_EQ(dec.exp, -50);
  EXPECT_EQ(dec.negative, true);

  dec = zmij::to_decimal(-0.0);
  EXPECT_EQ(dec.sig, 0);
  EXPECT_EQ(dec.exp, 0);
  EXPECT_EQ(dec.negative, true);

  uint32_t garlic = 0;
  memcpy(&garlic, "🧄", 4);
  uint64_t bits = 0x7FF0000000000000 | garlic;
  double garlic_nan = 0;
  memcpy(&garlic_nan, &bits, sizeof(bits));
  dec = zmij::to_decimal(garlic_nan);
  EXPECT_EQ(dec.sig, garlic);
}

TEST(double_test, write_precision) {
  EXPECT_EQ(to_scientific(1.5, 1), "1.5e+00");
  EXPECT_EQ(to_scientific(1.0, 0), "1e+00");       // no point when precision 0
  EXPECT_EQ(to_scientific(0.0, 4), "0.0000e+00");  // zero
  EXPECT_EQ(to_scientific(std::numeric_limits<double>::infinity(), 2), "inf");

  // Overshoot: values >= 10 still normalize to a single leading digit.
  EXPECT_EQ(to_scientific(12.0, 1), "1.2e+01");
  EXPECT_EQ(to_scientific(123.0, 2), "1.23e+02");
  EXPECT_EQ(to_scientific(12345.678, 2), "1.23e+04");

  // Carry: rounding 9...9 up rolls into a new leading digit.
  EXPECT_EQ(to_scientific(9.99, 1), "1.0e+01");
  EXPECT_EQ(to_scientific(99.9, 1), "1.0e+02");

  // Round half-to-even.
  EXPECT_EQ(to_scientific(0.125, 1), "1.2e-01");  // 1.25 -> 1.2
  EXPECT_EQ(to_scientific(2.5, 0), "2e+00");      // -> 2 (even)
  EXPECT_EQ(to_scientific(3.5, 0), "4e+00");      // -> 4 (even)

  // Sign is carried through.
  EXPECT_EQ(to_scientific(-9.99, 1), "-1.0e+01");

  // Subnormals take a separate normalization path, so check both boundaries
  // (smallest and largest) at low and full precision.
  EXPECT_EQ(to_scientific(5e-324, 0), "5e-324");    // DBL_TRUE_MIN
  EXPECT_EQ(to_scientific(-5e-324, 0), "-5e-324");  // sign preserved
  // Smallest subnormal at full precision (exercises the widened table top).
  EXPECT_EQ(to_scientific(5e-324, 17), "4.94065645841246544e-324");
  // Largest subnormal, round-tripped at full precision.
  EXPECT_EQ(to_scientific(2.2250738585072009e-308, 16),
            "2.2250738585072009e-308");
  EXPECT_EQ(to_scientific(2.2250738585072009e-308, 5), "2.22507e-308");

  // Large values at low precision reach the low end of the table.
  EXPECT_EQ(to_scientific(1.7976931348623157e308, 0), "2e+308");  // DBL_MAX
  EXPECT_EQ(to_scientific(1.7976931348623157e308, 1), "1.8e+308");

  // Full-precision round trip.
  EXPECT_EQ(to_scientific(6.62607015e-34, 8), "6.62607015e-34");
}

TEST(double_test, negative_precision) {
  // Pass the same negative/zero precision to printf, which defaults it to 6
  // (and treats 0 as 1 for %g), and check we produce identical output.
  double value = 1234.5678;
  char buf[64], ref[64];
  char* end = zmij::write_scientific(buf, sizeof(buf), value, -1);
  snprintf(ref, sizeof(ref), "%.*e", -1, value);
  EXPECT_EQ(std::string(buf, end), ref);
  end = zmij::write_fixed(buf, sizeof(buf), value, -5);
  snprintf(ref, sizeof(ref), "%.*f", -5, value);
  EXPECT_EQ(std::string(buf, end), ref);
  end = zmij::write_general(buf, sizeof(buf), value, -1);
  snprintf(ref, sizeof(ref), "%.*g", -1, value);
  EXPECT_EQ(std::string(buf, end), ref);
  end = zmij::write_general(buf, sizeof(buf), value, 0);
  snprintf(ref, sizeof(ref), "%.*g", 0, value);
  EXPECT_EQ(std::string(buf, end), ref);
}

TEST(double_test, write_precision_irregular) {
  for (uint64_t exp = 1; exp <= 2046; ++exp) {
    uint64_t bits = exp << 52;
    double value = 0;
    memcpy(&value, &bits, sizeof(double));
    for (int precision = 0; precision <= 18; ++precision) {
      char expected[32];
      snprintf(expected, sizeof(expected), "%.*e", precision, value);
      EXPECT_EQ(to_scientific(value, precision), expected)
          << "value=" << value << " precision=" << precision;
    }
  }
}

// Big precision (> 18) routes write_scientific, write_general, and write_fixed
// through write_big; all must match printf's %e, %g, and %f.
TEST(double_test, write_big) {
  auto check = [](double value, int precision) {
    char buf[1200], ref[1200];
    char* end = zmij::write_scientific(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*e", precision, value);
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "scientific value=" << value << " precision=" << precision;
    end = zmij::write_general(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*g", precision, value);
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "general value=" << value << " precision=" << precision;
    end = zmij::write_fixed(buf, sizeof(buf), value, precision);
    snprintf(ref, sizeof(ref), "%.*f", precision, value);
    EXPECT_EQ(std::string(buf, end), std::string(ref))
        << "fixed value=" << value << " precision=" << precision;
  };
  const double values[] = {1.0,
                           2.0,
                           0.1,
                           0.5,
                           1.5,
                           1.25,
                           3.141592653589793,
                           1234.5678,
                           1e300,
                           1e-300,
                           9.999999999999999e22,
                           1.7976931348623157e308,   // DBL_MAX
                           2.2250738585072014e-308,  // smallest normal
                           5e-324};                  // smallest subnormal
  for (double value : values) {
    for (int precision : {19, 20, 25, 30, 40, 60, 100, 300, 767, 800}) {
      check(value, precision);
      check(-value, precision);
    }
  }
}

// An undersized buffer truncates the big-precision result without overrunning.
TEST(double_test, write_big_truncated) {
  char buf[8];
  memset(buf, '?', sizeof(buf));
  char* end = zmij::write_scientific(buf, 5, 1.5, 30);
  EXPECT_EQ(std::string(buf, end), "1.500");  // first 5 of 1.500...e+00
  EXPECT_EQ(end, buf + 5);
  EXPECT_EQ(buf[5], '?');  // no overrun past the requested size

  memset(buf, '?', sizeof(buf));
  end = zmij::write_general(buf, 5, 0.1, 30);
  EXPECT_EQ(std::string(buf, end), "0.100");  // first 5 of 0.10000...
  EXPECT_EQ(end, buf + 5);
  EXPECT_EQ(buf[5], '?');

  memset(buf, '?', sizeof(buf));
  end = zmij::write_fixed(buf, 5, 1.5, 30);
  EXPECT_EQ(std::string(buf, end), "1.500");  // first 5 of 1.5000...
  EXPECT_EQ(end, buf + 5);
  EXPECT_EQ(buf[5], '?');
}

// write_big with zero fractional digits must not emit a trailing decimal point,
// including on carry (e.g. 9.5 -> 1e+01). This path is only reachable directly,
// since the public API routes low precision through the shortest writers.
TEST(double_test, write_big_no_point) {
  char buf[32], ref[32];
  for (double value : {1.0, 2.5, 9.5, 12.5, 0.5, 1e300, 5e-324}) {
    for (int precision : {0, 1, 2}) {
      char* end = zmij::detail::write_big(value, precision, buf, sizeof(buf),
                                          zmij::format::scientific);
      snprintf(ref, sizeof(ref), "%.*e", precision, value);
      EXPECT_EQ(std::string(buf, end), std::string(ref))
          << "value=" << value << " precision=" << precision;
    }
  }
}

TEST(long_double_test, write_scientific) {
  char buf[80], ref[80];
  for (long double value : {1.5L, 0.0L, 1e300L, 5e-324L}) {
    for (int precision : {-1, 0, 6, 20}) {
      char* end = zmij::write_scientific(buf, sizeof(buf), value, precision);
      snprintf(ref, sizeof(ref), "%.*Le", precision < 0 ? 6 : precision, value);
      EXPECT_EQ(std::string(buf, end), std::string(ref))
          << "value=" << double(value) << " precision=" << precision;
    }
  }
}

TEST(float_test, write_general) {
  EXPECT_EQ(to_general(1.5f, 6), "1.5");
  EXPECT_EQ(to_general(0.0001f, 6), "0.0001");  // exp10 == -4 -> fixed
  EXPECT_EQ(to_general(0.00001f, 6), "1e-05");  // exp10 == -5 -> scientific
  EXPECT_EQ(to_general(-1.5f, 6), "-1.5");      // sign preserved
  EXPECT_EQ(to_general(std::numeric_limits<float>::denorm_min(), 1),
            "1e-45");  // subnormal path
}

TEST(double_test, write_general) {
  // Fixed range: decimal exponent in [-4, precision).
  EXPECT_EQ(to_general(1.5, 6), "1.5");
  EXPECT_EQ(to_general(100.0, 6), "100");
  EXPECT_EQ(to_general(123456.0, 6), "123456");
  EXPECT_EQ(to_general(0.0001, 6), "0.0001");  // exp10 == -4 -> fixed
  EXPECT_EQ(to_general(0.00001, 6), "1e-05");  // exp10 == -5 -> scientific
  EXPECT_EQ(to_general(1234567.0, 6),
            "1.23457e+06");  // exp10 == precision -> sci

  // Trailing zeros are trimmed, and the point with them.
  EXPECT_EQ(to_general(1.2000, 6), "1.2");
  EXPECT_EQ(to_general(1.0, 6), "1");
  EXPECT_EQ(to_general(1024.0, 6), "1024");

  // Zero and sign.
  EXPECT_EQ(to_general(0.0, 6), "0");
  EXPECT_EQ(to_general(-0.0, 6), "-0");
  EXPECT_EQ(to_general(-1.5, 6), "-1.5");

  // Rounding rolls into a new leading digit and bumps the format to scientific.
  EXPECT_EQ(to_general(999999.0, 5), "1e+06");

  // Specials.
  EXPECT_EQ(to_general(std::numeric_limits<double>::infinity(), 6), "inf");

  // Full-precision round trips.
  EXPECT_EQ(to_general(6.62607015e-34, 9), "6.62607015e-34");
  EXPECT_EQ(to_general(3.14159265358979, 15), "3.14159265358979");
}

TEST(double_test, write_general_irregular) {
  for (uint64_t exp = 1; exp <= 2046; ++exp) {
    uint64_t bits = exp << 52;
    double value = 0;
    memcpy(&value, &bits, sizeof(double));
    for (int precision = 1; precision <= 18; ++precision) {
      char expected[32];
      snprintf(expected, sizeof(expected), "%.*g", precision, value);
      EXPECT_EQ(to_general(value, precision), expected)
          << "value=" << value << " precision=" << precision;
    }
  }
}

#endif  // !ZMIJ_C

auto main(int argc, char** argv) -> int {
  testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
