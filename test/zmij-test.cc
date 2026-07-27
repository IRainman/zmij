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
// Writes `value` with `precision` significant digits in scientific format.
static auto to_scientific(float value, int precision) -> std::string {
  char buffer[zmij::float_precision_buffer_size];
  return {buffer,
          zmij::write_scientific(buffer, sizeof(buffer), value, precision)};
}
static auto to_scientific(double value, int precision) -> std::string {
  char buffer[zmij::double_precision_buffer_size];
  return {buffer,
          zmij::write_scientific(buffer, sizeof(buffer), value, precision)};
}

// Writes `value` with up to `precision` significant digits in general format.
static auto to_general(float value, int precision) -> std::string {
  char buffer[zmij::float_precision_buffer_size];
  return {buffer, zmij::write_general(buffer, sizeof(buffer), value, precision)};
}
static auto to_general(double value, int precision) -> std::string {
  char buffer[zmij::double_precision_buffer_size];
  return {buffer, zmij::write_general(buffer, sizeof(buffer), value, precision)};
}

TEST(float_test, to_chars) {
  char buffer[zmij::float_buffer_size];
  auto result = zmij::to_chars(buffer, buffer + sizeof(buffer), 6.62607e-34f);
  EXPECT_EQ(result.ec, std::errc());
  EXPECT_EQ(std::string(buffer, result.ptr), "6.62607e-34");

  // Too small: nothing written, ptr == last, value_too_large.
  char small[3] = {'?', '?', '?'};
  result = zmij::to_chars(small, small + 2, 1.25f);
  EXPECT_EQ(result.ec, std::errc::value_too_large);
  EXPECT_EQ(result.ptr, small + 2);
  EXPECT_EQ(std::string(small, sizeof(small)), "???");
}

TEST(float_test, write_precision) {
  EXPECT_EQ(to_scientific(1.5f, 2), "1.5e+00");
  EXPECT_EQ(to_scientific(9.99f, 2), "1.0e+01");   // carry
  EXPECT_EQ(to_scientific(2.5f, 1), "2e+00");      // round half to even
  EXPECT_EQ(to_scientific(-1.5f, 2), "-1.5e+00");  // sign preserved
  EXPECT_EQ(to_scientific(std::numeric_limits<float>::denorm_min(), 1),
            "1e-45");  // subnormal path
  EXPECT_EQ(to_scientific(std::numeric_limits<float>::max(), 9),
            "3.40282347e+38");
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

  // Too small: nothing written, ptr == last, value_too_large.
  char small[3] = {'?', '?', '?'};
  result = zmij::to_chars(small, small + 2, 1.25);
  EXPECT_EQ(result.ec, std::errc::value_too_large);
  EXPECT_EQ(result.ptr, small + 2);
  EXPECT_EQ(std::string(small, sizeof(small)), "???");
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
  EXPECT_EQ(to_scientific(1.5, 2), "1.5e+00");
  EXPECT_EQ(to_scientific(1.0, 1), "1e+00");       // no point when precision 1
  EXPECT_EQ(to_scientific(0.0, 5), "0.0000e+00");  // zero
  EXPECT_EQ(to_scientific(std::numeric_limits<double>::infinity(), 3), "inf");

  // Overshoot: the integral part carries precision + 1 digits, so the extra
  // digit is dropped and the exponent bumped up.
  EXPECT_EQ(to_scientific(12.0, 2), "1.2e+01");
  EXPECT_EQ(to_scientific(123.0, 3), "1.23e+02");
  EXPECT_EQ(to_scientific(12345.678, 3), "1.23e+04");

  // Carry: rounding 9...9 up rolls into a new leading digit.
  EXPECT_EQ(to_scientific(9.99, 2), "1.0e+01");
  EXPECT_EQ(to_scientific(99.9, 2), "1.0e+02");

  // Round half-to-even.
  EXPECT_EQ(to_scientific(0.125, 2), "1.2e-01");  // 1.25 -> 1.2
  EXPECT_EQ(to_scientific(2.5, 1), "2e+00");      // -> 2 (even)
  EXPECT_EQ(to_scientific(3.5, 1), "4e+00");      // -> 4 (even)

  // Sign is carried through.
  EXPECT_EQ(to_scientific(-9.99, 2), "-1.0e+01");

  // Subnormals take a separate normalization path, so check both boundaries
  // (smallest and largest) at low and full precision.
  EXPECT_EQ(to_scientific(5e-324, 1), "5e-324");    // DBL_TRUE_MIN
  EXPECT_EQ(to_scientific(-5e-324, 1), "-5e-324");  // sign preserved
  // Smallest subnormal at full precision (exercises the widened table top).
  EXPECT_EQ(to_scientific(5e-324, 18), "4.94065645841246544e-324");
  // Largest subnormal, round-tripped at full precision.
  EXPECT_EQ(to_scientific(2.2250738585072009e-308, 17),
            "2.2250738585072009e-308");
  EXPECT_EQ(to_scientific(2.2250738585072009e-308, 6), "2.22507e-308");

  // Large values at low precision reach the low end of the table.
  EXPECT_EQ(to_scientific(1.7976931348623157e308, 1), "2e+308");  // DBL_MAX
  EXPECT_EQ(to_scientific(1.7976931348623157e308, 2), "1.8e+308");

  // Full-precision round trip.
  EXPECT_EQ(to_scientific(6.62607015e-34, 9), "6.62607015e-34");
}

TEST(double_test, write_precision_irregular) {
  for (uint64_t exp = 1; exp <= 2046; ++exp) {
    uint64_t bits = exp << 52;
    double value = 0;
    memcpy(&value, &bits, sizeof(double));
    for (int precision = 1; precision <= 18; ++precision) {
      char expected[32];
      snprintf(expected, sizeof(expected), "%.*e", precision - 1, value);
      EXPECT_EQ(to_scientific(value, precision), expected)
          << "value=" << value << " precision=" << precision;
    }
  }
}

TEST(float_test, write_general) {
  EXPECT_EQ(to_general(1.5f, 6), "1.5");
  EXPECT_EQ(to_general(0.0001f, 6), "0.0001");   // exp10 == -4 -> fixed
  EXPECT_EQ(to_general(0.00001f, 6), "1e-05");   // exp10 == -5 -> scientific
  EXPECT_EQ(to_general(-1.5f, 6), "-1.5");       // sign preserved
  EXPECT_EQ(to_general(std::numeric_limits<float>::denorm_min(), 1),
            "1e-45");  // subnormal path
}

TEST(double_test, write_general) {
  // Fixed range: decimal exponent in [-4, precision).
  EXPECT_EQ(to_general(1.5, 6), "1.5");
  EXPECT_EQ(to_general(100.0, 6), "100");
  EXPECT_EQ(to_general(123456.0, 6), "123456");
  EXPECT_EQ(to_general(0.0001, 6), "0.0001");         // exp10 == -4 -> fixed
  EXPECT_EQ(to_general(0.00001, 6), "1e-05");         // exp10 == -5 -> scientific
  EXPECT_EQ(to_general(1234567.0, 6), "1.23457e+06");  // exp10 == precision -> sci

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
