#!/usr/bin/env python3
"""
A script to verify the correctness of the Żmij FP-to-string conversion for
the extended-precision long double formats: x87 80-bit and IEEE binary128.

Copyright (c) 2025 - present, Victor Zverovich
Portions Copyright (c) 2020 YaoYuan
Distributed under the MIT license.
https://github.com/vitaut/zmij/

Companion to verify.py (double), reusing its floor_sum machinery. Żmij's
long-double path adapts YaoYuan's (yy) method, the same code for both formats.

Overview
--------

Żmij converts v = bin_sig * 2**bin_exp (a p-bit significand, p = 64 for x87,
113 for binary128) to the shortest decimal dec_sig * 10**dec_exp. Following
Schubfach it scales by a power of ten:

    dec_sig = v * 10**(-dec_exp),   dec_exp = floor(bin_exp * log10(2)),

using a precomputed constant pow10 * 2**pow10_exp ~= 10**(-dec_exp), where
pow10 is a normalized POW10_BITS-bit integer (top bit set). With
shift = -(bin_exp + pow10_exp) the scaling is a single multiply and shift:

    v * 10**(-dec_exp) = (bin_sig * pow10) * 2**(bin_exp + pow10_exp)
                       = (bin_sig * pow10) >> shift

The product is kept to 256 bits: a 128-bit integral part and a 128-bit
fraction (`integral` and `fractional` in to_decimal),

    scaled     = (bin_sig * pow10) >> (shift - 128)
    integral   = scaled >> 128        # floor(v * 10**(-dec_exp))
    fractional = scaled mod 2**128    # the bits past the decimal point

Long multiply, most significant bit on the left:

    ------------------------------------------------------------
                     |HHHHHHHHHHHHHHHH|LLLLLLLLLLLLLLLL|........  pow10
                     |        XXXXXXXX|                           bin_sig
    ------------------------------------------------------------
    |   XHXHXHXHXHXHX|HXHXHXHXHXHXHXHX|                           H * bin_sig
                     |   XLXLXLXLXLXLX|LXLXLXLXLXLXLXLX|          L * bin_sig
                                      |   .............|........  tail * bin_sig
    ------------------------------------------------------------
    |    integral    |   fractional   |....dropped.....|

H is the high 128 bits of pow10 and L the next 128; the low tail beyond
POW10_BITS is dropped. The decimal point sits between integral and fractional.

pow10 is only POW10_BITS bits (256), so it, and hence the product, is rounded
down; every bit below the kept fraction is truncated. The retained value is
therefore slightly low, and a carry out of the discarded tail could nudge it up
across a rounding boundary - the critical boundary conditions to check.

Shortening `integral` to the shortest decimal makes three rounding decisions,
each a threshold test on the truncated value that the error could flip:

1. Round to nearest, deciding the last kept digit. The tie is
   fractional == 2**127 (exactly one half), broken to even.
2. Trim down to a multiple of ten, when v - half_ulp reaches it. The tie is
   v - half_ulp exactly on the multiple, broken to even.
3. Trim up to a multiple of ten, when v + half_ulp reaches it. The tie is
   v + half_ulp exactly on the multiple, broken to even.

On the last-digit axis, from one multiple of ten up to the next (the two
shorter, trimmed candidates), v sits at integral + fractional:

    m*10                       v                       (m+1)*10
    ---|----+----+---- ... ----*----+---- ... ----+----+---|---
       0    1    2            d0   d0+1                9   10
             v-half_ulp <----( v )----> v+half_ulp

    trim down if the band reaches m*10; trim up if it reaches (m+1)*10;
    otherwise round to the nearest of d0 / d0+1 (tie at fractional == 1/2).

where d0 = last_digit and m = integral // 10, so m*10 = integral - last_digit
is the multiple of ten at or below integral (the trimmed significand).

For example, the x87 value bin_sig = 0x934F069BF2A74DE5, bin_exp = 6:

    v            = 679341447270162987328       (half_ulp = 32)
    [v-hu, v+hu] = [679341447270162987296, 679341447270162987360]
    nearest      = 67934144727016298733 x 10    # 20 digits (...987330)
    shortest     = 6793414472701629873  x 100   # 19 digits (...987300)

The interval reaches the multiple of ten just below v (...987300), so trim down
(decision 2) drops the last digit; rounding to nearest alone keeps 20 digits.

The exact power of two at sig_min is irregular: its lower gap is half an ulp,
so it is handled on a separate path.

For speed the two trim tests avoid reading the full 128-bit fraction: the last
decimal digit (integral mod 10, 4 bits) is merged with the top 124 bits of the
fraction into a single 128-bit integer

    c = (last_digit << 124) | (fractional >> 4),

with half_ulp = (pow10 >> (shift - 123)) mod 2**128 in the same scale, so the
two trim ties become c == half_ulp and c == ten - half_ulp (ten == 10 << 124).
Dropping the low 4 fractional bits loses a little more precision - one more
reason these boundaries need care.

Verification runs three edge-case searches, one per rounding boundary (round to
nearest, trim up to a multiple of ten, trim down to a multiple of ten). Each
counts the near-boundary residues: the product residues the algorithm reads as
a tie. For the two trim boundaries the count of these is asserted to equal
half_ulp_solution_count, the number of significands that sit *exactly* on the
boundary: any excess is a residue the algorithm mistakes for a tie, i.e. a
candidate misround. floor_sum gives both counts directly, with no
per-significand oracle.

to_decimal (the Żmij algorithm) and to_decimal_exact (the Fraction reference)
are kept for investigating any flagged case.
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Set, Tuple

from verify import (count_mod_mul_solutions, enumerate_mod_mul_solutions,
                    pow10_hi)

# Bits kept in each floored power-of-ten constant. The verifier needs a bit
# over digits + 128 (the tie-comparison window) so the near-boundary residues
# stay enumerable; 256 covers x87 (64-bit) and binary128 (113-bit) with room
# to spare.
POW10_BITS = 256


@dataclass
class Format:
    """Parameters of a binary floating-point format."""
    name: str         # human-readable label for the sweep output
    digits: int       # precision p: significand bits incl. the leading 1,
                      # whether that bit is stored (x87) or implicit (binary*)
    exp_bits: int     # exponent field width

    def __post_init__(self) -> None:
        sig_bits = self.digits - 1
        exp_offset = (1 << (self.exp_bits - 1)) - 1 + sig_bits
        self.sig_min = 1 << sig_bits              # smallest normal significand
        self.sig_max = (1 << self.digits) - 1
        self.min_e2 = 1 - exp_offset              # min unbiased exponent
        self.max_e2 = (1 << self.exp_bits) - 2 - exp_offset


BINARY80 = Format("x87 80-bit", digits=64, exp_bits=15)
BINARY128 = Format("IEEE binary128", digits=113, exp_bits=15)


def strip_zeros(dec_sig: int, dec_exp: int) -> Tuple[int, int]:
    """
    Drop trailing zeros from `dec_sig`, bumping `dec_exp` so that the value
    dec_sig * 10**dec_exp is unchanged and equal values compare equal.
    """
    while dec_sig and dec_sig % 10 == 0:
        dec_sig //= 10
        dec_exp += 1
    return dec_sig, dec_exp


def to_decimal(bin_sig: int, bin_exp: int, fmt: Format) -> Tuple[int, int]:
    """
    Bit-exact port of Żmij's long-double shortest path.

    Return the shortest decimal of bin_sig * 2**bin_exp as (significand, exp),
    the value significand * 10**exp with no trailing zeros.
    """
    regular = (bin_sig != fmt.sig_min)  # power of two: fraction bits are zero

    log10_2_sig = 20_201_781
    log10_3_4_sig = 8_384_497
    dec_exp = (bin_exp * log10_2_sig - (0 if regular else log10_3_4_sig)) >> 26

    pow10, pow10_exp = pow10_hi(-dec_exp, POW10_BITS)  # floored power of ten
    shift = -(bin_exp + pow10_exp)

    mask128 = (1 << 128) - 1
    product = bin_sig * pow10
    scaled = (product >> (shift - 128)) & ((1 << 256) - 1)
    integral = scaled >> 128
    fractional = scaled & mask128
    last_digit = integral % 10

    half_ulp = (pow10 >> (shift - 123)) & mask128
    c = ((last_digit << 124) | (fractional >> 4)) & mask128
    half = 1 << 127
    ten = 10 << 124
    even = (bin_sig & 1) == 0

    if regular:
        round_up = fractional >= half
        if fractional == half:
            round_up = (integral & 1) != 0
        trim_down = c <= half_ulp
        if c == half_ulp:
            trim_down = even
    else:
        round_up = fractional > half
        quarter_ulp = half_ulp >> 1
        if (fractional >> 4) > quarter_ulp:
            round_up = True
        trim_down = c <= quarter_ulp

    trim_up = c >= ten - half_ulp
    gap = (ten - half_ulp - c) & mask128
    if gap <= 1 and (dec_exp == 0 or gap == 1):
        trim_up = even

    if trim_down or trim_up:
        dec_sig = integral - last_digit + (10 if trim_up else 0)
    else:
        dec_sig = integral + round_up

    return strip_zeros(dec_sig, dec_exp)


def log10_floor(f: Fraction) -> int:
    """floor(log10(f)) for f > 0."""
    n, d = f.numerator, f.denominator

    def ge_pow(k: int) -> bool:  # n/d >= 10**k, using only non-negative powers
        return n >= d * 10 ** k if k >= 0 else n * 10 ** (-k) >= d

    # Estimate from bit lengths (log10(2) ~ 0.30103); the loops below correct
    # it. str(n) would trip Python's 4300-digit int-to-str limit for extremes.
    k = int((n.bit_length() - d.bit_length()) * 0.30103)
    while ge_pow(k + 1):
        k += 1
    while not ge_pow(k):
        k -= 1
    return k


def to_decimal_exact(bin_sig: int, bin_exp: int, fmt: Format
                     ) -> Tuple[int, int]:
    """
    The true shortest correctly-rounded decimal of bin_sig * 2**bin_exp,
    computed with exact Fraction arithmetic; the reference for to_decimal.
    """
    two = Fraction(2)
    v = Fraction(bin_sig) * two ** bin_exp

    # Nearest representable neighbors. Only a power of two above the minimum
    # exponent is irregular (its lower gap is half an ulp); subnormals and the
    # smallest normal are uniformly spaced.
    if bin_sig < fmt.sig_max:
        succ = Fraction(bin_sig + 1) * two ** bin_exp
    else:
        succ = Fraction(fmt.sig_min) * two ** (bin_exp + 1)
    if bin_sig == fmt.sig_min and bin_exp > fmt.min_e2:
        pred = Fraction(fmt.sig_max) * two ** (bin_exp - 1)
    else:
        pred = Fraction(bin_sig - 1) * two ** bin_exp

    lo = (v + pred) / 2
    hi = (v + succ) / 2
    closed = (bin_sig % 2 == 0)  # endpoints round to v only under ties-to-even

    # Largest p (fewest significant digits) with a multiple of 10**p in the
    # rounding interval; then the in-interval multiple nearest v (ties to even).
    # Run the search with integer floor/ceil on the fractions' numerators and
    # denominators, avoiding gcd-heavy Fraction division in the hot loop.
    ln, ld = lo.numerator, lo.denominator
    hn, hd = hi.numerator, hi.denominator
    vn, vd = v.numerator, v.denominator
    p_hi = log10_floor(hi) + 2
    p_lo = log10_floor(hi - lo) - 2
    for p in range(p_hi, p_lo - 1, -1):
        gn, gd = (10 ** p, 1) if p >= 0 else (1, 10 ** -p)
        lnum, lden = ln * gd, ld * gn    # lo / 10**p
        hnum, hden = hn * gd, hd * gn    # hi / 10**p
        kmin = -(-lnum // lden)          # ceil
        if not closed and lnum % lden == 0:
            kmin += 1
        kmax = hnum // hden              # floor
        if not closed and hnum % hden == 0:
            kmax -= 1
        if kmin > kmax:
            continue
        # round() on a Fraction gives nearest, ties to even; clamp to interval.
        k = max(kmin, min(kmax, round(Fraction(vn * gd, vd * gn))))
        return strip_zeros(k, p)
    raise AssertionError("no shortest decimal found")


# --- verification ----------------------------------------------------------
#
# The three find_edge_case_* searches are adapted from yy_double/verify.py
# (https://github.com/ibireme/c_numconv_benchmark), which verifies binary64,
# retargeted to the extended-precision formats, and using floor_sum instead of
# continued fractions and the three-gap theorem.
#
# One search per rounding boundary. Each counts the near-boundary residues, the
# R = (bin_sig * pow10) mod 2**shift the algorithm reads as a tie, using
# floor_sum via count_mod_mul_solutions.


def half_ulp_solution_count(bin_exp: int, dec_exp: int, sig_min: int,
                            sig_max: int, sign: int) -> int:
    """
    Number of significands in [sig_min, sig_max] whose boundary
    v + sign * half_ulp lands exactly on a multiple of 10**(dec_exp + 1), the
    grid a trim rounds to. Nonzero only for dec_exp > 0: smaller values are
    dyadic fractions (denominator a power of two) that can never sit exactly on
    such a multiple.
    """
    if dec_exp <= 0:
        return 0
    ulp = 1 << bin_exp                 # bin_exp > 0 whenever dec_exp > 0
    dec_den = 10 ** (dec_exp + 1)      # == 10 ** len(str(ulp))
    r = (sign * (ulp >> 1)) % dec_den  # v + sign * half_ulp on a multiple of 10
    return count_mod_mul_solutions(ulp, dec_den, sig_min, sig_max, r, r)


class Params:
    """Per-exponent constants of the regular path, mirroring to_decimal."""

    def __init__(self, bin_exp: int):
        self.bin_exp = bin_exp
        self.dec_exp = (bin_exp * 20_201_781) >> 26
        pow10, pow10_exp = pow10_hi(-self.dec_exp, POW10_BITS)
        self.pow10 = pow10
        self.shift = -(bin_exp + pow10_exp)
        self.half_ulp = (pow10 >> (self.shift - 123)) & ((1 << 128) - 1)
        # pow10 is exact (drops no significant bits) iff 5**(-dec_exp) fits in
        # POW10_BITS; then scaling adds no error and the tie tests are exact.
        self.exact = (self.dec_exp <= 0
                      and (5 ** -self.dec_exp).bit_length() <= POW10_BITS)


def find_edge_case_1(p: Params, sig_min: int, sig_max: int,
                     found: Set[Tuple[int, int]]) -> None:
    """
    Round to nearest: report significands whose fractional part lands within
    one LSB of the 1/2 tie (fractional == 2**127), where the floored pow10
    could push the true value across it. Exact pow10 adds no error, so skip it.
    """
    if p.exact:
        return
    den = 1 << p.shift
    lsb = 1 << (p.shift - 128)           # R spanned by one fractional unit
    tie = 1 << (p.shift - 1)             # fractional == 2**127
    lo, hi = tie - lsb, tie + lsb - 1
    if count_mod_mul_solutions(p.pow10, den, sig_min, sig_max, lo, hi) == 0:
        return
    for bin_sig, _ in enumerate_mod_mul_solutions(p.pow10, den, sig_min,
                                                  sig_max, lo, hi):
        found.add((p.bin_exp, bin_sig))


def trim_band(p: Params, c: int) -> Tuple[int, int, int]:
    """
    Residue window (mod 10 * 2**shift) and modulus covering the one LSB the
    algorithm reads as this c. c = last_digit * 2**124 | fractional >> 4;
    encoding res = last_digit * 2**shift + R (R = product mod 2**shift) pins
    the last digit while R ranges over one LSB.
    """
    lsb = 1 << (p.shift - 124)
    base = (c >> 124) * (1 << p.shift) + (c & ((1 << 124) - 1)) * lsb
    return 10 << p.shift, base, base + lsb - 1


def find_edge_case_2(p: Params, sig_min: int, sig_max: int) -> None:
    """
    Trim up to a multiple of ten: v + half_ulp on that multiple.

    Flooring pow10 (hence also half_ulp) can only lower the algorithm's c, so a
    genuine tie is expected one LSB below the true threshold ten - half_ulp, at
    gap == 1, the position the even override treats as the tie. We search at
    c == ten - half_ulp - 1, and the count assertion below confirms it.
    """
    if p.exact:
        return
    den, lo, hi = trim_band(p, (10 << 124) - p.half_ulp - 1)
    count = count_mod_mul_solutions(p.pow10, den, sig_min, sig_max, lo, hi)
    assert count == half_ulp_solution_count(p.bin_exp, p.dec_exp, sig_min,
                                            sig_max, +1), \
        f"trim_up bin_exp={p.bin_exp} dec_exp={p.dec_exp} count={count}"


def find_edge_case_3(p: Params, sig_min: int, sig_max: int) -> None:
    """Trim down to a multiple of ten: v - half_ulp on that multiple."""
    if p.exact:
        return
    den, lo, hi = trim_band(p, p.half_ulp)                 # c == half_ulp
    count = count_mod_mul_solutions(p.pow10, den, sig_min, sig_max, lo, hi)
    assert count == half_ulp_solution_count(p.bin_exp, p.dec_exp, sig_min,
                                            sig_max, -1), \
        f"trim_down bin_exp={p.bin_exp} dec_exp={p.dec_exp} count={count}"


def find_edge_cases(fmt: Format) -> None:
    """Run the three edge-case searches over every binary exponent."""
    print(f"{fmt.name} edge-case sweep ... ", end="", flush=True)
    found: Set[Tuple[int, int]] = set()
    for bin_exp in range(fmt.min_e2, fmt.max_e2 + 1):
        p = Params(bin_exp)
        # Regular significands (the power of two at sig_min is irregular and
        # not covered here); subnormals share min_e2 and use the regular path.
        ranges = [(fmt.sig_min + 1, fmt.sig_max)]
        if bin_exp == fmt.min_e2:
            ranges.append((1, fmt.sig_min - 1))
        for sig_min, sig_max in ranges:
            find_edge_case_1(p, sig_min, sig_max, found)
            find_edge_case_2(p, sig_min, sig_max)
            find_edge_case_3(p, sig_min, sig_max)

    print("ok")
    if found:
        print(f"  {len(found)} round-to-nearest near-tie candidate(s) to "
              f"inspect:")
        for bin_exp, bin_sig in sorted(found):
            print(f"    bin_sig=0x{bin_sig:X} bin_exp={bin_exp}: "
                  f"actual={to_decimal(bin_sig, bin_exp, fmt)} "
                  f"expected={to_decimal_exact(bin_sig, bin_exp, fmt)}")


if __name__ == "__main__":
    find_edge_cases(BINARY80)
    find_edge_cases(BINARY128)
