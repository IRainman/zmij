#!/usr/bin/env python3
"""
A script to verify the correctness of the Żmij FP-to-string conversion for
80-bit (x87 extended) long double.

Copyright (c) 2025 - present, Victor Zverovich
Distributed under the MIT license (see LICENSE) or alternatively
the Boost Software License, Version 1.0.
https://github.com/vitaut/zmij/

Companion to verify.py (double), reusing its floor_sum machinery. Żmij's
long-double path adapts YaoYuan's (yy) method with rounded-down 256-bit
power-of-ten constants.

Scaling the 64-bit significand by a floored constant leaves the result low by
under 2**64. The >= 124 low-order bits below the retained fraction hold this
shortfall far short of every boundary, so a decision could flip only for a
significand within that margin. floor_sum finds none across all binary
exponents, so every window is empty - which is itself the proof. (Any
candidate that appeared would be checked against an exact Fraction oracle.)
"""

from dataclasses import dataclass
from fractions import Fraction
from typing import Set, Tuple

from verify import (count_mod_mul_solutions, enumerate_mod_mul_solutions,
                    pow10_hi)


@dataclass
class Format:
    """Parameters of a binary floating-point format."""
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


BINARY80 = Format(digits=64, exp_bits=15)       # x87 extended


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

    pow10, pow10_exp = pow10_hi(-dec_exp, 256)  # 256-bit floor power of ten
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
# find_regular_edge_cases derives the rounding boundaries for one exponent,
# check_boundaries enumerates the significands whose product residue lands
# just below each boundary, and the exact Fraction oracle checks those.


def check_boundaries(bin_exp: int, pow10: int, shift: int, x_min: int,
                     x_max: int, boundaries: Set[int], exact: bool,
                     exceptions: Set[Tuple[int, int]],
                     fmt: Format) -> int:
    """
    Check the near-boundary significands for one exponent against the oracle
    and return how many were checked.
    """
    mod = 1 << shift
    margin = 1 << 66   # window width; must exceed the < 2**64 error
    checked = 0
    seen: Set[int] = set()
    for boundary in boundaries:
        # A significand misrounds only if the product residue R = (bin_sig *
        # pow10) mod 2**shift lands within margin below the boundary b, where
        # the < 2**64 error from the floored pow10 can carry the true residue up
        # across b. The boundary point R == b is a hazard only when pow10 is
        # inexact: the model then reads an exact tie while the true value is
        # strictly above b and must round up. Every b is a multiple of the
        # discard granularity 2**(shift-128), so R == b has a zero discarded
        # tail; when pow10 is exact (e == 0) the true value then sits exactly on
        # b, a genuine tie handled correctly, and R can land there for a whole
        # cluster of significands, so b is left out to keep the window
        # enumerable. Trim boundaries can reduce to near 0 mod 2**shift, so
        # split the window when it wraps past 0.
        b = boundary % mod
        top = b if not exact else b - 1
        if b == 0:
            windows = [(mod - margin, mod - 1)]
            if not exact:
                windows.append((0, 0))
        elif b >= margin:
            windows = [(b - margin, top)]
        else:  # margin << mod, so mod + b - margin never underflows past 0
            windows = [(0, top), (mod + b - margin, mod - 1)]
        for y_lo, y_hi in windows:
            count = count_mod_mul_solutions(pow10, mod, x_min, x_max,
                                            y_lo, y_hi)
            # Residues never cluster this close to a tie, so the window stays
            # small enough to check exhaustively; a wider-than-expected one
            # means a boundary was mis-derived, so fail loudly.
            assert count <= 256, \
                f"bin_exp={bin_exp} boundary={boundary:#x}: {count}"
            for bin_sig, _ in enumerate_mod_mul_solutions(pow10, mod, x_min,
                                                          x_max, y_lo, y_hi):
                if bin_sig in seen:
                    continue
                seen.add(bin_sig)
                checked += 1
                actual = to_decimal(bin_sig, bin_exp, fmt)
                if actual != to_decimal_exact(bin_sig, bin_exp, fmt):
                    exceptions.add((bin_exp, bin_sig))
    return checked


def find_regular_edge_cases(bin_exp: int, x_min: int, x_max: int,
                            exceptions: Set[Tuple[int, int]],
                            fmt: Format) -> int:
    """
    Check the near-boundary significands in [x_min, x_max] for one exponent,
    at every tie a rounding error could flip.

    The integral carry is not enumerated (unlike verify.py): its region is
    dense - for round exponents R clusters, so ~1/5 of significands sit near a
    carry - and cannot be swept. Instead note that across a carry the model's
    c and the true c are adjacent (they differ by 1 for last digit d < 9; ten
    vs 0 for d == 9), so trim_up, trim_down, and the gap <= 1 even override all
    resolve the same on both sides - yielding integral + 1 or the matching
    trim - unless a decision threshold lands between them, i.e. half_ulp within
    1 of a multiple of 2**124. The assert below rules that out for every inexact
    exponent; exact ones have e == 0 and never straddle a carry.
    """
    # Per-exponent regular-path constants, mirroring to_decimal's derivation.
    log10_2_sig = 20_201_781
    dec_exp = (bin_exp * log10_2_sig) >> 26
    pow10, pow10_exp = pow10_hi(-dec_exp, 256)
    shift = -(bin_exp + pow10_exp)
    # shift stays in [252, 255] over the whole exponent range, so the step
    # 2**(shift-124) below is >= 2**128 and dwarfs the < 2**64 constant error;
    # the boundary derivation relies on it, and a smaller shift would break it.
    assert 252 <= shift <= 255, (bin_exp, shift)
    half_ulp = (pow10 >> (shift - 123)) & ((1 << 128) - 1)

    # pow10 is exact (drops no significant bits) iff 5**(-dec_exp) fits in the
    # 256-bit significand; the 2**k in 10**k contributes only trailing zeros.
    # Only then is e == 0, which check_boundaries uses to skip the R == b point.
    exact = dec_exp <= 0 and (5 ** -dec_exp).bit_length() <= 256

    # Integral-carry safety (see docstring): a carry misrounds only if a
    # decision threshold falls between the adjacent model and true c, i.e. if
    # half_ulp is within 1 of a multiple of 2**124. Only inexact exponents
    # straddle; assert they stay far from that alignment (the actual slack is
    # ~2**110), so the dense carry region needs no enumeration.
    if not exact:
        r = half_ulp % (1 << 124)
        assert min(r, (1 << 124) - r) > (1 << 66), (bin_exp, half_ulp)

    # Round to nearest: the two edges of the fractional == 1/2 band.
    enter = 1 << (shift - 1)                  # fractional enters == 1/2 band
    leave = enter + (1 << (shift - 128))      # and leaves it
    nearest = {enter, leave}

    # c is quantized in units of one R step, so each tie sits at a step
    # boundary k*step and a decision flips as c crosses it. The window sits
    # just below k*step, catching the residue that a carry pushes up to k.
    # The trim boundaries below key only on c's low 124 bits: last_digit (its
    # top 4 bits) lives outside R, so each is probed for all last_digit - a
    # sound superset of the true trigger that the oracle then confirms.
    step = 1 << (shift - 124)                 # R granularity of one c unit

    # Round up to a multiple of 10 (trim_up): trim_up_frac is fractional_top124
    # at the threshold ten - half_ulp. With gap = (ten - half_ulp - c) mod
    # 2**128, the even override rounds at c == threshold - 1 (gap 1) always, and
    # at c == threshold (gap 0) when dec_exp == 0. One past that the gap wraps
    # around and the override drops, so trim_up flips at fractional_top124 in
    # {trim_up_frac +/- 1, trim_up_frac}; probe the step below each.
    trim_up_frac = ((10 << 124) - half_ulp) & ((1 << 124) - 1)
    carry_ten = {(trim_up_frac - 1) * step, trim_up_frac * step,
                 (trim_up_frac + 1) * step}

    # Round down to a multiple of 10 (trim_down): trim_down flips as c crosses
    # half_ulp, into the tie (c == half_ulp) and out of it (c == half_ulp + 1).
    trim_down_frac = half_ulp & ((1 << 124) - 1)
    drop_last = {trim_down_frac * step, (trim_down_frac + 1) * step}

    return check_boundaries(bin_exp, pow10, shift, x_min, x_max,
                            nearest | carry_ten | drop_last, exact,
                            exceptions, fmt)


def find_edge_cases(fmt: Format) -> None:
    """Sweep every binary exponent for potential misrounds."""
    print("long double edge-case sweep ... ", end="", flush=True)
    exceptions: Set[Tuple[int, int]] = set()
    checked = 0
    powers_of_two = 0
    sig_min, sig_max = fmt.sig_min, fmt.sig_max
    for bin_exp in range(fmt.min_e2, fmt.max_e2 + 1):
        # The power of two is the only irregular significand (asymmetric
        # boundaries); check it directly.
        powers_of_two += 1
        if to_decimal(sig_min, bin_exp, fmt) != \
                to_decimal_exact(sig_min, bin_exp, fmt):
            exceptions.add((bin_exp, sig_min))
        # Regular significands (exclude the power of two at sig_min).
        checked += find_regular_edge_cases(bin_exp, sig_min + 1, sig_max,
                                           exceptions, fmt)
        if bin_exp == fmt.min_e2:  # subnormals share min_e2, use regular path
            checked += find_regular_edge_cases(bin_exp, 1, sig_min - 1,
                                               exceptions, fmt)

    if exceptions:
        print("FAILED")
        for bin_exp, bin_sig in sorted(exceptions):
            print(f"  bin_sig=0x{bin_sig:016X} bin_exp={bin_exp}: "
                  f"actual={to_decimal(bin_sig, bin_exp, fmt)} "
                  f"expected={to_decimal_exact(bin_sig, bin_exp, fmt)}")
        raise SystemExit(1)

    print("ok")
    if checked:
        print(f"  {checked:,} near-boundary significands and {powers_of_two:,} "
              f"powers of two checked; no misrounds")
    else:
        print(f"  {powers_of_two:,} powers of two checked; no other "
              f"significand lies within 2**64 of a rounding boundary, so no "
              f"decision can flip; no misrounds")


if __name__ == "__main__":
    find_edge_cases(BINARY80)
