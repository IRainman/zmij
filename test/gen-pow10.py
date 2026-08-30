#!/usr/bin/env python3
# Power of 10 significand generator for Żmij.
# Copyright (c) 2025 - present, Victor Zverovich
#
# The output is a superset of zmij.c's pow10_significands table. zmij.cc builds
# the same significands at compile time, and the pow10 test checks them against
# big integers computed in the test itself.

import math

# Range of decimal exponents covered by the pow10 significand table.
dec_exp_min = -341
dec_exp_max =  307

num_bits = 128

def get_pow10():
    # Negate dec_pow_min and dec_pow_max because we need negative powers 10^-k.
    for dec_exp in range(-dec_exp_max, -dec_exp_min + 1, 1):
        # dec_exp is -k in the paper.
        bin_exp = math.floor(dec_exp * math.log2(10)) - (num_bits - 1)
        bin_pow = 2**abs(bin_exp)
        dec_pow = 10**abs(dec_exp)
        if dec_exp < 0:
            result = bin_pow // dec_pow
        elif bin_exp < 0:
            result = dec_pow * bin_pow
        else:
            result = dec_pow // bin_pow
        hi, lo = result >> 64, (result & (2**64 - 1))
        print(f"{{{hi:#x}, {lo:#018x}}}, // {dec_exp:4}")

get_pow10()
