-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import core
-- `Finset.Icc` over ℕ, which the sweeps over the precision need.
import Mathlib.Order.Interval.Finset.Nat

/-! # Correctness of Żmij at a chosen precision

`zmij.lean` proves the shortest path correct. This file proves the other one:
`to_decimal(bin_sig, bin_exp, precision)`, which rounds to a digit count the
caller picks, together with the `normalize` a caller runs first. The two share
the power-of-ten table and nothing else. There is no shortest representation to
select here, so `core.lean`'s selection rule plays no part; what has to hold is
that the reported significand has the digits asked for and is correctly rounded
on the grid reported with it, which is `correct`.

    shift   = 52 - floor(log2(bin_sig))      -- normalize; 0 for a normal
    bin_sig, bin_exp = bin_sig << shift, bin_exp - shift
    dec_exp = compute_dec_exp(bin_exp + 52) - (precision - 1)
    scaled  = scale(bin_sig, bin_exp, dec_exp)
    dec_sig = round_even(scaled)
    if dec_sig >= 10^precision:              -- one digit too many
      dec_sig, dec_exp = round_even(demote(scaled)), dec_exp + 1

`normalize` brings the significand's leading bit up to bit 52, which
`to_decimal` needs because it picks the scale from the exponent alone. zmij's
callers run it, for a subnormal only; folding it in here is what lets `correct`
speak of a binary64 value rather than of an already-shifted significand.

`scale` packs the scaled value above two guard bits, bit 1 the 1/2 place and bit
0 a sticky bit, and `round_even` reads its decision off those two. The packed
value is inexact twice over, and the two errors are placed so that neither can
turn a decision:

* the table entry is the truncated 128-bit significand of `10^k` with one
  added, so the computed value never falls below the exact one and a value at or
  above a midpoint cannot present itself below one;
* the sticky bit is taken from the product's bits `[64, n-1)`, discarding the
  low word, so the bump's excess — under `2^64` denominators, `gap_lt` — cannot
  appear as a set sticky bit and push a value exactly on a midpoint above it.

One ambiguity survives: a value *near* a half-step boundary presents the same
guard bits as one exactly on it. `tie_windows_refuted` rules that out over every
significand of every (exponent, precision) pair, and it covers the reported grid
and the reround's at once: a grid point is an even multiple of half a step and a
midpoint an odd one, so both are boundaries of the same spacing.

With that ruled out the packed value is not an approximation of the scaled value
at all. It is that value's canonical guard/sticky encoding at the half step,
`packed_eq_exact_packed`, which is the invariant the rest of the file turns on:
correctness of `round_even`, and of `round_even` after `demote`, are then generic
facts about the encoding. They are the same fact twice, because a demoted
encoding is the encoding at ten times the half step, `demote_exact_packed`, so
the reround's grid is the reported grid with a coarser step and nothing else.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`; only `toDecimal`
  takes them unnormalized, everything under it is the normalized pair;
* `p`: the number of significant digits asked for;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`;
* `n`: `shiftBits e p`, the product bits below the integral part.

The scaled value is `exact f e p / step e p`, and everything between the
arithmetic and the specification is a comparison of integers in that cleared
scale. `exact_eq` is the one identity it all rests on: the integral part and the
1/2 bit at their weights, plus a remainder `dev` that the guard bits do not
report.

## Dependencies

    correct
      ← normalized_of_finite
      ← correctly_rounded_of_normalized
          ← value_normalized
      ← rounded_correct
          ← fine_within_half, coarse_within_half
              ← packed_eq_exact_packed
                  ← exact_eq
                  ← dev_eq_zero         (the certificates)
                  ← dev_pos_of_sticky
              ← round_even_exact_packed
              ← demote_exact_packed     (the reround's grid only)
          ← exact_bounds                (the digit count)
          ← value_scaled                (the other use of ℚ)

## Why it is not in the default build

The checks below run for about two minutes. Nothing else depends on this file,
so it is a `lean_lib` of its own, absent from `defaultTargets`: `lake build` is
unaffected and `lake build «zmij-p»` is the explicit request to verify the
fixed-precision path.

## What the two minutes are spent on

|  | count | cost |
|---|---|---|
| `point_shift_bounds` | 37,764 pairs | 12s |
| `table_checks` | 649 indices, to 1.1 kbit | under a second |
| `grid_bounds` | 37,764 pairs | 21s |
| `pair_refuted` | 37,764 certificates | ~95s |

As in `yy128.lean` and `yy80.lean` the multiplier is found by
`ModWindows.search` during elaboration and only the literal reaches the proof
term. The certificates are the bulk of the cost even so, and they spend it on
elaboration rather than in the kernel: 37,764 goals, against the 2098 exponents
`zmij.lean` splits.
-/

namespace zmij.precision

set_option maxHeartbeats 0

-- The sweeps fold over lists of tens of thousands of entries, well past the
-- default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## Żmij's fixed-precision conversion

One 192-bit multiply of the shifted significand by the 128-bit power of ten,
with the integral part and the two guard bits read out of the product at a fixed
bit position. The definitions below name each of those pieces, and the shift
that fills the significand's box before any of them.
-/

/-- The decimal exponent of the grid the digits are asked for: the exponent of
    the leading digit, estimated from the exponent of the value's top bit, less
    the `p - 1` digits that follow it. -/
def decExp (e : ℤ) (p : ℕ) : ℤ :=
  binary64.decimalExponent (e + 52) - ((p : ℤ) - 1)

/-- The index of the power of ten `scale` reads, `-dec_exp`. -/
def idx (e : ℤ) (p : ℕ) : ℤ := -decExp e p

/-- zmij's `point_shift`: where the binary point falls in the top 128 bits of
    the product, `11 - bin_exp - pow10_exp`. The 11 is the headroom above a
    normalized binary64 significand in a 64-bit word. -/
def pointShift (e : ℤ) (p : ℕ) : ℤ :=
  11 - e - binary64.power10Exponent (idx e p)

/-- The product bits below the integral part: the 64 that `umul192_hi128`
    discards, the 64 of `p.lo`, and `point_shift`. -/
def shiftBits (e : ℤ) (p : ℕ) : ℕ := (128 + pointShift e p).toNat

/-- Numerator of the exact power of ten at the index read. -/
def num (e : ℤ) (p : ℕ) : ℕ := binary64.power10Num (idx e p)

/-- Denominator of that same power of ten. -/
def den (e : ℤ) (p : ℕ) : ℕ := binary64.power10Den (idx e p)

/-- The table entry `scale` multiplies by: the truncated 128-bit significand of
    `10^k`, which is `num / den`, with one added. That is the ceiling wherever
    the truncation loses something and one place past it at the 56 indices where
    it does not, and the error budget asks only that the entry be at or above
    the exact ratio by under a denominator's worth, so the bump needs no
    condition on the index. zmij adds it to the low word, which is where it
    fits: `table_checks`. -/
def tableEntry (k : ℤ) : ℕ :=
  binary64.power10Num k / binary64.power10Den k + 1

/-- The 192-bit product, `(bin_sig << 11) · pow10`. -/
def product (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := f * 2 ^ 11 * tableEntry (idx e p)

/-- The integral part of the scaled value, `p.hi >> point_shift`. -/
def integral (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := product f e p / 2 ^ shiftBits e p

/-- The 1/2 bit, the product bit just below the integral part. -/
def half (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  product f e p / 2 ^ (shiftBits e p - 1) % 2

/-- The product bits below the 1/2 place. zmij sees all but their low 64. -/
def tail (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := product f e p % 2 ^ (shiftBits e p - 1)

/-- The sticky bit: whether anything zmij can see below the 1/2 place is set.
    The low 64 product bits are not among them, `umul192_hi128` having dropped
    them, so this is `tail` from bit 64 up. -/
def sticky (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  if tail f e p / 2 ^ 64 = 0 then 0 else 1

/-- `scale`: the scaled value packed above its two guard bits. zmij writes the
    three pieces into disjoint bits with `integral << 2 | half << 1 |
    sticky`. -/
def packed (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  4 * integral f e p + 2 * half f e p + sticky f e p

/-- `round_even`: a packed value to the nearest integer, ties to even, off the
    two guard bits. -/
def roundEven (x : ℕ) : ℕ := (x + 1 + x / 4 % 2) / 4

/-- Repack a packed value one decimal place coarser, folding the digit that
    leaves into the sticky bit. Unlike the packing above this is written as zmij
    writes it, because the bit it sets may already be set: what the reround must
    not do is present the coarser value as exact when a digit was dropped. -/
def demote (x : ℕ) : ℕ := x / 10 ||| (if x % 10 = 0 then 0 else 1)

/-- The rounding itself, on a normalized significand: `round_even` off the
    packed value, rerounded one place coarser when it comes out a digit too
    long. -/
def rounded (f : ℕ) (e : ℤ) (p : ℕ) : ℕ × ℤ :=
  let x := packed f e p
  let d := roundEven x
  if d < 10 ^ p then (d, decExp e p) else (roundEven (demote x), decExp e p + 1)

/-- `normalize`'s shift, `clz(bin_sig) - 11` written as a logarithm: what it
    takes to bring the significand's leading bit up to bit 52. It is zero once
    the bit is there, which is why zmij's callers run `normalize` for a
    subnormal only. -/
def normShift (f : ℕ) : ℕ := 52 - Nat.log2 f

/-- `to_decimal` on the value a caller has, `normalize` then the rounding: the
    significand and exponent zmij reports for `p` significant digits. zmij
    returns the significand padded right to 18 digits along with the leading
    digit's exponent, which denotes the same value. Those 18 also bound the
    precision a caller may ask for, `1 ≤ p ∧ p ≤ 18` standing as a hypothesis
    of its own throughout: it constrains the request, where `binary64.Finite`
    and the structure below constrain the value. -/
def toDecimal (f : ℕ) (e : ℤ) (p : ℕ) : ℕ × ℤ :=
  rounded (f * 2 ^ normShift f) (e - normShift f) p

/-- The value `rounded` is called on, which `normalized_of_finite` derives from
    `binary64.Finite`, the value `to_decimal` is called on. The significand is
    normalized, which for a subnormal costs exponent range: the shift reaches 52
    below `emin`. -/
structure Normalized (f : ℕ) (e : ℤ) : Prop where
  sig : 2 ^ 52 ≤ f ∧ f < 2 ^ 53
  exp : -1126 ≤ e ∧ e ≤ 971

/-! ## The cleared scale

Scaled by `10^(-k)`, the reported grid becomes the integers and the exact value
becomes `exact / step`. `step` is the factor that clears it: the power of ten's
denominator times the product's alignment. Every comparison below is between
integers in that scale, and `halfStep` is the distance a correctly rounded
significand must stay within.
-/

/-- Half a step of the reported grid, cleared. -/
def halfStep (e : ℤ) (p : ℕ) : ℕ := den e p * 2 ^ (shiftBits e p - 1)

/-- One step of the reported grid, cleared: the scale that clears it. -/
def step (e : ℤ) (p : ℕ) : ℕ := 2 * halfStep e p

/-- The exact scaled value, cleared: `f·2^e·10^(-k)·step`. -/
def exact (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := f * 2 ^ 11 * num e p

/-- What the discarded low word can be worth, cleared: the bump puts the entry
    at most one above the exact ratio, which the shifted significand scales by
    under `2^64`. -/
def slack (e : ℤ) (p : ℕ) : ℕ := 2 ^ 64 * den e p

/-- What the bump added, cleared and scaled by the significand: the difference
    between the product zmij formed and the exact one. -/
def gap (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := den e p * product f e p - exact f e p

/-- What the guard bits do not report: the product bits below the 1/2 place,
    cleared, less what the bump added. It is `dev` being zero that makes an
    apparent tie a real one. -/
def dev (f : ℕ) (e : ℤ) (p : ℕ) : ℤ := den e p * tail f e p - gap f e p

/-! ## Finite checks

Three cheap sweeps — the table over the indices reached, where the product is
read, and that the scaled value has the digits asked for — and then the two
certificate families, which are the reason for the wait. The indices themselves
need no sweep: monotonicity bounds them.
-/

/-- The indices `scale` reads. Monotonicity of `decimalExponent` puts them
    between the two ends of the domain, so this is a derivation and not a
    sweep. -/
theorem idx_range {e : ℤ} {p : ℕ} (he : -1126 ≤ e ∧ e ≤ 971)
    (hp : 1 ≤ p ∧ p ≤ 18) : -307 ≤ idx e p ∧ idx e p ≤ 341 := by
  have hlo : binary64.decimalExponent (-1074)
      ≤ binary64.decimalExponent (e + 52) :=
    binary64.decimal_exponent_mono (by omega)
  have hhi : binary64.decimalExponent (e + 52)
      ≤ binary64.decimalExponent 1023 :=
    binary64.decimal_exponent_mono (by omega)
  have hends : binary64.decimalExponent (-1074) = -324
      ∧ binary64.decimalExponent 1023 = 307 := by
    constructor <;> rfl
  simp only [idx, decExp]
  omega

/-- Where `scale` reads the product. `point_shift` staying in `[3, 62]` is what
    makes zmij's two shifts and its mask well defined, and it leaves `n` far
    above 65, which is what keeps the discarded low word inside half a step. -/
theorem point_shift_bounds : ∀ p ∈ Finset.Icc 1 18,
    ∀ e ∈ Finset.Icc (-1126 : ℤ) 971,
      3 ≤ pointShift e p ∧ pointShift e p ≤ 62 := by
  -- `+kernel` keeps the enumeration out of the elaborator, whose recursion and
  -- exponentiation guards it would otherwise trip. So for the two sweeps below.
  decide +kernel

/-- The table over the indices reached: the bump does not carry out of the low
    word it is added to, and the entry it leaves is a normalized 128-bit number.

    Nothing below consumes this. `tableEntry` is the single number zmij's two
    words denote, and the correctness argument reads it as one; this is the check
    that the two words really do denote it, which is what lets zmij add its one
    to the low word alone. It is fidelity to the implementation, not a step in
    the chain, and it is kept here because it is the only place that pairing is
    written down. -/
theorem table_checks : ∀ k ∈ Finset.Icc (-307 : ℤ) 341,
    binary64.power10Num k / binary64.power10Den k % 2 ^ 64 ≠ 2 ^ 64 - 1
      ∧ 2 ^ 127 ≤ tableEntry k ∧ tableEntry k < 2 ^ 128 := by
  decide +kernel

/-- The scaled value has the digits asked for, to within a step: it is at least
    `10^(p-1)` and below `2·10^p`. Monotonicity in the significand leaves one
    comparison per end of its box. -/
theorem grid_bounds : ∀ p ∈ Finset.Icc 1 18, ∀ e ∈ Finset.Icc (-1126 : ℤ) 971,
    10 ^ (p - 1) * step e p ≤ 2 ^ 52 * 2 ^ 11 * num e p
      ∧ (2 ^ 53 - 1) * 2 ^ 11 * num e p < 2 * 10 ^ p * step e p := by
  decide +kernel

/-- The window problem at an (exponent, precision) pair: the residues of `exact`
    that sit within `slack` of a half-step boundary without sitting on one. A
    significand there would present the guard bits of a tie without being one,
    and that is the only way the packed value can mislead.

    The modulus is half a step rather than a step, which is what lets `0` stand
    for either kind of boundary: the reported grid's midpoints are the odd
    multiples of `halfStep` and the reround's grid points the even ones. -/
def tieWindows (e : ℤ) (p : ℕ) : ModWindows where
  g := 2 ^ 11 * num e p
  modulus := halfStep e p
  f0 := 2 ^ 52
  f1 := 2 ^ 53 - 1
  windows :=
    let w : ℤ := slack e p
    [(1 - w, -1), (1, w - 1)]

/-! ### Modular certificates

`modCertTactic` reads one integer literal out of the goal and runs the search on
it during elaboration, so the two indices have to arrive as one: `pairIndex`
packs them, eighteen precisions to the exponent, and the family below unpacks
them. A sweep over the packed index is then the same one variable
`interval_cases` splits in `yy128.lean` and `yy80.lean`.

Doing it instead by deciding `refutedBy search` over the grid would put the
Euclidean search itself in the kernel, 37,764 times, which is hours and
gigabytes rather than minutes.
-/

/-- The `(exponent, precision)` pair as one index, `0 ≤ c < 37764`. -/
def pairIndex (e : ℤ) (p : ℕ) : ℤ := (e + 1126) * 18 + ((p : ℤ) - 1)

/-- The window problem at the pair `c` denotes. -/
def pairWindows (c : ℤ) : ModWindows :=
  tieWindows (c / 18 - 1126) ((c % 18).toNat + 1)

/-- Close `∃ q, (pairWindows c).refutedBy q = true` for a literal `c`. -/
elab "tie_cert" : tactic => modCertTactic fun c => (pairWindows c).search

/-- No significand puts the guard bits at a tie that is not one. The multiplier
    is searched for during elaboration and checked by the kernel, so a bad one
    would be a failed proof rather than an unsound one. -/
private theorem pair_refuted (c : ℤ) (hlo : 0 ≤ c) (hhi : c ≤ 37763) :
    ∃ q, (pairWindows c).refutedBy q = true := by
  interval_cases c <;> tie_cert

/-- Unpacking inverts packing: eighteen precisions to the exponent, so the
    precision is what the division leaves. -/
private theorem pair_index_unpack {e : ℤ} {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 18) :
    pairIndex e p / 18 - 1126 = e ∧ (pairIndex e p % 18).toNat + 1 = p := by
  rw [pairIndex]
  omega

/-- The certificate in the pair's own terms. -/
theorem tie_windows_refuted {e : ℤ} {p : ℕ} (he : -1126 ≤ e ∧ e ≤ 971)
    (hp : 1 ≤ p ∧ p ≤ 18) : ∃ q, (tieWindows e p).refutedBy q = true := by
  obtain ⟨hdiv, hmod⟩ := pair_index_unpack (e := e) hp
  have h : pairWindows (pairIndex e p) = tieWindows e p := by
    simp only [pairWindows, hdiv, hmod]
  rw [← h]
  exact pair_refuted _ (by rw [pairIndex]; omega) (by rw [pairIndex]; omega)

/-! ## The arithmetic model

The product, split at the two bit positions zmij reads it at, and the exact
value, recovered from that split. `exact_eq` is where the two meet.
-/

theorem den_pos (e : ℤ) (p : ℕ) : 0 < den e p :=
  binary64.power10_den_pos _

theorem half_step_pos (e : ℤ) (p : ℕ) : 0 < halfStep e p := by
  have := den_pos e p
  rw [halfStep]
  positivity

theorem step_pos (e : ℤ) (p : ℕ) : 0 < step e p := by
  have := half_step_pos e p
  rw [step]
  omega

/-- The shift, as an integer, once `point_shift` is known to be non-negative. -/
theorem shift_bits_eq {e : ℤ} {p : ℕ} (hs : 3 ≤ pointShift e p) :
    (shiftBits e p : ℤ) = 128 + pointShift e p := by
  rw [shiftBits]
  omega

/-- And how far above 65 it leaves the shift, which is the room the discarded
    low word needs. -/
theorem shift_bits_ge {e : ℤ} {p : ℕ} (hs : 3 ≤ pointShift e p) :
    131 ≤ shiftBits e p := by
  rw [shiftBits]
  omega

/-- One step is the denominator against the whole alignment. -/
theorem step_eq {e : ℤ} {p : ℕ} (hn : 1 ≤ shiftBits e p) :
    step e p = den e p * 2 ^ shiftBits e p := by
  have h : 2 ^ shiftBits e p = 2 ^ (shiftBits e p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [step, halfStep, h]
  ring

/-- The product, split where zmij reads it: the integral part, the 1/2 bit, and
    the bits below it. -/
theorem product_split (f : ℕ) (e : ℤ) (p : ℕ) (hn : 1 ≤ shiftBits e p) :
    product f e p = 2 ^ shiftBits e p * integral f e p
      + 2 ^ (shiftBits e p - 1) * half f e p + tail f e p := by
  have hpow : 2 ^ shiftBits e p = 2 ^ (shiftBits e p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hq : product f e p / 2 ^ (shiftBits e p - 1)
      = 2 * integral f e p + half f e p := by
    rw [integral, half, hpow, ← Nat.div_div_eq_div_mul]
    omega
  calc product f e p
      = 2 ^ (shiftBits e p - 1) * (product f e p / 2 ^ (shiftBits e p - 1))
          + product f e p % 2 ^ (shiftBits e p - 1) :=
        (Nat.div_add_mod _ _).symm
    _ = 2 ^ (shiftBits e p - 1) * (2 * integral f e p + half f e p)
          + tail f e p := by rw [hq, tail]
    _ = _ := by rw [hpow]; ring

/-- The guard bits are bits. -/
theorem guard_le_one (f : ℕ) (e : ℤ) (p : ℕ) :
    half f e p ≤ 1 ∧ sticky f e p ≤ 1 := by
  refine ⟨?_, ?_⟩
  · rw [half]
    omega
  · rw [sticky]
    split_ifs <;> omega

/-- The bits below the 1/2 place are worth less than the 1/2 place. -/
theorem tail_lt (f : ℕ) (e : ℤ) (p : ℕ) :
    tail f e p < 2 ^ (shiftBits e p - 1) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A clear sticky bit is everything zmij can see below the 1/2 place being
    zero, which leaves the discarded low word unaccounted for. -/
theorem sticky_eq_zero_iff (f : ℕ) (e : ℤ) (p : ℕ) :
    sticky f e p = 0 ↔ tail f e p < 2 ^ 64 := by
  have hdiv : tail f e p / 2 ^ 64 = 0 ↔ tail f e p < 2 ^ 64 :=
    ⟨fun h0 => by
      by_contra hle
      have := Nat.div_pos (Nat.le_of_not_lt hle) (Nat.two_pow_pos 64)
      omega,
     Nat.div_eq_of_lt⟩
  rw [sticky]
  split_ifs with h
  · exact iff_of_true rfl (hdiv.mp h)
  · exact iff_of_false (by simp) fun hlt => h (hdiv.mpr hlt)

/-- The table entry is never below the exact ratio, and above it by one
    denominator's worth at most: the bump gives the first, and the truncation
    the bump lands on gives the second. -/
theorem entry_bounds (k : ℤ) :
    binary64.power10Num k ≤ binary64.power10Den k * tableEntry k
      ∧ binary64.power10Den k * tableEntry k
          ≤ binary64.power10Num k + binary64.power10Den k := by
  have hd := binary64.power10_den_pos k
  have hdm := Nat.div_add_mod (binary64.power10Num k) (binary64.power10Den k)
  have hlt := Nat.mod_lt (binary64.power10Num k) hd
  rw [tableEntry, Nat.mul_add]
  omega

/-- What the bump added: the product zmij formed, cleared, is the exact value
    plus `gap`. -/
theorem gap_eq (f : ℕ) (e : ℤ) (p : ℕ) :
    den e p * product f e p = exact f e p + gap f e p := by
  have hle : exact f e p ≤ den e p * product f e p := by
    rw [exact, product]
    calc f * 2 ^ 11 * num e p
        ≤ f * 2 ^ 11 * (den e p * tableEntry (idx e p)) :=
          Nat.mul_le_mul_left _ (entry_bounds _).1
      _ = den e p * (f * 2 ^ 11 * tableEntry (idx e p)) := by ring
  rw [gap]
  omega

/-- And it added less than the discarded low word could hold, which is why
    discarding it costs nothing. -/
theorem gap_lt (f : ℕ) (e : ℤ) (p : ℕ) (hf : f < 2 ^ 53) :
    gap f e p < slack e p := by
  have hb := entry_bounds (idx e p)
  have hd := den_pos e p
  have hle : den e p * product f e p ≤ exact f e p + f * 2 ^ 11 * den e p := by
    rw [exact, product]
    calc den e p * (f * 2 ^ 11 * tableEntry (idx e p))
        = f * 2 ^ 11 * (den e p * tableEntry (idx e p)) := by ring
      _ ≤ f * 2 ^ 11 * (num e p + den e p) := Nat.mul_le_mul_left _ hb.2
      _ = f * 2 ^ 11 * num e p + f * 2 ^ 11 * den e p := by ring
  have hslack : f * 2 ^ 11 * den e p < slack e p := by
    rw [slack]
    exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hd
  rw [gap]
  omega

/-- The exact value in the cleared scale, read off the product: the integral
    part and the 1/2 bit at their weights, plus what the guard bits leave
    unreported. This is the identity every comparison below is made against. -/
theorem exact_eq (f : ℕ) (e : ℤ) (p : ℕ) (hn : 1 ≤ shiftBits e p) :
    (exact f e p : ℤ) = 2 * halfStep e p * integral f e p
      + halfStep e p * half f e p + dev f e p := by
  have hsplit := product_split f e p hn
  have hgap : (den e p : ℤ) * product f e p = exact f e p + gap f e p := by
    exact_mod_cast gap_eq f e p
  have hstep : (den e p : ℤ) * 2 ^ shiftBits e p = 2 * halfStep e p := by
    have h := step_eq hn
    rw [step] at h
    exact_mod_cast h.symm
  have hhalf : (den e p : ℤ) * 2 ^ (shiftBits e p - 1) = halfStep e p := by
    rw [halfStep]
    push_cast
    ring
  have hprod : (den e p : ℤ) * product f e p
      = 2 * halfStep e p * integral f e p + halfStep e p * half f e p
        + den e p * tail f e p := by
    rw [show ((product f e p : ℤ)) = 2 ^ shiftBits e p * integral f e p
          + 2 ^ (shiftBits e p - 1) * half f e p + tail f e p from by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hsplit]
    linear_combination (integral f e p : ℤ) * hstep + (half f e p : ℤ) * hhalf
  rw [dev]
  linarith [hgap, hprod]

/-- What the guard bits leave unreported, bounded: less than half a step, and
    more than `-slack`, the bump being all that can put it negative. -/
theorem dev_bounds (f : ℕ) (e : ℤ) (p : ℕ) (hf : f < 2 ^ 53) :
    -(slack e p : ℤ) < dev f e p ∧ dev f e p < halfStep e p := by
  have hgap := gap_lt f e p hf
  have hup : den e p * tail f e p < halfStep e p := by
    rw [halfStep]
    exact Nat.mul_lt_mul_of_le_of_lt le_rfl (tail_lt f e p) (den_pos e p)
  rw [dev]
  omega

/-- A set sticky bit puts the exact value strictly above the midpoint the 1/2
    bit reports: the bits it saw are worth more than the bump could add. -/
theorem dev_pos_of_sticky (f : ℕ) (e : ℤ) (p : ℕ) (hf : f < 2 ^ 53)
    (h : sticky f e p = 1) : 0 < dev f e p := by
  have hgap := gap_lt f e p hf
  have htail : 2 ^ 64 ≤ tail f e p := by
    by_contra hlt
    exact absurd ((sticky_eq_zero_iff f e p).mpr (by omega)) (by omega)
  have hlo : slack e p ≤ den e p * tail f e p := by
    rw [slack]
    calc 2 ^ 64 * den e p = den e p * 2 ^ 64 := by ring
      _ ≤ den e p * tail f e p := Nat.mul_le_mul_left _ htail
  rw [dev]
  omega

/-! ## Crossing into ℚ

The specification is about rationals; everything above is about naturals. `step`
is the factor that clears the grid, and it sends the exact scaled value to
`exact`, so every distance the specification asks about is a distance of
integers. Only this section and the normalization below touch `ℚ`.
-/

/-- `step` sends the exact scaled value to the integer `exact`. -/
theorem value_scaled (f : ℕ) (e : ℤ) (p : ℕ) (hs : 3 ≤ pointShift e p) :
    value f e * 10 ^ (-decExp e p) * (step e p : ℚ) = (exact f e p : ℚ) := by
  set pe := binary64.power10Exponent (idx e p) with hpe
  have hd : (0 : ℚ) < (den e p : ℚ) := by
    exact_mod_cast den_pos e p
  -- The exact power of ten, cleared by its denominator.
  have hnum : (10 : ℚ) ^ idx e p * 2 ^ ((128 : ℤ) - pe) * (den e p : ℚ)
      = (num e p : ℚ) := by
    rw [show (128 : ℤ) = (binary64.p10Width : ℤ) from rfl, hpe,
      binary64.power10_exact_ratio, ← num, ← den,
      div_mul_cancel₀ _ (ne_of_gt hd)]
  -- The alignment spends the exponents the power of ten leaves, and what
  -- remains is the shift into the top of the product.
  have hen : (2 : ℚ) ^ e * 2 ^ (shiftBits e p : ℤ)
      = 2 ^ (11 : ℕ) * 2 ^ ((128 : ℤ) - pe) := by
    rw [← zpow_add₀ (two_ne_zero' ℚ),
      show ((2 : ℚ) ^ (11 : ℕ)) = 2 ^ (11 : ℤ) from by norm_num,
      ← zpow_add₀ (two_ne_zero' ℚ)]
    congr 1
    rw [shift_bits_eq hs, pointShift, ← hpe]
    ring
  have hstep : (step e p : ℚ) = (den e p : ℚ) * 2 ^ (shiftBits e p : ℤ) := by
    rw [step_eq (by have := shift_bits_ge hs; omega)]
    push_cast
    rw [zpow_natCast]
  rw [value, exact, show (-decExp e p) = idx e p from rfl, hstep]
  push_cast
  rw [← hnum]
  linear_combination ((f : ℚ) * 10 ^ idx e p * (den e p : ℚ)) * hen

/-- The same at the reround's grid: ten steps there is one step here. -/
theorem value_scaled_coarse (f : ℕ) (e : ℤ) (p : ℕ) (hs : 3 ≤ pointShift e p) :
    value f e * 10 ^ (-(decExp e p + 1)) * ((10 * step e p : ℕ) : ℚ)
      = (exact f e p : ℚ) := by
  have h := value_scaled f e p hs
  have h10 : (10 : ℚ) ^ (-(decExp e p + 1)) * 10 = 10 ^ (-decExp e p) := by
    rw [show -(decExp e p + 1) = -decExp e p - 1 from by ring,
      zpow_sub_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
    field_simp
  push_cast
  calc value f e * 10 ^ (-(decExp e p + 1)) * (10 * (step e p : ℚ))
      = value f e * ((10 : ℚ) ^ (-(decExp e p + 1)) * 10) * (step e p : ℚ) := by
        ring
    _ = (exact f e p : ℚ) := by rw [h10]; exact h

/-- A candidate within half a step of the exact value is correctly rounded on
    the grid at `k`, a candidate exactly half a step away having to be even.
    `m` is the scale that clears that grid; the rest is `core.lean`'s bridge. -/
theorem correctly_rounded_of_dist {f : ℕ} {e : ℤ} {p : ℕ} {d m : ℕ} {k : ℤ}
    (hm : 0 < m) (hx : value f e * 10 ^ (-k) * (m : ℚ) = (exact f e p : ℚ))
    (hle : -(m : ℤ) ≤ 2 * ((exact f e p : ℤ) - d * m)
      ∧ 2 * ((exact f e p : ℤ) - d * m) ≤ m)
    (heven : 2 * ((exact f e p : ℤ) - d * m) = m
      ∨ 2 * ((exact f e p : ℤ) - d * m) = -(m : ℤ) → d % 2 = 0) :
    CorrectlyRounded f e d k := by
  obtain ⟨hcmp, -, heq⟩ := scaled_cmp_of_int_eq (c := d) (m := m) (a := 2)
    (b := m) (t := (exact f e p : ℤ)) (dist := (exact f e p : ℤ) - d * m)
    (x := value f e * 10 ^ (-k)) (thr := 1 / 2) hm two_pos hx
    (by push_cast; ring) (by ring)
  push_cast at hcmp heq
  exact correctly_rounded_of_le_half f e d k (hcmp.mpr hle)
    fun h => heven (heq.mp h)

/-! ## The canonical packing

The two guard bits are not an approximation of the scaled value: they are its
canonical packing at the half step, and `packed_eq_exact_packed` below proves
that zmij computes exactly that. Everything the rounding needs follows from that
one identity, and follows generically — no exponent, precision or table enters
this section.

`demote_exact_packed` is why there is one rounding argument here rather than two.
A demoted packing is the packing at ten times the half step, so the reround's
grid is the reported grid with a coarser `G` and nothing else, and
`round_even_exact_packed` serves both.
-/

/-- The canonical packing of `x` at half step `G`: the half steps it covers,
    which the 1/2 bit's weight makes twice the count, and whether anything is
    left over. -/
def exactPacked (x G : ℕ) : ℕ := 2 * (x / G) + if x % G = 0 then 0 else 1

/-- `round_even`, off the two guard bits: it rounds up when they say the value
    is past the midpoint, and at the midpoint when what remains is odd. -/
theorem round_even_eq (i b : ℕ) (hb : b ≤ 3) :
    roundEven (4 * i + b)
      = i + if 2 ≤ b ∧ (b = 3 ∨ i % 2 = 1) then 1 else 0 := by
  rw [roundEven]
  split_ifs <;> omega

/-- `demote` sets the sticky bit unless what it drops is zero. -/
theorem demote_eq (x : ℕ) :
    demote x = if x % 10 = 0 then x / 10 else 2 * (x / 20) + 1 := by
  have hor (y : ℕ) : y ||| 1 = 2 * (y / 2) + 1 := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ j =>
      have hdiv : (y ||| 1) / 2 = y / 2 := by
        simpa [Nat.shiftRight_eq_div_pow] using
          (Nat.shiftRight_or_distrib (i := 1) (a := y) (b := 1))
      rw [Nat.testBit_succ, Nat.testBit_succ, hdiv,
        show (2 * (y / 2) + 1) / 2 = y / 2 from by omega]
  rw [demote]
  split_ifs
  · rw [Nat.or_zero]
  -- One division by a literal, which is what `omega` reads below.
  · rw [hor, Nat.div_div_eq_div_mul]

/-- A sticky bit as arithmetic, which is what `omega` reads. -/
private theorem stick_eq (r : ℕ) : (if r = 0 then 0 else 1) = min r 1 := by
  split_ifs <;> omega

/-- The packing read off a split of the value at the half step: `q` half steps
    and a remainder inside one. This is the only place the division in
    `exactPacked` is unfolded, and every packing below arrives through it. -/
private theorem exact_packed_split {x G q r : ℕ} (hG : 0 < G) (hr : r < G)
    (hx : x = r + G * q) : exactPacked x G = 2 * q + min r 1 := by
  rw [exactPacked, hx, Nat.add_mul_div_left _ _ hG, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hr, Nat.mod_eq_of_lt hr, stick_eq, Nat.zero_add]

/-- `demote` on a canonical packing, in terms of the half steps counted and the
    decimal digit that leaves: the digit joins the sticky bit. -/
private theorem demote_pack (Q d s : ℕ) (hd : d < 10) (hs : s ≤ 1) :
    demote (2 * (10 * Q + d) + s) = 2 * Q + min (2 * d + s) 1 := by
  rw [demote_eq]
  interval_cases d <;> interval_cases s <;> split_ifs <;> omega

/-- Demoting a canonical packing is the canonical packing at ten times the half
    step. The reported grid and the reround's are therefore the same packing,
    which is what collapses the two rounding arguments into one. -/
theorem demote_exact_packed (x G : ℕ) (hG : 0 < G) :
    demote (exactPacked x G) = exactPacked x (10 * G) := by
  have hrlt : x % G < G := Nat.mod_lt _ hG
  have hdlt : x / G % 10 < 10 := Nat.mod_lt _ (by omega)
  have hq : x / G = 10 * (x / G / 10) + x / G % 10 := (Nat.div_add_mod _ 10).symm
  -- The same value split at each step. The coarser split keeps the digit that
  -- leaves at its weight, and the two remainders together stay inside one
  -- coarser step.
  have hfine : x = x % G + G * (10 * (x / G / 10) + x / G % 10) := by
    rw [← hq]
    exact (Nat.mod_add_div x G).symm
  have hlt : G * (x / G % 10) + x % G < 10 * G := by
    have : G * (x / G % 10) ≤ G * 9 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hcoarse : x = G * (x / G % 10) + x % G + 10 * G * (x / G / 10) := by
    calc x = x % G + G * (10 * (x / G / 10) + x / G % 10) := hfine
      _ = G * (x / G % 10) + x % G + 10 * G * (x / G / 10) := by ring
  -- The coarse sticky bit is the digit that leaves, or else the fine one.
  have hstick : min (G * (x / G % 10) + x % G) 1
      = min (2 * (x / G % 10) + min (x % G) 1) 1 := by
    rcases Nat.eq_zero_or_pos (x / G % 10) with h1 | h1
    · rw [h1, Nat.mul_zero]
      omega
    · have : 0 < G * (x / G % 10) := Nat.mul_pos hG h1
      omega
  rw [exact_packed_split hG hrlt hfine, demote_pack _ _ _ hdlt (by omega),
    exact_packed_split (by omega) hlt hcoarse, hstick]

/-- Round-to-nearest-even off the two guard bits, over abstract integers: `G` is
    half a step, `dev` what the half step leaves, and `c` the increment the
    guard bits call for. Eight cases, each linear once the parities are
    literals; `omega` reads implications but not disjunctions, which is why the
    ties arrive as two implications and the parity is a case rather than a
    disjunct. -/
private theorem dist_bound {G dev : ℤ} {h s c i : ℕ} (hh : h ≤ 1) (hs : s ≤ 1)
    (hlo : -G < dev) (hhi : dev < G) (hsticky : s = 1 → 0 < dev)
    (htie : s = 0 → dev = 0)
    (hc : c = if h = 1 ∧ (s = 1 ∨ i % 2 = 1) then 1 else 0) :
    -G ≤ G * h + dev - 2 * G * c ∧ G * h + dev - 2 * G * c ≤ G
      ∧ (G * h + dev - 2 * G * c = G → (i + c) % 2 = 0)
      ∧ (G * h + dev - 2 * G * c = -G → (i + c) % 2 = 0) := by
  interval_cases h <;> interval_cases s <;>
    rcases show i % 2 = 0 ∨ i % 2 = 1 from by omega with hi | hi <;>
      rw [hi] at hc <;> norm_num at hc <;> subst hc <;> omega

/-- Rounding a canonical packing is round-to-nearest-even on the value packed:
    the candidate is at most half a step away, and exactly half a step away only
    when it is even. Nothing about Żmij enters, and both grids below read their
    bound off this one statement. -/
theorem round_even_exact_packed (x G : ℕ) (hG : 0 < G) :
    -(G : ℤ) ≤ (x : ℤ) - roundEven (exactPacked x G) * (2 * G)
      ∧ (x : ℤ) - roundEven (exactPacked x G) * (2 * G) ≤ G
      ∧ ((x : ℤ) - roundEven (exactPacked x G) * (2 * G) = G
          ∨ (x : ℤ) - roundEven (exactPacked x G) * (2 * G) = -(G : ℤ)
        → roundEven (exactPacked x G) % 2 = 0) := by
  have hrlt : x % G < G := Nat.mod_lt _ hG
  set s : ℕ := if x % G = 0 then 0 else 1 with hs
  have hsle : s ≤ 1 := by rw [hs]; split_ifs <;> omega
  set c : ℕ := if x / G % 2 = 1 ∧ (s = 1 ∨ x / G / 2 % 2 = 1) then 1 else 0
    with hc
  -- The candidate, off `round_even_eq` in the `4 * i + b` form it reads.
  have hround : roundEven (exactPacked x G) = x / G / 2 + c := by
    rw [show exactPacked x G = 4 * (x / G / 2) + (2 * (x / G % 2) + s) from by
        rw [exactPacked, ← hs]; omega,
      round_even_eq _ _ (by omega), hc]
    congr 1
    split_ifs <;> omega
  -- The distance, with the whole steps cancelled.
  have hdist : (x : ℤ) - (x / G / 2 + c : ℕ) * (2 * G)
      = G * (x / G % 2) + (x % G : ℕ) - 2 * G * c := by
    have hx : (x : ℤ) = G * (2 * (x / G / 2) + x / G % 2) + (x % G : ℕ) := by
      have h2 : 2 * (x / G / 2) + x / G % 2 = x / G := by omega
      exact_mod_cast
        (by rw [h2]; exact Nat.div_add_mod x G :
          G * (2 * (x / G / 2) + x / G % 2) + x % G = x).symm
    push_cast at hx ⊢
    linear_combination hx
  obtain ⟨hlo, hhi, hup, hdown⟩ := dist_bound (G := (G : ℤ))
    (dev := ((x % G : ℕ) : ℤ)) (h := x / G % 2) (s := s) (c := c)
    (i := x / G / 2) (by omega) hsle (by push_cast; omega)
    (by exact_mod_cast hrlt)
    (fun h1 => by rw [hs] at h1; split_ifs at h1; omega)
    (fun h0 => by rw [hs] at h0; split_ifs at h0; omega) hc
  rw [hround, hdist]
  exact ⟨hlo, hhi, fun htie => htie.elim hup hdown⟩

/-! ## An apparent tie is a real one

Everything the guard bits hide is under `slack`: the product bits they do not
see and the bump's excess both are. So the packed value can only mislead by
presenting a value near a half-step boundary as one exactly on it, and the
certificate says no significand does that.

With that settled the two directions meet — a clear sticky bit means `dev = 0`
and a set one means `dev > 0` — and `packed_eq_exact_packed` reads the invariant
off them. It is the last statement in this file about zmij's arithmetic; the
sections after it are about the packing alone.
-/

/-- A clear sticky bit leaves the exact value within `slack` of the boundary the
    guard bits report: the bits it hides are worth less than that, and so is the
    bump's excess. -/
theorem dev_near_of_sticky_eq_zero (f : ℕ) (e : ℤ) (p : ℕ) (hf : f < 2 ^ 53)
    (hsticky : sticky f e p = 0) :
    -(slack e p : ℤ) < dev f e p ∧ dev f e p < slack e p := by
  have hgap := gap_lt f e p hf
  have hup : den e p * tail f e p < slack e p := by
    rw [slack]
    calc den e p * tail f e p < den e p * 2 ^ 64 :=
          Nat.mul_lt_mul_of_le_of_lt le_rfl
            ((sticky_eq_zero_iff f e p).mp hsticky) (den_pos e p)
      _ = 2 ^ 64 * den e p := by ring
  rw [dev]
  omega

/-- What the certificate says: when the sticky bit is clear the exact value sits
    exactly on the half-step boundary the guard bits report. This is the one
    statement that makes an apparent tie a real one, at the reported grid and at
    the reround's alike, because `exact_eq` writes the exact value as a multiple
    of `halfStep` plus `dev` whatever the guard bits happen to say: the integral
    part counts the steps and the 1/2 bit the odd half-step. -/
theorem dev_eq_zero (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) (hsticky : sticky f e p = 0) : dev f e p = 0 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hn := shift_bits_ge hs.1
  have hsig := hin.sig
  have hnear := dev_near_of_sticky_eq_zero f e p hin.sig.2 hsticky
  have hcert := (tie_windows_refuted hin.exp hp).choose_spec
  have hbox : (tieWindows e p).f0 ≤ f ∧ f ≤ (tieWindows e p).f1 := by
    simp only [tieWindows]
    omega
  have hmod : 0 < (tieWindows e p).modulus := by
    have := den_pos e p
    simp only [tieWindows, halfStep]
    positivity
  set w : ℤ := (slack e p : ℤ) with hw
  have hmem₁ : (1 - w, (-1 : ℤ)) ∈ (tieWindows e p).windows := by
    simp [tieWindows, hw]
  have hmem₂ : ((1 : ℤ), w - 1) ∈ (tieWindows e p).windows := by
    simp [tieWindows, hw]
  -- The residue at the boundary is what the guard bits do not report.
  have hres : dev f e p = (tieWindows e p).g * f
      - (tieWindows e p).modulus * (2 * integral f e p + half f e p) := by
    have hex := exact_eq f e p (by omega)
    rw [exact] at hex
    simp only [tieWindows]
    push_cast at hex ⊢
    linarith
  rcases lt_trichotomy (dev f e p) 0 with hlt | heq | hgt
  · exact absurd hres fun h => (tieWindows e p).not_hit_rep f hmod hcert
      hmem₁ hbox.1 hbox.2 h (by omega) (by omega)
  · exact heq
  · exact absurd hres fun h => (tieWindows e p).not_hit_rep f hmod hcert
      hmem₂ hbox.1 hbox.2 h (by omega) (by omega)

/-- The invariant the whole file turns on: `scale` does not merely land near the
    exact scaled value, it computes that value's canonical packing at the half
    step. The two guard bits are the packing's, digit for digit — `exact_eq`
    places the integral part and the 1/2 bit, and `dev`, which the two lemmas
    above pin to zero exactly when the sticky bit is clear, is the remainder.

    Correctness of the rounding, and of the rounding after `demote`, are generic
    facts about that packing from here on. -/
theorem packed_eq_exact_packed (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    packed f e p = exactPacked (exact f e p) (halfStep e p) := by
  obtain ⟨hh, hst⟩ := guard_le_one f e p
  have hs := point_shift_bounds p (by simpa using hp) e (by simpa using hin.exp)
  have hex := exact_eq f e p (by have := shift_bits_ge hs.1; omega)
  have hdev := dev_bounds f e p hin.sig.2
  have hG := half_step_pos e p
  -- The remainder vanishes exactly with the sticky bit, which is the certificate
  -- one way round and the discarded low word's small size the other.
  have hiff : dev f e p = 0 ↔ sticky f e p = 0 :=
    ⟨fun h => by
       by_contra hne
       exact absurd (dev_pos_of_sticky f e p hin.sig.2 (by omega)) (by omega),
     dev_eq_zero f e hin p hp⟩
  have hnn : 0 ≤ dev f e p := by
    rcases show sticky f e p = 0 ∨ sticky f e p = 1 from by omega with h0 | h1
    · exact le_of_eq (hiff.mpr h0).symm
    · exact le_of_lt (dev_pos_of_sticky f e p hin.sig.2 h1)
  -- The remainder as a natural, so the division it settles is one of naturals.
  set r : ℕ := (dev f e p).toNat with hr
  have hrcast : (r : ℤ) = dev f e p := Int.toNat_of_nonneg hnn
  have hrlt : r < halfStep e p := by omega
  have hsplit : exact f e p
      = r + halfStep e p * (2 * integral f e p + half f e p) := by
    have : (exact f e p : ℤ)
        = r + halfStep e p * (2 * integral f e p + half f e p) := by
      rw [hrcast, hex]
      ring
    exact_mod_cast this
  rw [packed, exact_packed_split hG hrlt hsplit]
  have : r = 0 ↔ sticky f e p = 0 := by rw [← hiff]; omega
  omega

/-! ## Half a step

Both candidates are within half a step of the exact value, with a step of
whichever grid they are reported on. These two bounds are the whole of the
correctness argument, and with the packing identity in hand each is a line: the
reported grid reads `round_even_exact_packed` at the half step and the reround's
reads the same theorem at ten times it.
-/

/-- Half a step and one step, as integers. -/
private theorem step_cast (e : ℤ) (p : ℕ) :
    (step e p : ℤ) = 2 * (halfStep e p : ℤ) := by
  rw [step]
  push_cast
  ring

/-- The distance from the exact value to the significand `round_even` reports,
    in the cleared scale. -/
def fineDist (f : ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  (exact f e p : ℤ) - roundEven (packed f e p) * step e p

/-- And to the one the reround reports, on the grid ten times coarser. -/
def coarseDist (f : ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  (exact f e p : ℤ) - roundEven (demote (packed f e p)) * (10 * step e p)

/-- `round_even`'s candidate is within half a step, and exactly half a step away
    only when it is even. -/
theorem fine_within_half (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    -(halfStep e p : ℤ) ≤ fineDist f e p ∧ fineDist f e p ≤ halfStep e p
      ∧ (fineDist f e p = halfStep e p ∨ fineDist f e p = -(halfStep e p : ℤ)
        → roundEven (packed f e p) % 2 = 0) := by
  rw [fineDist, packed_eq_exact_packed f e hin p hp, step_cast]
  exact round_even_exact_packed _ _ (half_step_pos e p)

/-- The same for the reround's candidate, with a step of its own grid. The
    demoted packing is the reported one at ten times the half step, so this is
    the theorem above a second time. -/
theorem coarse_within_half (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    -(10 * (halfStep e p : ℤ)) ≤ coarseDist f e p
      ∧ coarseDist f e p ≤ 10 * halfStep e p
      ∧ (coarseDist f e p = 10 * halfStep e p
          ∨ coarseDist f e p = -(10 * (halfStep e p : ℤ))
        → roundEven (demote (packed f e p)) % 2 = 0) := by
  have hG := half_step_pos e p
  obtain ⟨hlo, hhi, hev⟩ :=
    round_even_exact_packed (exact f e p) (10 * halfStep e p) (by omega)
  push_cast at hlo hhi hev
  rw [coarseDist, packed_eq_exact_packed f e hin p hp,
    demote_exact_packed _ _ hG, step_cast]
  refine ⟨by linarith, by linarith, fun htie => hev (htie.imp ?_ ?_)⟩ <;>
    intro h <;> linarith

/-! ## Normalization

`to_decimal` picks the scale from the exponent alone, so the significand has to
fill its box before the call. `normalize` shifts it there and the exponent pays
the shift, which leaves the value alone; the value is all the specification
reads of the pair, so what holds of the normalized pair holds of the input.
-/

/-- `normalize` fills the significand's box: the leading bit goes to bit 52, and
    the shift that takes it there is at most 52, so the exponent it spends
    reaches no further than 52 below `emin`. -/
theorem normalized_of_finite {f : ℕ} {e : ℤ} (hin : binary64.Finite f e) :
    Normalized (f * 2 ^ normShift f) (e - normShift f) := by
  have hpos : 0 < f := hin.pos
  have hlt : f < 2 ^ 53 := hin.sig_lt
  have hne : f ≠ 0 := by omega
  have hlog : Nat.log2 f ≤ 52 := by
    have := (Nat.log2_lt hne).mpr hlt
    omega
  have hsum : Nat.log2 f + normShift f = 52 := by
    rw [normShift]
    omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · calc 2 ^ 52 = 2 ^ Nat.log2 f * 2 ^ normShift f := by rw [← pow_add, hsum]
      _ ≤ f * 2 ^ normShift f :=
        Nat.mul_le_mul_right _ (Nat.log2_self_le hne)
  · calc f * 2 ^ normShift f < 2 ^ (Nat.log2 f + 1) * 2 ^ normShift f :=
        Nat.mul_lt_mul_of_lt_of_le Nat.lt_log2_self le_rfl (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← pow_add]; congr 1; omega
  · have : -1074 ≤ e ∧ e ≤ 971 := hin.range
    rw [normShift]
    omega

/-- Normalizing leaves the value where it was: the significand's shift is the
    exponent's, the other way. -/
theorem value_normalized (f : ℕ) (e : ℤ) :
    value (f * 2 ^ normShift f) (e - normShift f) = value f e := by
  have h : ((2 : ℚ) ^ normShift f) * 2 ^ (e - (normShift f : ℤ)) = 2 ^ e := by
    rw [← zpow_natCast (2 : ℚ) (normShift f), ← zpow_add₀ (two_ne_zero' ℚ)]
    congr 1
    ring
  simp only [value]
  push_cast
  linear_combination (f : ℚ) * h

/-- So a candidate correctly rounded against the normalized pair is correctly
    rounded against the input, `CorrectlyRounded` reading the pair only through
    `value`. -/
theorem correctly_rounded_of_normalized {f : ℕ} {e : ℤ} {d : ℕ} {k : ℤ}
    (h : CorrectlyRounded (f * 2 ^ normShift f) (e - normShift f) d k) :
    CorrectlyRounded f e d k := by
  simpa only [CorrectlyRounded, value_normalized] using h

/-! ## Correctness

The reported significand is correctly rounded on the grid it is reported at,
which is `half a step` away from the specification and no more, and it has the
digits asked for, which is `grid_bounds` against the same half step. Both are
stated of the normalized pair, and `correct` carries them back to the input.
-/

/-- The scaled value, bounded by the digits asked for: at least `10^(p-1)` and
    below `2·10^p`, over the whole significand box. -/
theorem exact_bounds (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    10 ^ (p - 1) * step e p ≤ exact f e p
      ∧ exact f e p < 2 * 10 ^ p * step e p := by
  obtain ⟨hlo, hhi⟩ := grid_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hsig := hin.sig
  refine ⟨hlo.trans ?_, lt_of_le_of_lt ?_ hhi⟩
  · rw [exact]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsig.1)
  · rw [exact]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

/-- What `to_decimal` reports when the first rounding has the digits asked for,
    as the two components: `omega` reads a projection of a pair as an atom of
    its own, so the branches are taken apart here rather than at each use. -/
private theorem to_decimal_fine {f : ℕ} {e : ℤ} {p : ℕ}
    (hover : roundEven (packed f e p) < 10 ^ p) :
    (rounded f e p).1 = roundEven (packed f e p)
      ∧ (rounded f e p).2 = decExp e p := by
  constructor <;> simp [rounded, hover]

/-- And when it comes out one digit too long. -/
private theorem to_decimal_coarse {f : ℕ} {e : ℤ} {p : ℕ}
    (hover : ¬roundEven (packed f e p) < 10 ^ p) :
    (rounded f e p).1 = roundEven (demote (packed f e p))
      ∧ (rounded f e p).2 = decExp e p + 1 := by
  constructor <;> simp [rounded, hover]

/-- The reported significand has the digits asked for and is correctly rounded on
    the grid reported with it. One split on the reround settles both: the
    distance bound gives the rounding, and the same bound read against
    `exact_bounds` gives the digit count. -/
theorem rounded_correct (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    10 ^ (p - 1) ≤ (rounded f e p).1 ∧ (rounded f e p).1 < 10 ^ p
      ∧ CorrectlyRounded f e (rounded f e p).1 (rounded f e p).2 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hspos : 0 < step e p := step_pos e p
  have hstep := step_cast e p
  obtain ⟨hgridlo, hgridhi⟩ := exact_bounds f e hin p hp
  have hcast : ((10 ^ (p - 1) * step e p : ℕ) : ℤ)
      = (10 : ℤ) ^ (p - 1) * step e p := by push_cast; ring
  have hcast' : ((2 * 10 ^ p * step e p : ℕ) : ℤ)
      = 2 * (10 : ℤ) ^ p * step e p := by push_cast; ring
  have hlo : (10 : ℤ) ^ (p - 1) * step e p ≤ exact f e p := by
    rw [← hcast]
    exact_mod_cast hgridlo
  have hhi : (exact f e p : ℤ) < 2 * (10 : ℤ) ^ p * step e p := by
    rw [← hcast']
    exact_mod_cast hgridhi
  -- The fine bound serves both branches: the reround's lower digit bound comes
  -- from the significand it rerounds having had one digit too many.
  obtain ⟨hflo, hfhi, heven⟩ := fine_within_half f e hin p hp
  simp only [fineDist] at hflo hfhi heven
  by_cases hover : roundEven (packed f e p) < 10 ^ p
  · obtain ⟨hd, hk⟩ := to_decimal_fine hover
    rw [hd, hk]
    refine ⟨?_, hover, ?_⟩
    · -- Below `10^(p-1)` the candidate would be more than half a step short.
      by_contra hlt
      have h1 : (roundEven (packed f e p) : ℤ) + 1 ≤ (10 : ℤ) ^ (p - 1) := by
        have : roundEven (packed f e p) + 1 ≤ 10 ^ (p - 1) := by omega
        exact_mod_cast this
      have h2 : ((roundEven (packed f e p) : ℤ) + 1) * step e p
          ≤ (10 : ℤ) ^ (p - 1) * step e p :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have : (0 : ℤ) < halfStep e p := by omega
      linarith
    · exact correctly_rounded_of_dist hspos (value_scaled f e p hs.1)
        ⟨by omega, by omega⟩
        fun htie => heven (htie.imp (fun h => by omega) fun h => by omega)
  · obtain ⟨hclo, hchi, hceven⟩ := coarse_within_half f e hin p hp
    simp only [coarseDist] at hclo hchi hceven
    obtain ⟨hd, hk⟩ := to_decimal_coarse hover
    rw [hd, hk]
    -- The rerounded significand is a tenth of one that had `p + 1` digits.
    have hbig : (10 : ℤ) ^ p ≤ (roundEven (packed f e p) : ℤ) := by
      have : 10 ^ p ≤ roundEven (packed f e p) := by omega
      exact_mod_cast this
    have hbig' : (10 : ℤ) ^ p * step e p
        ≤ (roundEven (packed f e p) : ℤ) * step e p :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlt
      have h1 : (roundEven (demote (packed f e p)) : ℤ) + 1
          ≤ (10 : ℤ) ^ (p - 1) := by
        have : roundEven (demote (packed f e p)) + 1 ≤ 10 ^ (p - 1) := by omega
        exact_mod_cast this
      have h2 : ((roundEven (demote (packed f e p)) : ℤ) + 1) * (10 * step e p)
          ≤ (10 : ℤ) ^ (p - 1) * (10 * step e p) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h10 : (10 : ℤ) ^ (p - 1) * 10 = 10 ^ p := by
        rw [← pow_succ]
        congr 1
        omega
      have : (0 : ℤ) < halfStep e p := by omega
      nlinarith
    · by_contra hge
      have h1 : (10 : ℤ) ^ p ≤ (roundEven (demote (packed f e p)) : ℤ) := by
        have : 10 ^ p ≤ roundEven (demote (packed f e p)) := by omega
        exact_mod_cast this
      have h2 : (10 : ℤ) ^ p * (10 * step e p)
          ≤ (roundEven (demote (packed f e p)) : ℤ) * (10 * step e p) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have hppos : (1 : ℤ) ≤ (10 : ℤ) ^ p := one_le_pow₀ (by norm_num)
      nlinarith
    · exact correctly_rounded_of_dist (m := 10 * step e p) (by omega)
        (value_scaled_coarse f e p hs.1)
        ⟨by push_cast; omega, by push_cast; omega⟩
        fun htie => hceven (htie.imp (fun h => by push_cast at h; omega)
          fun h => by push_cast at h; omega)

/-- zmij converts a positive finite binary64 to a chosen precision correctly:
    the significand it reports has the digits asked for and is correctly rounded
    on the grid reported with it. -/
theorem correct (f : ℕ) (e : ℤ) (hfin : binary64.Finite f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    let (d, k) := toDecimal f e p
    10 ^ (p - 1) ≤ d ∧ d < 10 ^ p ∧ CorrectlyRounded f e d k :=
  have h := rounded_correct _ _ (normalized_of_finite hfin) p hp
  ⟨h.1, h.2.1, correctly_rounded_of_normalized h.2.2⟩

end zmij.precision
