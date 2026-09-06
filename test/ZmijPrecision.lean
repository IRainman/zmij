-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import Core
-- `Finset.Icc` over ℕ, which the sweeps over the precision need.
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! # Correctness of Żmij's fixed-precision conversion

`Zmij.lean` proves the shortest path correct. This file proves the other one:
the `to_decimal` overload that takes a precision, which rounds to a digit count
the caller picks, together with the `normalize` a caller runs first. The two
share the power-of-ten table and nothing else. There is no shortest
representation to select here, so `Core.lean`'s selection rule plays no part;
what has to hold is that the reported significand has the digits asked for and
is correctly rounded on the grid reported with it, which is `correct`.

`normalize` brings the significand's leading bit up to bit 52, which
`to_decimal` needs because it picks the scale from the exponent alone. zmij's
callers run it, for a subnormal only; folding it in here is what lets `correct`
speak of a binary64 value rather than of an already-shifted significand.

The conversion keeps every product bit returned by `umul192_hi128`: an integral
part and a retained fractional remainder, with only the low 64 product bits
discarded. `roundFine` compares that remainder directly with one half. If the
result has one digit too many, `roundCoarse` compares the integral part's last
decimal digit with five and rounds directly on the grid ten times coarser.

The table entry is the truncated 128-bit significand of `10^k` with one added,
so the computed value never falls below the exact one. The bump and the
discarded low product word together are worth less than one retained fraction
unit. A strict retained comparison therefore cannot be reversed. At apparent
ties, `tie_windows_refuted` rules out every nonzero displacement over every
significand of every (exponent, precision) pair, so the apparent boundary is an
exact one.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`; only `toDecimal`
  takes them unnormalized, everything under it is the normalized pair;
* `p`: the number of significant digits asked for;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`;
* `n`: `shiftBits e p`, the product bits below the integral part.

The scaled value is `exact f e p / step e p`, and everything between the
arithmetic and the specification is a comparison of integers in that scale.
`exact_split` is the identity it all rests on: the integral part at one whole
step, plus the retained fraction and the exact displacement left by the table
bump and discarded low word.

## Dependencies

    correct
      ← normalized_of_finite
      ← correctly_rounded_of_normalized
          ← value_normalized
      ← rounded_correct
          ← round_fine_nearest
          ← round_coarse_nearest
              ← exact_split
              ← the certificates, through `deviation`
          ← exact_bounds                (the digit count)
          ← value_scaled                (the crossing into ℚ)

## Why it is not in the default build

The checks below run for about two minutes. Nothing else depends on this file,
so it is a `lean_lib` of its own, absent from `defaultTargets`: `lake build` is
unaffected and `lake build ZmijPrecision` is the explicit request to verify
the fixed-precision path.

## What the two minutes are spent on

|  | count | cost |
|---|---|---|
| `point_shift_bounds` | 37,764 pairs | 12s |
| `grid_bounds` | 37,764 pairs | 21s |
| `pair_refuted` | 37,764 certificates | ~95s |

As in `YY128.lean` and `YY80.lean` the multiplier is found by
`ModWindows.search` during elaboration and only the literal reaches the proof
term. The certificates are the bulk of the cost even so, and they spend it on
elaboration rather than in the kernel: 37,764 goals, against the 2098 exponents
`Zmij.lean` splits.
-/

namespace ZmijPrecision

set_option maxHeartbeats 0

-- The sweeps fold over lists of tens of thousands of entries, well past the
-- default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## Żmij's fixed-precision conversion

One 192-bit multiply of the shifted significand by the 128-bit power of ten,
with the integral and retained fractional parts read out of the product. The
definitions below name those pieces and the shift that fills the significand's
box before either is read.
-/

/-- The decimal exponent of the grid the digits are asked for: the exponent of
    the leading digit, which zmij's `compute_dec_exp` estimates from the
    exponent of the value's top bit, less the `p - 1` digits that follow it. -/
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
    condition on the index. It is the single number zmij's two words denote, and
    everything below reads it as one; zmij adds its one to the low word, where
    over the indices reached it fits. -/
def tableEntry (k : ℤ) : ℕ :=
  binary64.power10Num k / binary64.power10Den k + 1

/-- The 192-bit product, `(bin_sig << 11) · pow10`. -/
def product (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := f * 2 ^ 11 * tableEntry (idx e p)

/-- The integral part of the scaled value, `p.hi >> point_shift`. -/
def integral (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := product f e p / 2 ^ shiftBits e p

/-- Number of retained fraction values in one integral step. -/
def fractionUnit (e : ℤ) (p : ℕ) : ℕ := 2 ^ (shiftBits e p - 64)

/-- The retained fraction at one half. -/
def fractionHalf (e : ℤ) (p : ℕ) : ℕ := 2 ^ (shiftBits e p - 65)

/-- Product bits below the integral part and above the discarded low word. -/
def fraction (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  product f e p / 2 ^ 64 % fractionUnit e p

/-- The discarded low product word. -/
def low (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := product f e p % 2 ^ 64

/-- Round the retained fixed-point value to the nearest integer, ties to even. -/
def roundFine (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  let i := integral f e p
  let r := fraction f e p
  i + if fractionHalf e p < r ∨
      (r = fractionHalf e p ∧ i % 2 = 1) then 1 else 0

/-- Round the same retained value directly on the grid ten times coarser. -/
def roundCoarse (f : ℕ) (e : ℤ) (p : ℕ) : ℕ :=
  let i := integral f e p
  let q := i / 10
  let a := i % 10
  q + if 5 < a ∨
      (a = 5 ∧ (fraction f e p ≠ 0 ∨ q % 2 = 1)) then 1 else 0

/-- The rounding itself on a normalized significand. The fine candidate is
    computed first; if it has one digit too many, the retained value is rounded
    directly on the grid ten times coarser. -/
def rounded (f : ℕ) (e : ℤ) (p : ℕ) : ℕ × ℤ :=
  let d := roundFine f e p
  if d < 10 ^ p then (d, decExp e p)
  else (roundCoarse f e p, decExp e p + 1)

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

/-! ## The integer scale

Scaled by `10^(-k)`, the reported grid becomes the integers and the exact value
becomes `exact / step`. `step` is the factor that takes it there: the power of
ten's denominator times the product's alignment. Every comparison below is
between integers in that scale, and `halfStep` is the distance a correctly
rounded significand must stay within.
-/

/-- Half a step of the reported grid, in integers. -/
def halfStep (e : ℤ) (p : ℕ) : ℕ := den e p * 2 ^ (shiftBits e p - 1)

/-- One step of the reported grid in integers: the scale that takes it there. -/
def step (e : ℤ) (p : ℕ) : ℕ := 2 * halfStep e p

/-- The exact scaled value, in integers: `f·2^e·10^(-k)·step`. -/
def exact (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := f * 2 ^ 11 * num e p

/-- What the discarded low word can be worth, in integers: the bump puts the
    entry at most one above the exact ratio, which the shifted significand
    scales by under `2^64`. -/
def slack (e : ℤ) (p : ℕ) : ℕ := 2 ^ 64 * den e p

/-- What the bump added, in integers and scaled by the significand: the
    difference between the product zmij formed and the exact one. -/
def gap (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := den e p * product f e p - exact f e p

/-- Exact displacement from the boundary represented by the retained product. -/
def deviation (f : ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  den e p * low f e p - gap f e p

/-- Exact fractional part below `integral`, in the integer scale. -/
def residual (f : ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  slack e p * fraction f e p + deviation f e p

/-! ## Finite checks

Two cheap sweeps — where the product is read, and that the scaled value has the
digits asked for — and then the two certificate families, which are the reason
for the wait.
-/

/-- Where `scale` reads the product. `point_shift` staying in `[3, 62]` is what
    makes zmij's two shifts and its mask well defined, and it leaves `n` far
    above 65, which is what keeps the discarded low word inside half a step. -/
theorem point_shift_bounds : ∀ p ∈ Finset.Icc 1 18,
    ∀ e ∈ Finset.Icc (-1126 : ℤ) 971,
      3 ≤ pointShift e p ∧ pointShift e p ≤ 62 := by
  -- `+kernel` keeps the enumeration out of the elaborator, whose recursion and
  -- exponentiation guards it would otherwise trip. So for the sweep below.
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
    significand there would make a retained boundary look exact when it is not,
    and that is the only way a direct tie decision can be wrong.

    The modulus is half a step rather than a step, which is what lets `0` stand
    for either kind of boundary: the reported grid's midpoints are the odd
    multiples of `halfStep` and the reround's grid points the even ones. -/
def tieWindows (e : ℤ) (p : ℕ) : ModWindows where
  n := 2 ^ 11 * num e p
  m := halfStep e p
  fmin := 2 ^ 52
  fmax := 2 ^ 53 - 1
  windows :=
    let w : ℤ := slack e p
    [(1 - w, -1), (1, w - 1)]

/-! ### Modular certificates

`modCertTactic` reads one integer literal out of the goal and runs the search on
it during elaboration, so the two indices have to arrive as one: `pairIndex`
packs them, eighteen precisions to the exponent, and the family below unpacks
them. A sweep over the packed index is then the same one variable
`interval_cases` splits in `YY128.lean` and `YY80.lean`.

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

/-- No significand puts the exact value in a nonzero ambiguous boundary window.
    The multiplier is searched for during elaboration and checked by the kernel,
    so a bad one would be a failed proof rather than an unsound one. -/
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

The product, split into the integral part, retained fraction, and discarded low
word, and the exact value recovered from that split. `exact_split` is where the
two meet.
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

private theorem pow64_mul_fraction_unit {e : ℤ} {p : ℕ}
    (hn : 64 ≤ shiftBits e p) :
    2 ^ 64 * fractionUnit e p = 2 ^ shiftBits e p := by
  rw [fractionUnit, ← pow_add]
  congr 1
  omega

private theorem fraction_unit_eq_two_mul_half {e : ℤ} {p : ℕ}
    (hn : 65 ≤ shiftBits e p) :
    fractionUnit e p = 2 * fractionHalf e p := by
  rw [fractionUnit, fractionHalf,
    show shiftBits e p - 64 = (shiftBits e p - 65) + 1 by omega, pow_succ]
  ring

private theorem fraction_unit_pos (e : ℤ) (p : ℕ) :
    0 < fractionUnit e p := by
  rw [fractionUnit]
  positivity

private theorem fraction_half_pos (e : ℤ) (p : ℕ) :
    0 < fractionHalf e p := by
  rw [fractionHalf]
  positivity

private theorem fraction_lt_unit (f : ℕ) (e : ℤ) (p : ℕ) :
    fraction f e p < fractionUnit e p := by
  rw [fraction]
  exact Nat.mod_lt _ (fraction_unit_pos e p)

private theorem retained_quotient (f : ℕ) (e : ℤ) (p : ℕ)
    (hn : 64 ≤ shiftBits e p) :
    product f e p / 2 ^ 64 / fractionUnit e p = integral f e p := by
  rw [Nat.div_div_eq_div_mul, pow64_mul_fraction_unit hn, integral]

/-- Split the product into its integral part, retained fraction, and low word. -/
theorem product_split (f : ℕ) (e : ℤ) (p : ℕ)
    (hn : 64 ≤ shiftBits e p) :
    product f e p =
      2 ^ shiftBits e p * integral f e p
        + 2 ^ 64 * fraction f e p + low f e p := by
  calc
    product f e p =
        2 ^ 64 * (product f e p / 2 ^ 64) + low f e p := by
      rw [low]
      exact (Nat.div_add_mod _ _).symm
    _ = 2 ^ 64 *
          (fractionUnit e p * integral f e p + fraction f e p)
          + low f e p := by
      rw [← (Nat.div_add_mod
        (product f e p / 2 ^ 64) (fractionUnit e p)),
        retained_quotient f e p hn, fraction]
    _ = 2 ^ shiftBits e p * integral f e p
          + 2 ^ 64 * fraction f e p + low f e p := by
      rw [← pow64_mul_fraction_unit hn]
      ring

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

/-- What the bump added: the product zmij formed, in integers, is the exact
    value plus `gap`. -/
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

/-- The exact value split at the same two positions as the retained product. -/
theorem exact_split (f : ℕ) (e : ℤ) (p : ℕ)
    (hn : 64 ≤ shiftBits e p) :
    (exact f e p : ℤ) =
      step e p * integral f e p + residual f e p := by
  have hp := product_split f e p hn
  have hg : (den e p : ℤ) * product f e p = exact f e p + gap f e p := by
    exact_mod_cast gap_eq f e p
  have hs : (step e p : ℤ) = den e p * 2 ^ shiftBits e p := by
    exact_mod_cast step_eq (by omega : 1 ≤ shiftBits e p)
  calc
    (exact f e p : ℤ) = den e p * product f e p - gap f e p := by
      linarith
    _ = den e p *
          (2 ^ shiftBits e p * integral f e p
            + 2 ^ 64 * fraction f e p + low f e p) - gap f e p := by
      rw [hp]
      push_cast
      rfl
    _ = step e p * integral f e p + residual f e p := by
      rw [residual, deviation, slack]
      push_cast
      rw [hs]
      ring

private theorem slack_mul_fraction_unit {e : ℤ} {p : ℕ}
    (hn : 64 ≤ shiftBits e p) :
    slack e p * fractionUnit e p = step e p := by
  rw [slack, step_eq (by omega : 1 ≤ shiftBits e p), ← pow64_mul_fraction_unit hn]
  ring

private theorem slack_mul_fraction_half {e : ℤ} {p : ℕ}
    (hn : 65 ≤ shiftBits e p) :
    slack e p * fractionHalf e p = halfStep e p := by
  have hpow : 2 ^ 64 * 2 ^ (shiftBits e p - 65)
      = 2 ^ (shiftBits e p - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [slack, fractionHalf, halfStep, ← hpow]
  ring

private theorem deviation_bounds (f : ℕ) (e : ℤ) (p : ℕ)
    (hf : f < 2 ^ 53) :
    -(slack e p : ℤ) < deviation f e p
      ∧ deviation f e p < slack e p := by
  have hg := gap_lt f e p hf
  have hl : low f e p < 2 ^ 64 := by
    rw [low]
    exact Nat.mod_lt _ (by positivity)
  have hd := den_pos e p
  have hup : den e p * low f e p < slack e p := by
    calc
      den e p * low f e p < den e p * 2 ^ 64 :=
        (Nat.mul_lt_mul_left hd).mpr hl
      _ = slack e p := by rw [slack]; ring
  rw [deviation]
  omega

/-! ## Crossing into ℚ

The specification is about rationals; everything above is about naturals. `step`
is the factor that makes the grid the integers, and it sends the exact scaled
value to `exact`, so every distance the specification asks about is a distance
of integers. Only this section and the normalization below touch `ℚ`.
-/

/-- `step` sends the exact scaled value to the integer `exact`. -/
theorem value_scaled (f : ℕ) (e : ℤ) (p : ℕ) (hs : 3 ≤ pointShift e p) :
    value f e * 10 ^ (-decExp e p) * (step e p : ℚ) = (exact f e p : ℚ) := by
  set pe := binary64.power10Exponent (idx e p) with hpe
  have hd : (0 : ℚ) < (den e p : ℚ) := by
    exact_mod_cast den_pos e p
  -- The exact power of ten, multiplied through by its denominator.
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
    `scale` takes that grid to the integers; the rest is `Core.lean`'s
    bridge. -/
theorem correctly_rounded_of_dist {f : ℕ} {e : ℤ} {p : ℕ} {d scale : ℕ} {k : ℤ}
    (hscale : 0 < scale)
    (hx : value f e * 10 ^ (-k) * (scale : ℚ) = (exact f e p : ℚ))
    (hle : -(scale : ℤ) ≤ 2 * ((exact f e p : ℤ) - d * scale)
      ∧ 2 * ((exact f e p : ℤ) - d * scale) ≤ scale)
    (heven : 2 * ((exact f e p : ℤ) - d * scale) = scale
      ∨ 2 * ((exact f e p : ℤ) - d * scale) = -(scale : ℤ) → d % 2 = 0) :
    CorrectlyRounded f e d k := by
  obtain ⟨hcmp, -, heq⟩ := scaled_cmp_of_int_eq (c := d) (scale := scale)
    (a := 2) (b := scale) (x' := (exact f e p : ℤ))
    (dist := (exact f e p : ℤ) - d * scale) (x := value f e * 10 ^ (-k))
    (thr := 1 / 2) hscale two_pos hx (by push_cast; ring) (by ring)
  push_cast at hcmp heq
  exact correctly_rounded_of_le_half f e d k (hcmp.mpr hle)
    fun h => heven (heq.mp h)

/-! ## Apparent retained boundaries are exact -/

private theorem deviation_eq_zero_of_boundary
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18)
    (hboundary :
      fraction f e p = 0 ∨ fraction f e p = fractionHalf e p) :
    deviation f e p = 0 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 65 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hsig := hnorm.sig
  obtain ⟨hlo, hhi⟩ := deviation_bounds f e p hnorm.sig.2
  have hex := exact_split f e p (by omega)
  have hh := slack_mul_fraction_half (e := e) (p := p) hn
  have hh' : (slack e p : ℤ) * fractionHalf e p = halfStep e p := by
    exact_mod_cast hh
  have hstep : (step e p : ℤ) = 2 * halfStep e p := by
    rw [step]
    push_cast
    ring
  have hnexact : ((tieWindows e p).n : ℤ) * f = exact f e p := by
    simp only [tieWindows, exact]
    push_cast
    ring
  have hmhalf : ((tieWindows e p).m : ℤ) = halfStep e p := by
    simp only [tieWindows]
  obtain hzero | hhalf := hboundary
  · rw [residual, hzero, Nat.cast_zero, mul_zero, zero_add] at hex
    have hres : deviation f e p = (tieWindows e p).n * f
        - (tieWindows e p).m * (2 * integral f e p) := by
      calc
        deviation f e p =
            exact f e p - step e p * integral f e p := by linarith
        _ = exact f e p - halfStep e p * (2 * integral f e p) := by
          rw [hstep]
          ring
        _ = (tieWindows e p).n * f
              - (tieWindows e p).m * (2 * integral f e p) := by
          rw [hnexact, hmhalf]
    have hm : 0 < (tieWindows e p).m := by
      simpa only [tieWindows] using half_step_pos e p
    have hcert := (tie_windows_refuted hnorm.exp hp).choose_spec
    have hfmin : (tieWindows e p).fmin ≤ f := by
      simp only [tieWindows]
      omega
    have hfmax : f ≤ (tieWindows e p).fmax := by
      simp only [tieWindows]
      omega
    rcases lt_trichotomy (deviation f e p) 0 with hneg | hzero' | hpos
    · exact ((tieWindows e p).not_hit_rep f hm hcert
        (rmin := 1 - (slack e p : ℤ)) (rmax := -1) (by simp [tieWindows])
        hfmin hfmax hres (by omega) (by omega)).elim
    · exact hzero'
    · exact ((tieWindows e p).not_hit_rep f hm hcert
        (rmin := 1) (rmax := (slack e p : ℤ) - 1) (by simp [tieWindows])
        hfmin hfmax hres (by omega) (by omega)).elim
  · rw [residual, hhalf] at hex
    rw [hh'] at hex
    have hres : deviation f e p = (tieWindows e p).n * f
        - (tieWindows e p).m * (2 * integral f e p + 1) := by
      calc
        deviation f e p =
            exact f e p - step e p * integral f e p - halfStep e p := by
          linarith
        _ = exact f e p
              - halfStep e p * (2 * integral f e p + 1) := by
          rw [hstep]
          ring
        _ = (tieWindows e p).n * f
              - (tieWindows e p).m * (2 * integral f e p + 1) := by
          rw [hnexact, hmhalf]
    have hm : 0 < (tieWindows e p).m := by
      simpa only [tieWindows] using half_step_pos e p
    have hcert := (tie_windows_refuted hnorm.exp hp).choose_spec
    have hfmin : (tieWindows e p).fmin ≤ f := by
      simp only [tieWindows]
      omega
    have hfmax : f ≤ (tieWindows e p).fmax := by
      simp only [tieWindows]
      omega
    rcases lt_trichotomy (deviation f e p) 0 with hneg | hzero | hpos
    · exact ((tieWindows e p).not_hit_rep f hm hcert
        (rmin := 1 - (slack e p : ℤ)) (rmax := -1) (by simp [tieWindows])
        hfmin hfmax hres (by omega) (by omega)).elim
    · exact hzero
    · exact ((tieWindows e p).not_hit_rep f hm hcert
        (rmin := 1) (rmax := (slack e p : ℤ) - 1) (by simp [tieWindows])
        hfmin hfmax hres (by omega) (by omega)).elim

/-! ## The exact fractional remainder -/

private theorem residual_bounds
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    0 ≤ residual f e p ∧ residual f e p < step e p
      ∧ (residual f e p = 0 ↔ fraction f e p = 0) := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 64 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hdev := deviation_bounds f e p hnorm.sig.2
  have hrlt := fraction_lt_unit f e p
  have hC : 0 < slack e p := by
    rw [slack]
    exact Nat.mul_pos (by positivity) (den_pos e p)
  have hCU := slack_mul_fraction_unit (e := e) (p := p) hn
  by_cases hr0 : fraction f e p = 0
  · have hd0 := deviation_eq_zero_of_boundary f e hnorm p hp (Or.inl hr0)
    have hstep := step_pos e p
    simp [residual, hr0, hd0, hstep]
  · have hrpos : 1 ≤ fraction f e p := by omega
    have hlo : slack e p ≤ slack e p * fraction f e p :=
      by simpa using Nat.mul_le_mul_left (slack e p) hrpos
    have hnext : fraction f e p + 1 ≤ fractionUnit e p := by omega
    have hhi : slack e p * (fraction f e p + 1)
        ≤ slack e p * fractionUnit e p :=
      Nat.mul_le_mul_left (slack e p) hnext
    rw [residual]
    constructor
    · linarith
    constructor
    · linarith
    · constructor
      · intro hzero
        linarith
      · exact fun h => (hr0 h).elim

private theorem residual_lt_half_of_fraction_lt
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18)
    (hr : fraction f e p < fractionHalf e p) :
    residual f e p < halfStep e p := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 65 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hdev := deviation_bounds f e p hnorm.sig.2
  have hnext : fraction f e p + 1 ≤ fractionHalf e p := by omega
  have hmul : slack e p * (fraction f e p + 1)
      ≤ slack e p * fractionHalf e p :=
    Nat.mul_le_mul_left (slack e p) hnext
  have hh := slack_mul_fraction_half (e := e) (p := p) hn
  have hmul' : (slack e p : ℤ) * (fraction f e p + 1)
      ≤ slack e p * fractionHalf e p := by
    exact_mod_cast hmul
  have hh' : (slack e p : ℤ) * fractionHalf e p = halfStep e p := by
    exact_mod_cast hh
  rw [residual]
  linarith

private theorem residual_eq_half_of_fraction_eq
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18)
    (hr : fraction f e p = fractionHalf e p) :
    residual f e p = halfStep e p := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 65 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hd0 :=
    deviation_eq_zero_of_boundary f e hnorm p hp (Or.inr hr)
  have hh := slack_mul_fraction_half (e := e) (p := p) hn
  rw [residual, hr, hd0, add_zero]
  exact_mod_cast hh

private theorem half_lt_residual_of_half_lt_fraction
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18)
    (hr : fractionHalf e p < fraction f e p) :
    halfStep e p < residual f e p := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 65 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hdev := deviation_bounds f e p hnorm.sig.2
  have hnext : fractionHalf e p + 1 ≤ fraction f e p := by omega
  have hmul : slack e p * (fractionHalf e p + 1)
      ≤ slack e p * fraction f e p :=
    Nat.mul_le_mul_left (slack e p) hnext
  have hh := slack_mul_fraction_half (e := e) (p := p) hn
  have hmul' : (slack e p : ℤ) * (fractionHalf e p + 1)
      ≤ slack e p * fraction f e p := by
    exact_mod_cast hmul
  have hh' : (slack e p : ℤ) * fractionHalf e p = halfStep e p := by
    exact_mod_cast hh
  rw [residual]
  linarith

/-! ## Direct rounding -/

/-- The fine candidate is nearest on the requested grid, ties to even. -/
theorem round_fine_nearest
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    -(halfStep e p : ℤ)
        ≤ (exact f e p : ℤ) - roundFine f e p * step e p
      ∧ (exact f e p : ℤ) - roundFine f e p * step e p
        ≤ halfStep e p
      ∧ ((exact f e p : ℤ) - roundFine f e p * step e p = halfStep e p
          ∨ (exact f e p : ℤ) - roundFine f e p * step e p
              = -(halfStep e p : ℤ)
        → roundFine f e p % 2 = 0) := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 64 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hex := exact_split f e p hn
  obtain ⟨hv0, hvstep, -⟩ := residual_bounds f e hnorm p hp
  have hstep : (step e p : ℤ) = 2 * halfStep e p := by
    rw [step]
    push_cast
    ring
  rcases lt_trichotomy (fraction f e p) (fractionHalf e p) with
      hr | hr | hr
  · have hvh := residual_lt_half_of_fraction_lt f e hnorm p hp hr
    have hd : roundFine f e p = integral f e p := by
      simp [roundFine, show ¬(fractionHalf e p < fraction f e p ∨
        fraction f e p = fractionHalf e p ∧ integral f e p % 2 = 1) by omega]
    rw [hd]
    have hdist : (exact f e p : ℤ) - integral f e p * step e p
        = residual f e p := by rw [hex]; ring
    rw [hdist]
    refine ⟨by linarith, by linarith, ?_⟩
    intro htie
    rcases htie with htie | htie <;> linarith
  · have hvh := residual_eq_half_of_fraction_eq f e hnorm p hp hr
    rcases Nat.mod_two_eq_zero_or_one (integral f e p) with hpar | hpar
    · have hd : roundFine f e p = integral f e p := by
        simp [roundFine, hr, hpar]
      rw [hd]
      have hdist : (exact f e p : ℤ) - integral f e p * step e p
          = residual f e p := by rw [hex]; ring
      rw [hdist, hvh]
      exact ⟨by linarith, le_rfl, fun _ => hpar⟩
    · have hd : roundFine f e p = integral f e p + 1 := by
        simp [roundFine, hr, hpar]
      rw [hd]
      have hdist : (exact f e p : ℤ)
          - (integral f e p + 1 : ℕ) * step e p
          = residual f e p - step e p := by rw [hex]; push_cast; ring
      rw [hdist, hvh, hstep]
      refine ⟨by linarith, by linarith, fun _ => ?_⟩
      omega
  · have hvh := half_lt_residual_of_half_lt_fraction f e hnorm p hp hr
    have hd : roundFine f e p = integral f e p + 1 := by
      simp [roundFine, hr]
    rw [hd]
    have hdist : (exact f e p : ℤ)
        - (integral f e p + 1 : ℕ) * step e p
        = residual f e p - step e p := by rw [hex]; push_cast; ring
    rw [hdist]
    refine ⟨by linarith, by linarith, ?_⟩
    intro htie
    rcases htie with htie | htie <;> linarith

/-- The coarse candidate is nearest on the grid ten times coarser, ties to
    even. -/
theorem round_coarse_nearest
    (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    -(5 * step e p : ℤ)
        ≤ (exact f e p : ℤ) - roundCoarse f e p * (10 * step e p)
      ∧ (exact f e p : ℤ) - roundCoarse f e p * (10 * step e p)
        ≤ 5 * step e p
      ∧ ((exact f e p : ℤ)
            - roundCoarse f e p * (10 * step e p) = 5 * step e p
          ∨ (exact f e p : ℤ)
              - roundCoarse f e p * (10 * step e p) = -(5 * step e p : ℤ)
        → roundCoarse f e p % 2 = 0) := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hn : 64 ≤ shiftBits e p := by
    have := shift_bits_ge hs.1
    omega
  have hex := exact_split f e p hn
  obtain ⟨hv0, hvstep, hvzero⟩ := residual_bounds f e hnorm p hp
  have hstep : 0 < step e p := step_pos e p
  set q := integral f e p / 10 with hq
  set a := integral f e p % 10 with ha_def
  set v := residual f e p with hv
  set c : ℕ := if 5 < a ∨
      (a = 5 ∧ (fraction f e p ≠ 0 ∨ q % 2 = 1)) then 1 else 0 with hc
  have ha : a < 10 := by
    rw [ha_def]
    exact Nat.mod_lt _ (by omega)
  have hi : integral f e p = 10 * q + a := by
    rw [hq, ha_def]
    exact (Nat.div_add_mod _ 10).symm
  have hd : roundCoarse f e p = q + c := by
    simp only [roundCoarse, ← hq, ← ha_def, ← hc]
  have hdist : (exact f e p : ℤ)
      - (q + c : ℕ) * (10 * step e p)
      = step e p * a + v - c * (10 * step e p) := by
    rw [hex]
    push_cast
    rw [hi]
    push_cast
    ring
  rw [hd, hdist]
  interval_cases a <;>
    by_cases hr0 : fraction f e p = 0 <;>
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar <;>
        simp [hc, hr0, hpar] at hvzero ⊢ <;> omega

/-! ## Normalization

`to_decimal` picks the scale from the exponent alone, so the significand has to
fill its box before the call. `normalize` shifts it there and the exponent pays
the shift, which leaves the value alone; the value is all the specification
reads of the pair, so what holds of the normalized pair holds of the input.
-/

/-- `normalize` fills the significand's box: the leading bit goes to bit 52, and
    the shift that takes it there is at most 52, so the exponent it spends
    reaches no further than 52 below `emin`. -/
theorem normalized_of_finite {f : ℕ} {e : ℤ} (hfin : binary64.Finite f e) :
    Normalized (f * 2 ^ normShift f) (e - normShift f) := by
  have hpos : 0 < f := hfin.pos
  have hlt : f < 2 ^ 53 := hfin.sig_lt
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
  · have : -1074 ≤ e ∧ e ≤ 971 := hfin.range
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

One bound settles both halves of the specification: the candidate is within half
a step of the exact value, with a step of whichever grid it is reported on. That
is `round_fine_nearest` or `round_coarse_nearest`, according to the branch.
Being correctly rounded is that bound carried into ℚ, and having the digits
asked for is that bound against `exact_bounds`. Both are stated of the
normalized pair, and `correct` carries them back to the input.
-/

/-- Half a step and one step, as integers. -/
private theorem step_cast (e : ℤ) (p : ℕ) :
    (step e p : ℤ) = 2 * (halfStep e p : ℤ) := by
  rw [step]
  push_cast
  ring

/-- A candidate within half a step of the value reaches every grid point the
    value is above: half a step is not enough to fall back over one. `h` is half
    the step, which is the form the direct rounding bounds come in. -/
private theorem le_of_dist_le {x d h lo : ℤ} (hh : 0 < h)
    (hd : x - d * (2 * h) ≤ h) (hx : (2 * lo - 1) * h < x) : lo ≤ d := by
  by_contra hlt
  have := mul_le_mul_of_nonneg_right (show d + 1 ≤ lo by omega) hh.le
  linarith

/-- And stays below every grid point the value stays half a step clear of. -/
private theorem lt_of_le_dist {x d h hi : ℤ} (hh : 0 < h)
    (hd : -h ≤ x - d * (2 * h)) (hx : x < (2 * hi - 1) * h) : d < hi := by
  by_contra hge
  have := mul_le_mul_of_nonneg_right (show hi ≤ d by omega) hh.le
  linarith

/-- The scaled value, bounded by the digits asked for: at least `10^(p-1)` and
    below `2·10^p`, over the whole significand box. -/
theorem exact_bounds (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    10 ^ (p - 1) * step e p ≤ exact f e p
      ∧ exact f e p < 2 * 10 ^ p * step e p := by
  obtain ⟨hlo, hhi⟩ := grid_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hsig := hnorm.sig
  refine ⟨hlo.trans ?_, lt_of_le_of_lt ?_ hhi⟩
  · rw [exact]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hsig.1)
  · rw [exact]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

private theorem rounded_fine {f : ℕ} {e : ℤ} {p : ℕ}
    (hover : roundFine f e p < 10 ^ p) :
    (rounded f e p).1 = roundFine f e p
      ∧ (rounded f e p).2 = decExp e p := by
  constructor <;> simp [rounded, hover]

private theorem rounded_coarse {f : ℕ} {e : ℤ} {p : ℕ}
    (hover : ¬roundFine f e p < 10 ^ p) :
    (rounded f e p).1 = roundCoarse f e p
      ∧ (rounded f e p).2 = decExp e p + 1 := by
  constructor <;> simp [rounded, hover]

/-- The fractional method reports `p` digits and rounds correctly on its
    reported grid. -/
theorem rounded_correct (f : ℕ) (e : ℤ) (hnorm : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    10 ^ (p - 1) ≤ (rounded f e p).1 ∧ (rounded f e p).1 < 10 ^ p
      ∧ CorrectlyRounded f e (rounded f e p).1 (rounded f e p).2 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hnorm.exp)
  have hstep := step_cast e p
  have hh : (0 : ℤ) < halfStep e p := by
    exact_mod_cast half_step_pos e p
  obtain ⟨hgridlo, hgridhi⟩ := exact_bounds f e hnorm p hp
  have hlo : (10 : ℤ) ^ (p - 1) * (2 * halfStep e p) ≤ exact f e p := by
    rw [← hstep]
    exact_mod_cast hgridlo
  have hhi : (exact f e p : ℤ)
      < 2 * (10 : ℤ) ^ p * (2 * halfStep e p) := by
    rw [← hstep]
    exact_mod_cast hgridhi
  obtain ⟨hflo, hfhi, hfeven⟩ := round_fine_nearest f e hnorm p hp
  have hflo' : -(halfStep e p : ℤ) ≤ (exact f e p : ℤ)
      - roundFine f e p * (2 * halfStep e p) := by
    rw [← hstep]
    exact hflo
  have hfhi' : (exact f e p : ℤ)
      - roundFine f e p * (2 * halfStep e p) ≤ halfStep e p := by
    rw [← hstep]
    exact hfhi
  have hfscale :
      -(step e p : ℤ)
          ≤ 2 * ((exact f e p : ℤ) - roundFine f e p * step e p)
        ∧ 2 * ((exact f e p : ℤ) - roundFine f e p * step e p)
          ≤ step e p := by
    constructor
    · calc
        -(step e p : ℤ) = 2 * (-(halfStep e p : ℤ)) := by rw [hstep]; ring
        _ ≤ 2 * ((exact f e p : ℤ) - roundFine f e p * step e p) :=
          mul_le_mul_of_nonneg_left hflo (by norm_num)
    · calc
        2 * ((exact f e p : ℤ) - roundFine f e p * step e p)
            ≤ 2 * halfStep e p :=
          mul_le_mul_of_nonneg_left hfhi (by norm_num)
        _ = step e p := by rw [hstep]
  by_cases hover : roundFine f e p < 10 ^ p
  · obtain ⟨hd, hk⟩ := rounded_fine hover
    rw [hd, hk]
    refine ⟨?_, hover, ?_⟩
    · exact_mod_cast le_of_dist_le (lo := (10 : ℤ) ^ (p - 1)) hh hfhi'
        (by linarith)
    · exact correctly_rounded_of_dist (step_pos e p)
        (value_scaled f e p hs.1)
        hfscale
        fun htie => hfeven (htie.imp
          (fun h => by linarith)
          fun h => by linarith)
  · obtain ⟨hd, hk⟩ := rounded_coarse hover
    rw [hd, hk]
    obtain ⟨hclo, hchi, hceven⟩ :=
      round_coarse_nearest f e hnorm p hp
    have hhalf : (5 * step e p : ℤ) = 10 * halfStep e p := by
      rw [hstep]
      ring
    have hclo' : -(10 * halfStep e p : ℤ)
        ≤ (exact f e p : ℤ)
          - roundCoarse f e p * (2 * (10 * halfStep e p)) := by
      calc
        -(10 * halfStep e p : ℤ) = -(5 * step e p : ℤ) := by rw [hhalf]
        _ ≤ (exact f e p : ℤ)
              - roundCoarse f e p * (10 * step e p) := hclo
        _ = (exact f e p : ℤ)
              - roundCoarse f e p * (2 * (10 * halfStep e p)) := by
          rw [hstep]
          ring
    have hchi' : (exact f e p : ℤ)
          - roundCoarse f e p * (2 * (10 * halfStep e p))
        ≤ 10 * halfStep e p := by
      calc
        (exact f e p : ℤ)
              - roundCoarse f e p * (2 * (10 * halfStep e p))
            = (exact f e p : ℤ)
              - roundCoarse f e p * (10 * step e p) := by
                rw [hstep]
                ring
        _ ≤ 5 * step e p := hchi
        _ = 10 * halfStep e p := hhalf
    have h10 : (10 : ℤ) ^ (p - 1) * (10 * halfStep e p)
        = 10 ^ p * halfStep e p := by
      rw [show (10 : ℤ) ^ p = 10 ^ (p - 1) * 10 from by
        rw [← pow_succ]
        congr 1
        omega]
      ring
    have hbig : (10 : ℤ) ^ p * (2 * halfStep e p)
        ≤ (roundFine f e p : ℤ) * (2 * halfStep e p) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_not_lt hover)
        (by linarith)
    have hone : (halfStep e p : ℤ) ≤ 10 ^ p * halfStep e p :=
      le_mul_of_one_le_left hh.le (one_le_pow₀ (by norm_num))
    refine ⟨?_, ?_, ?_⟩
    · have hdlo : (10 : ℤ) ^ (p - 1) ≤ roundCoarse f e p :=
        le_of_dist_le (lo := (10 : ℤ) ^ (p - 1))
          (by linarith) hchi' (by linarith)
      exact_mod_cast hdlo
    · have hdhi : (roundCoarse f e p : ℤ) < (10 : ℤ) ^ p :=
        lt_of_le_dist (hi := (10 : ℤ) ^ p)
          (by linarith) hclo' (by linarith)
      exact_mod_cast hdhi
    · exact correctly_rounded_of_dist (scale := 10 * step e p)
        (by have := step_pos e p; omega) (value_scaled_coarse f e p hs.1)
        ⟨
          calc
            -(10 * step e p : ℤ) = 2 * (-(5 * step e p : ℤ)) := by ring
            _ ≤ 2 * ((exact f e p : ℤ)
                - roundCoarse f e p * (10 * step e p)) :=
              mul_le_mul_of_nonneg_left hclo (by norm_num),
          calc
            2 * ((exact f e p : ℤ)
                - roundCoarse f e p * (10 * step e p))
                ≤ 2 * (5 * step e p) :=
              mul_le_mul_of_nonneg_left hchi (by norm_num)
            _ = (10 * step e p : ℤ) := by ring
        ⟩
        fun htie => hceven (htie.imp
          (fun h => by push_cast at h; linarith)
          fun h => by push_cast at h; linarith)

/-- Żmij converts a positive finite binary64 to a chosen precision correctly:
    the significand it reports has the digits asked for and is correctly rounded
    on the grid reported with it. -/
theorem correct (f : ℕ) (e : ℤ) (hfin : binary64.Finite f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    let (d, k) := toDecimal f e p
    10 ^ (p - 1) ≤ d ∧ d < 10 ^ p ∧ CorrectlyRounded f e d k :=
  (rounded_correct _ _ (normalized_of_finite hfin) p hp).imp_right
    (And.imp_right correctly_rounded_of_normalized)

end ZmijPrecision
