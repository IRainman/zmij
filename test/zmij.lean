-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import Mathlib.Algebra.Order.Floor.Semifield
import core

/-! # Correctness of Żmij

`core.lean` proves that an exact, Schubfach-like selection rule produces a
shortest, correctly rounded decimal whenever the decimal grid step is at most
one ULP and strictly greater than a tenth of one. This file proves that Żmij's
regular binary64 path implements that rule.

Żmij scales by `10^(-k-1)` rather than `10^(-k)`, an optimization by Xiang
JunBo: one multiply lands the *shorter* 15-16 digit candidate in the integral
part directly, with no division by ten, and the seventeenth digit is derived
from the fraction left over. So where yy computes a 17-digit significand and
trims a digit off it, Żmij computes the trimmed significand and appends a digit
only when it has to. Like yy and unlike Xiang's xjb64, Żmij uses truncated
power-of-ten significands.

That changes what has to be proved. Żmij's two coarse candidates are the
integral part and its successor, one unit apart on the grid at `k+1`, and its
two rounding flags say which of them lands within half a ULP. The fine
candidate is not a truncation at all but a rounded digit, so the tie rule that
yy wrote into a flag Żmij writes into a rounding constant.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`;
* `K`: the index `-k-1` of the power of ten Żmij multiplies by;
* `s`: the shift `exponentShift e`, aligning `f·2^e` with `10^K`.

Żmij makes three decisions, and each is an equivalence with a comparison of
naturals in the cleared scale of `## Żmij's arithmetic model`:

    round_down_iff_gap :  roundDown ↔ 2·zGap ≤ zNum
    round_up_iff_gap   :  roundUp   ↔ 2·zMul ≤ 2·zGap + zNum
    digit_nearest      :  |zDigitDist| ≤ zMul

The first two are strict for odd `f` and the third is not, which is each tie
rule written into its bound: the coarse candidates are ties in the binary
rounding interval, resolved by the parity of `f`, while a digit is a decimal
tie, resolved by the parity of the digit itself.

The coarse pair carries a second equivalence, on the other side:

    round_down_iff_roundtrips :  roundDown ↔ integralPart round-trips
    round_up_iff_roundtrips   :  roundUp   ↔ integralPart + 1 round-trips

The two boundaries mean different things and stay separate. `*_iff_gap` says the
finite-precision implementation reaches the correct exact decision;
`*_iff_roundtrips` connects the integer scale that decision is made in to the
semantic specification. Consumers read one direction or the other:
`coarse_output_roundtrips` uses `→`, `trim_of_coarse_roundtrip` uses `←`.

Both coarse candidates live on the grid at `k+1`, one unit apart. The reported
significand lives on the grid at `k`, ten times finer, where they become
multiples of ten and the derived digit fills the room between them. Relating the
two grids is all of `## The grid at k`.

## Dependencies

    correct
      ← ulp_scaled_bounds
      ← exact_candidate
          ← coarse_output_roundtrips
          ← fine_output_nearest
          ← trim_of_coarse_roundtrip

    coarse_output_roundtrips, trim_of_coarse_roundtrip
      ← round_down_iff_roundtrips, round_up_iff_roundtrips

    fine_output_nearest
      ← digit_nearest

`ulp_scaled_bounds` is the other thing `exact_candidate_correct` asks for: at
Żmij's exponent one ULP spans between one and ten grid steps, so the fine case
has a grid to be correctly rounded on.
-/

/-- Whether f·2^e is a regularly spaced positive binary64 value: a normal that
    is not a power of 2, or anything at the minimum exponent, subnormals
    included, there being no binade below to halve the spacing. -/
def Regular (f : ℕ) (e : ℤ) : Prop :=
  (0 < f ∧ f < 2 ^ 53 ∧ (2 ^ 52 < f ∨ e = -1074)) ∧
  (-1074 ≤ e ∧ e ≤ 971)

/-- A regular value has a positive significand. -/
theorem Regular.pos {f : ℕ} {e : ℤ} (hr : Regular f e) : 0 < f := hr.1.1

/-- A regular value has a significand below `2^53`. -/
theorem Regular.sig_lt {f : ℕ} {e : ℤ} (hr : Regular f e) : f < 2 ^ 53 :=
  hr.1.2.1

/-- A regular value's exponent lies in binary64's range. -/
theorem Regular.range {f : ℕ} {e : ℤ} (hr : Regular f e) :
    -1074 ≤ e ∧ e ≤ 971 := hr.2

/-! ## The power of ten

The table Żmij multiplies by, as a truncated 128-bit significand with a
fixed-point exponent. Nothing here is specific to Żmij: it is the same
normalized table yy uses, read at a different index.
-/

/-- Binary exponent of 10^k used to normalize its 128-bit significand: the
    fixed-point form of `⌊k·log₂10⌋ + 1`. Taking a logarithm here instead would
    make every exponent-wise check below shift a 1077-bit number down to zero
    one bit at a time. -/
def power10Exponent (k : ℤ) : ℤ :=
  k * 217_707 / 2 ^ 16 + 1

/-- Truncated 128-bit normalized binary significand of 10^k. -/
def power10Significand (k : ℤ) : ℕ :=
  ⌊(10 : ℚ) ^ k * 2 ^ (128 - power10Exponent k)⌋₊

/-- Numerator of the exact scaled power of ten `10^k·2^(128-pe)`, with negative
    exponents moved to the denominator. Writing the power as a ratio of naturals
    turns the truncation into a single `Nat` division, so the exponent-wise
    checks below can run in the kernel. -/
def power10Num (k : ℤ) : ℕ :=
  10 ^ k.toNat * 2 ^ (128 - power10Exponent k).toNat

/-- Denominator of that same power of ten, carrying the negative exponents. -/
def power10Den (k : ℤ) : ℕ :=
  10 ^ (-k).toNat * 2 ^ (power10Exponent k - 128).toNat

theorem power10_den_pos (k : ℤ) : 0 < power10Den k := by
  rw [power10Den]; positivity

/-- The scaled exact power of ten is exactly the rational `num / den`. -/
theorem power10_exact_ratio (k : ℤ) :
    (10 : ℚ) ^ k * 2 ^ (128 - power10Exponent k)
      = (power10Num k : ℚ) / (power10Den k : ℚ) := by
  set pe := power10Exponent k
  have hden : (power10Den k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (power10_den_pos k).ne'
  -- Each pair of exponents in the ratio adds up to the truncated one.
  have hk : k + ((-k).toNat : ℤ) = (k.toNat : ℤ) := by omega
  have hpe : 128 - pe + ((pe - 128).toNat : ℤ) = ((128 - pe).toNat : ℤ) := by
    omega
  rw [eq_div_iff hden, power10Num, power10Den]
  push_cast
  rw [← zpow_natCast (10 : ℚ) (-k).toNat,
    ← zpow_natCast (2 : ℚ) (pe - 128).toNat,
    ← zpow_natCast (10 : ℚ) k.toNat, ← zpow_natCast (2 : ℚ) (128 - pe).toNat,
    show (10 : ℚ) ^ k * 2 ^ (128 - pe) *
        (10 ^ ((-k).toNat : ℤ) * 2 ^ ((pe - 128).toNat : ℤ))
      = (10 ^ k * 10 ^ ((-k).toNat : ℤ)) *
        (2 ^ (128 - pe) * 2 ^ ((pe - 128).toNat : ℤ)) from by ring,
    ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), hk, hpe]

/-- The truncation is the natural quotient `num / den`, which is what lets the
    normalization check and the whole scaling layer stay in `Nat`. -/
theorem power10_significand_nat (k : ℤ) :
    power10Significand k = power10Num k / power10Den k := by
  rw [power10Significand, power10_exact_ratio]
  exact Nat.floor_div_eq_div _ _

/-- The fixed-point exponent does normalize `10^k`, over the range Żmij's power
    indices reach. Beyond it the approximation eventually drifts from
    `⌊k·log₂10⌋ + 1`, so this is where the range is pinned down. In ratio form
    the check is two comparisons of naturals per exponent. -/
theorem power10_ratio_normalized :
    ∀ k ∈ Finset.Icc (-293 : ℤ) 323,
      2 ^ 127 * power10Den k ≤ power10Num k ∧
        power10Num k < 2 ^ 128 * power10Den k := by
  -- This and the checks like it below enumerate up to 2046 exponents.
  -- `+kernel` keeps them out of the elaborator, whose recursion and
  -- exponentiation guards they would otherwise trip.
  decide +kernel

/-- Hence the significand is a normalized 128-bit number: its top bit is set,
    which is what makes `power10Exponent` an exponent for a 128-bit significand,
    and it still fits in 128 bits. -/
theorem power10_significand_bounds (k : ℤ) (hk : -293 ≤ k ∧ k ≤ 323) :
    2 ^ 127 ≤ power10Significand k ∧ power10Significand k < 2 ^ 128 := by
  obtain ⟨hlo, hhi⟩ :=
    power10_ratio_normalized k (by simpa [Finset.mem_Icc] using hk)
  rw [power10_significand_nat]
  exact ⟨(Nat.le_div_iff_mul_le (power10_den_pos k)).mpr hlo,
    (Nat.div_lt_iff_lt_mul (power10_den_pos k)).mpr hhi⟩

/-! ## Żmij's conversion

The algorithm, as Żmij computes it. One 192-bit multiply of the significand by
the 128-bit power of ten, keeping the top 128 bits; the integral part and the
fraction are read out of that product at a fixed bit position, and the three
decisions are comparisons on those two words.

`extraShift` is the 9 bits of headroom Żmij leaves below the integral part.
Nine is not forced: 3 keeps the shift non-negative, 10 keeps `f·2^s` inside 64
bits, and 9 lets the digit constant be shared with the base-ten multiply. What
the proof needs from it is only that the shift stays in `[6, 9]`.
-/

/-- Approximation of floor(e·log₁₀ 2) used as Żmij's decimal exponent. -/
def decimalExponent (e : ℤ) : ℤ :=
  e * 315_653 / 2 ^ 20

/-- The power of ten Żmij multiplies by is `10^K` for this `K`: one past the
    decimal exponent, which is what puts the shorter candidate in the integral
    part. -/
def powerIndex (e : ℤ) : ℤ :=
  -decimalExponent e - 1

/-- Shift chosen to align the binary exponent with the power of ten, including
    Żmij's nine bits of headroom. -/
def exponentShift (e : ℤ) : ℕ :=
  Int.toNat (e + (-(decimalExponent e + 1) * 217_707) / 2 ^ 16 + 10)

/-- The top 128 bits of Żmij's 192-bit product: `⌊f·2^s·p10 / 2^64⌋`. -/
def scaledSignificand (f : ℕ) (e : ℤ) : ℕ :=
  f * 2 ^ exponentShift e * power10Significand (powerIndex e) / 2 ^ 64

/-- The integral part of the scaled value, Żmij's shorter candidate: the product
    with the nine headroom bits and the fraction shifted off. -/
def integralPart (f : ℕ) (e : ℤ) : ℕ := scaledSignificand f e / 2 ^ 73

/-- The fraction of the scaled value, in units of `2^-64`. -/
def fractionalPart (f : ℕ) (e : ℤ) : ℕ :=
  scaledSignificand f e / 2 ^ 9 % 2 ^ 64

/-- Half a ULP in the same units, truncated to the high word of the power of
    ten, plus one when `f` is even. That `+1` is the tie rule: it turns each of
    the two comparisons below from strict into non-strict exactly when a tie is
    allowed to round. -/
def halfUlp (f : ℕ) (e : ℤ) : ℕ :=
  power10Significand (powerIndex e) / 2 ^ 64 / 2 ^ (10 - exponentShift e)
    + (1 - f % 2)

/-- Rounding constant for the derived digit: half of `2^64`, nudged up by six.
    The nudge covers the truncation in `fractionalPart`; it moves the digit
    boundary by less than one unit of that word. -/
def biasedHalf : ℕ := 2 ^ 63 + 6

structure DecimalCandidates where
  k : ℤ
  integral : ℕ
  digit : ℕ
  roundUp : Bool
  roundDown : Bool

def toDecimalCandidates (f : ℕ) (e : ℤ) : DecimalCandidates :=
  let frac := fractionalPart f e
  let half := halfUlp f e

  -- Żmij detects both of these by 64-bit carry: `frac + half` wrapping past
  -- `2^64` is the fraction reaching up to the next integer.
  let roundUp : Bool := 2 ^ 64 ≤ frac + half
  let roundDown : Bool := frac < half

  -- Ten times the fraction, rounded. The one exact half that survives
  -- truncation is a quarter, whose digit 2.5 has to go to even.
  let digit : ℕ := if frac = 2 ^ 62 then 2 else (frac * 10 + biasedHalf) / 2 ^ 64

  { k := decimalExponent e
    integral := integralPart f e + (if roundUp then 1 else 0)
    digit := digit
    roundUp := roundUp
    roundDown := roundDown }

/-- Converts a regularly spaced binary64 value f·2^e to a decimal significand
    and exponent using Żmij's regular path. The significand is reported on the
    grid at `k`, so the shorter candidate appears as a multiple of ten. -/
def toDecimal (f : ℕ) (e : ℤ) : ℕ × ℤ :=
  let c := toDecimalCandidates f e
  (c.integral * 10 + (if c.roundUp || c.roundDown then 0 else c.digit), c.k)

/-! ### The shift

The shift is `e + pe + 9`, where `pe` is the power-of-ten exponent at `K`, and
it lands in `[6, 9]`. Both facts are about the two fixed-point constants rather
than about magnitudes, so both are checked over the exponent range.
-/

/-- The shift before clamping, which is what the checks below enumerate. -/
theorem exponent_shift_eq (e : ℤ) :
    (exponentShift e : ℤ)
      = max 0 (e + (-(decimalExponent e + 1) * 217_707) / 2 ^ 16 + 10) := by
  rw [exponentShift]
  omega

/-- The shift is at least six and at most nine. The upper bound is what keeps
    `f·2^s` inside 64 bits in the implementation; the lower bound is what makes
    `10 - s` a positive shift in `halfUlp`. -/
theorem exponent_shift_bounds :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971,
      6 ≤ e + (-(decimalExponent e + 1) * 217_707) / 2 ^ 16 + 10 ∧
        e + (-(decimalExponent e + 1) * 217_707) / 2 ^ 16 + 10 ≤ 9 := by
  decide +kernel

/-- Hence the shift, as a natural, is in `[6, 9]`. -/
theorem exponent_shift_range (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    6 ≤ exponentShift e ∧ exponentShift e ≤ 9 := by
  have h := exponent_shift_bounds e (by simpa [Finset.mem_Icc] using he)
  have := exponent_shift_eq e
  omega

/-- The shift undoes the power-of-ten exponent: `s - 9 - pe = e`. Both sides
    scale the same fixed-point quotient, so once the shift is known not to have
    been clamped this is arithmetic, whatever the decimal exponent is. -/
theorem exponent_shift_align (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    (exponentShift e : ℤ) - 9 - power10Exponent (powerIndex e) = e := by
  have hb := exponent_shift_bounds e (by simpa [Finset.mem_Icc] using he)
  have heq := exponent_shift_eq e
  unfold power10Exponent powerIndex
  omega

/-- The power index stays inside the range the normalization check covers. -/
theorem power_index_range (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    -293 ≤ powerIndex e ∧ powerIndex e ≤ 323 := by
  unfold powerIndex decimalExponent
  omega

/-! ## The cleared quantities

The power of ten is a ratio `num / den`, and clearing that denominator turns
every comparison below into one between naturals. Cleared, the grid at `k+1`
has step `zMul = 2^(137-s)·den`, one ULP of the value is exactly `num`, and the
fraction Żmij compares is measured in units of `zUnit·den = 2^(73-s)·den`.

Two divisions of the implementation compose into one here. `integralPart`
shifts the 192-bit product down by 64 and then by 73, which is a single
division by `2^(137-s)` once the shift is factored out, and `fractionalPart`
reads the same quotient one word lower.
-/

/-- Numerator of the exact power of ten Żmij multiplies by. -/
def zNum (e : ℤ) : ℕ := power10Num (powerIndex e)

/-- Its denominator. -/
def zDen (e : ℤ) : ℕ := power10Den (powerIndex e)

/-- Its 128-bit truncation, the `p10` of the implementation. -/
def zSig (e : ℤ) : ℕ := power10Significand (powerIndex e)

theorem z_den_pos (e : ℤ) : 0 < zDen e := power10_den_pos _

/-- The truncation is natural-number division, which is what keeps this whole
    layer in `Nat`. -/
theorem z_sig_nat (e : ℤ) : zSig e = zNum e / zDen e :=
  power10_significand_nat _

/-- `den·p10 + τ = num`: the truncated power of ten and the bits it dropped. -/
theorem z_num_split (e : ℤ) : zDen e * zSig e + zNum e % zDen e = zNum e := by
  rw [z_sig_nat]; exact Nat.div_add_mod _ _

/-- The unit the fraction is measured in, before clearing the denominator. -/
def zUnit (e : ℤ) : ℕ := 2 ^ (73 - exponentShift e)

theorem z_unit_pos (e : ℤ) : 0 < zUnit e := by rw [zUnit]; positivity

/-- One step of the coarse grid at `k+1`, with the denominator cleared. -/
def zMul (e : ℤ) : ℕ := zUnit e * 2 ^ 64 * zDen e

theorem z_mul_pos (e : ℤ) : 0 < zMul e := by
  rw [zMul]
  exact Nat.mul_pos (Nat.mul_pos (z_unit_pos e) (by positivity)) (z_den_pos e)

/-- A power of two splits into the shift and what is left above it. -/
theorem pow_shift_split (e : ℤ) (n : ℕ) (hn : exponentShift e ≤ n) :
    (2 : ℕ) ^ n = 2 ^ exponentShift e * 2 ^ (n - exponentShift e) := by
  rw [← pow_add]
  congr 1
  omega

/-- The integral part is the quotient of the cleared product by one coarse
    step: the implementation's two shifts compose into one division, and the
    alignment shift divides out of both sides of it. -/
theorem integral_quotient (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    integralPart f e = f * zSig e / (zUnit e * 2 ^ 64) := by
  have hsplit : (2 : ℕ) ^ 64 * 2 ^ 73 = 2 ^ exponentShift e * (zUnit e * 2 ^ 64) := by
    rw [zUnit, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [integralPart, scaledSignificand, zSig, Nat.div_div_eq_div_mul, hsplit,
    show f * 2 ^ exponentShift e * power10Significand (powerIndex e)
        = 2 ^ exponentShift e * (f * power10Significand (powerIndex e)) from by
      ring,
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- The fraction is the same quotient read one word lower. -/
theorem fraction_quotient (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    fractionalPart f e = f * zSig e / zUnit e % 2 ^ 64 := by
  have hsplit : (2 : ℕ) ^ 64 * 2 ^ 9 = 2 ^ exponentShift e * zUnit e := by
    rw [zUnit, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [fractionalPart, scaledSignificand, zSig, Nat.div_div_eq_div_mul, hsplit,
    show f * 2 ^ exponentShift e * power10Significand (powerIndex e)
        = 2 ^ exponentShift e * (f * power10Significand (powerIndex e)) from by
      ring,
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- The integral part and the fraction are the two halves of one quotient. -/
theorem integral_add_fraction (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    integralPart f e * 2 ^ 64 + fractionalPart f e = f * zSig e / zUnit e := by
  rw [integral_quotient f e hs, fraction_quotient f e hs,
    ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

/-- The gap from the integral part up to the exact scaled value, cleared: what
    the quotient dropped, plus what the truncated power of ten dropped. -/
def zGap (f : ℕ) (e : ℤ) : ℕ :=
  zDen e * (f * zSig e % (zUnit e * 2 ^ 64)) + f * (zNum e % zDen e)

/-- The integral part scaled back up, plus the gap, is the scaled value
    `f·num`: `Nat.div_add_mod` recovers the product from the quotient and
    `z_num_split` the power of ten from its truncation. -/
theorem integral_add_gap (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    integralPart f e * zMul e + zGap f e = f * zNum e := by
  rw [integral_quotient f e hs, zMul, zGap]
  calc f * zSig e / (zUnit e * 2 ^ 64) * (zUnit e * 2 ^ 64 * zDen e)
        + (zDen e * (f * zSig e % (zUnit e * 2 ^ 64))
          + f * (zNum e % zDen e))
      = zDen e * (f * zSig e / (zUnit e * 2 ^ 64) * (zUnit e * 2 ^ 64)
          + f * zSig e % (zUnit e * 2 ^ 64)) + f * (zNum e % zDen e) := by ring
    _ = zDen e * (f * zSig e) + f * (zNum e % zDen e) := by
          rw [Nat.div_add_mod']
    _ = f * (zDen e * zSig e + zNum e % zDen e) := by ring
    _ = f * zNum e := by rw [z_num_split]

/-! ### What the truncations discard

Both of Żmij's comparisons are between a truncated 64-bit word and the exact
quantity it stands for, so each needs the size of what was dropped. The gap is
the fraction in cleared units plus a remainder below one such unit, and one
ULP is twice half a ULP in the same units plus a remainder below one. Those two
remainders are the whole error budget the certificates below have to close.
-/

/-- The gap, in the units the fraction is measured in, is the fraction plus
    what the two truncations discarded. -/
theorem gap_eq_fraction_add (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    zGap f e
      = zUnit e * zDen e * fractionalPart f e
        + (zDen e * (f * zSig e % zUnit e) + f * (zNum e % zDen e)) := by
  -- The remainder below one coarse step splits at the fraction's own unit.
  have hdiv : f * zSig e % (zUnit e * 2 ^ 64) / zUnit e
      = f * zSig e / zUnit e % 2 ^ 64 := Nat.mod_mul_right_div_self _ _ _
  have hmod : f * zSig e % (zUnit e * 2 ^ 64) % zUnit e = f * zSig e % zUnit e :=
    Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)
  have hsplit := Nat.div_add_mod (f * zSig e % (zUnit e * 2 ^ 64)) (zUnit e)
  rw [hdiv, hmod] at hsplit
  rw [zGap, ← hsplit, fraction_quotient f e hs]
  ring

/-! ### Crossing into ℚ

The specification is about rationals; everything above is about naturals.
`zMul` is exactly the factor that clears the denominator, and it sends one
scaled ULP to `zNum`, so a candidate's distance from the value is always an
integer and every comparison the specification asks for is a comparison of
integers. This is the only place `ℚ` appears.
-/

/-- One coarse step is the alignment shift with the denominator: the fraction's
    unit and the word above it compose into `2^(137-s)`. -/
theorem z_mul_pow (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    zMul e = 2 ^ (137 - exponentShift e) * zDen e := by
  rw [zMul, zUnit, ← pow_add,
    show 73 - exponentShift e + 64 = 137 - exponentShift e from by
      have := exponent_shift_range e he; omega]

/-- `zMul` clears the denominator in `power10_exact_ratio`, leaving `zNum`
    times the binary-decimal scaling factor. -/
theorem z_mul_eq (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    (zMul e : ℚ) = (zNum e : ℚ) * (2 ^ (-e) * 10 ^ (-powerIndex e)) := by
  set K := powerIndex e
  set pe := power10Exponent K
  have hd : (0 : ℚ) < (zDen e : ℚ) := by exact_mod_cast z_den_pos e
  have hnum : (10 : ℚ) ^ K * 2 ^ (128 - pe) * zDen e = zNum e := by
    rw [power10_exact_ratio, ← zNum, ← zDen, div_mul_cancel₀ _ (ne_of_gt hd)]
  -- The inverse scale turns the power-of-ten factor into `2^(137-s)`, which is
  -- where the shift alignment is spent.
  have hscale : (10 : ℚ) ^ K * 2 ^ (128 - pe) * (2 ^ (-e) * 10 ^ (-K))
      = 2 ^ (137 - exponentShift e) := by
    have h10 : (10 : ℚ) ^ K * 10 ^ (-K) = 1 := by
      rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp
    have halign : (exponentShift e : ℤ) - 9 - pe = e := exponent_shift_align e he
    have hs := exponent_shift_range e he
    calc (10 : ℚ) ^ K * 2 ^ (128 - pe) * (2 ^ (-e) * 10 ^ (-K))
        = (10 ^ K * 10 ^ (-K)) * (2 ^ (128 - pe) * 2 ^ (-e)) := by ring
      _ = (2 : ℚ) ^ ((128 - pe) + -e) := by
          rw [h10, one_mul, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = 2 ^ (137 - exponentShift e) := by
          rw [show (128 - pe) + -e = ((137 - exponentShift e : ℕ) : ℤ)
                from by omega, zpow_natCast]
  rw [z_mul_pow e he]
  push_cast
  rw [← hscale, ← hnum]
  ring

/-- The scale sends half a scaled ULP to half of `zNum`, so twice the scale
    sends it to `zNum` itself: one ULP on the grid at `k+1` is exactly one
    `zNum`. -/
theorem z_half_ulp_scaled (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ulp e * 10 ^ powerIndex e / 2 * (((2 : ℕ) : ℚ) * (zMul e : ℚ))
      = ((zNum e : ℕ) : ℚ) := by
  have h10 : (10 : ℚ) ^ powerIndex e * 10 ^ (-powerIndex e) = 1 := by
    rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp
  have h2 : (2 : ℚ) ^ e * 2 ^ (-e) = 1 := by
    rw [← zpow_add₀ (two_ne_zero' ℚ)]; simp
  calc ulp e * 10 ^ powerIndex e / 2 * (((2 : ℕ) : ℚ) * (zMul e : ℚ))
      = (zNum e : ℚ) * (2 ^ e * 2 ^ (-e))
          * (10 ^ powerIndex e * 10 ^ (-powerIndex e)) := by
        rw [ulp, z_mul_eq e he]; push_cast; ring
    _ = ((zNum e : ℕ) : ℚ) := by rw [h10, h2]; ring

/-- The one Żmij-specific fact the generic bridge needs: `zMul` sends the
    scaled value to the integer `f·num`, so every candidate distance is an
    integer. -/
theorem z_value_scaled (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    value f e * 10 ^ powerIndex e * (zMul e : ℚ) = ((f * zNum e : ℤ) : ℚ) := by
  have h := z_half_ulp_scaled e he
  rw [ulp] at h
  push_cast at h ⊢
  rw [value]
  linear_combination (f : ℚ) * h

/-- A candidate on the grid at `k+1` round-trips exactly when twice its signed
    distance stays within one ULP, that is within `zNum`, strictly so for odd
    `f`. This is the only use either direction of the coarse argument makes of
    `ℚ`. -/
theorem roundtrips_iff_dist (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) {c : ℕ}
    {dist : ℤ} (hc : (c : ℤ) * zMul e + dist = f * zNum e) :
    Roundtrips f e (c * 10 ^ (decimalExponent e + 1))
      ↔ if f % 2 = 0 then -(zNum e : ℤ) ≤ 2 * dist ∧ 2 * dist ≤ zNum e
        else -(zNum e : ℤ) < 2 * dist ∧ 2 * dist < zNum e := by
  have hgrid : -(decimalExponent e + 1) = powerIndex e := by
    rw [powerIndex]; ring
  obtain ⟨hle, hlt, -⟩ := scaled_cmp_of_int_eq (c := c) (m := zMul e) (a := 2)
    (b := zNum e) (dist := dist)
    (x := value f e * 10 ^ (-(decimalExponent e + 1)))
    (thr := ulp e * 10 ^ (-(decimalExponent e + 1)) / 2)
    (z_mul_pos e) two_pos
    (by rw [hgrid]; exact z_value_scaled f e he)
    (by rw [hgrid]; exact z_half_ulp_scaled e he) hc
  refine (roundtrips_iff_scaled f e (decimalExponent e + 1) c).trans ?_
  split_ifs
  · exact hle.trans (by omega)
  · exact hlt.trans (by omega)

/-! ## The error budget

Both coarse flags compare Żmij's truncated fraction with its truncated half
ULP. Cleared, one fraction unit is `zEdge = 2^(73-s)·den`: the fraction stands
for that much of the gap apiece, the half-ULP word for twice that much of one
ULP apiece, and each of the two truncations leaves a remainder below one unit,
`zErr` from the gap and `zErrHalf` from the ULP. Those two remainders are the
whole budget the certificates below have to close.
-/

/-- One fraction unit with the denominator cleared: the resolution both coarse
    comparisons work at. -/
def zEdge (e : ℤ) : ℕ := zUnit e * zDen e

theorem z_edge_pos (e : ℤ) : 0 < zEdge e :=
  Nat.mul_pos (z_unit_pos e) (z_den_pos e)

/-- One coarse step is `2^64` fraction units, which is what makes the carry out
    of Żmij's 64-bit addition the fraction reaching the next integer. -/
theorem z_mul_eq_edge (e : ℤ) : zMul e = zEdge e * 2 ^ 64 := by
  rw [zMul, zEdge]
  ring

/-- Half a ULP as Żmij truncates it, in fraction units. -/
def zHalf (e : ℤ) : ℕ := zSig e / (2 * zUnit e)

/-- What the fraction discards from the gap: the bits below one fraction unit,
    plus the power-of-ten truncation the whole product carries. -/
def zErr (f : ℕ) (e : ℤ) : ℕ :=
  zDen e * (f * zSig e % zUnit e) + f * (zNum e % zDen e)

/-- What the truncated half-ULP word discards from one ULP. -/
def zErrHalf (e : ℤ) : ℕ :=
  zDen e * (zSig e % (2 * zUnit e)) + zNum e % zDen e

/-- Żmij's half-ULP word is the truncated half ULP plus one for even `f`. That
    `+1` is the tie rule: it turns each comparison below from strict into
    non-strict exactly when a tie is allowed to round. -/
theorem half_ulp_eq (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    halfUlp f e = zHalf e + (1 - f % 2) := by
  have hpow : (2 : ℕ) ^ 64 * 2 ^ (10 - exponentShift e) = 2 * zUnit e := by
    rw [zUnit, ← pow_add,
      show 64 + (10 - exponentShift e) = 73 - exponentShift e + 1 from by omega,
      pow_succ]
    ring
  rw [halfUlp, zHalf, zSig, Nat.div_div_eq_div_mul, hpow]

/-- The gap is the fraction in cleared units plus what the fraction
    discarded. -/
theorem gap_eq_edge_fraction (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    zGap f e = zEdge e * fractionalPart f e + zErr f e := by
  rw [zEdge, zErr]
  exact gap_eq_fraction_add f e hs

/-- One ULP is twice the truncated half ULP in cleared units, plus what that
    truncation discarded. -/
theorem num_eq_edge_half (e : ℤ) :
    zNum e = 2 * (zEdge e * zHalf e) + zErrHalf e := by
  rw [zEdge, zHalf, zErrHalf]
  calc zNum e = zDen e * zSig e + zNum e % zDen e := (z_num_split e).symm
    _ = zDen e * (2 * zUnit e * (zSig e / (2 * zUnit e))
          + zSig e % (2 * zUnit e)) + zNum e % zDen e := by
        rw [Nat.div_add_mod]
    _ = 2 * (zUnit e * zDen e * (zSig e / (2 * zUnit e)))
          + (zDen e * (zSig e % (2 * zUnit e)) + zNum e % zDen e) := by ring

/-- The half-ULP truncation discards less than two fraction units, so the
    fraction reaching one unit past that word settles the comparison by
    itself. -/
theorem err_half_lt (e : ℤ) : zErrHalf e < 2 * zEdge e := by
  have hden := z_den_pos e
  have h1 : zSig e % (2 * zUnit e) + 1 ≤ 2 * zUnit e :=
    Nat.mod_lt _ (by have := z_unit_pos e; omega)
  have h2 : zNum e % zDen e < zDen e := Nat.mod_lt _ hden
  have hmono : zDen e * (zSig e % (2 * zUnit e) + 1) ≤ zDen e * (2 * zUnit e) :=
    Nat.mul_le_mul_left _ h1
  have hexp : zDen e * (zSig e % (2 * zUnit e) + 1)
      = zDen e * (zSig e % (2 * zUnit e)) + zDen e := by ring
  have hedge : 2 * zEdge e = zDen e * (2 * zUnit e) := by rw [zEdge]; ring
  rw [zErrHalf, hedge]
  omega

/-- Everything about the truncated power of ten that has to be checked per
    exponent rather than derived from magnitudes: the fraction's error stays
    within two fraction units of the half-ULP word's, and the two together stay
    under four. Both are stated at the largest error any significand can carry,
    and the first is tight, with two to spare at `e = -90`. -/
def zChecksHold (e : ℤ) : Bool :=
  let den := zDen e
  let unit := zUnit e
  let tau := zNum e % den
  let errHalf := den * (zNum e / den % (2 * unit)) + tau
  let errMax := den * (unit - 1) + (2 ^ 53 - 1) * tau
  decide (2 * errMax < errHalf + 2 * (unit * den)
    ∧ 2 * errMax + errHalf < 4 * (unit * den))

theorem z_checks_all :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, zChecksHold e = true := by
  decide +kernel

/-- Those two checks for one exponent, with the truncation read back as
    `zSig`. -/
theorem z_checks (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 * (zDen e * (zUnit e - 1) + (2 ^ 53 - 1) * (zNum e % zDen e))
        < zErrHalf e + 2 * zEdge e
      ∧ 2 * (zDen e * (zUnit e - 1) + (2 ^ 53 - 1) * (zNum e % zDen e))
          + zErrHalf e < 4 * zEdge e := by
  have hcert := z_checks_all e (by simpa [Finset.mem_Icc] using he)
  simp only [zChecksHold, decide_eq_true_eq] at hcert
  rw [zErrHalf, zEdge, z_sig_nat]
  exact hcert

/-- The fraction's truncation error, at its largest over the significands. -/
theorem z_err_le (f : ℕ) (e : ℤ) (hr : Regular f e) :
    zErr f e ≤ zDen e * (zUnit e - 1) + (2 ^ 53 - 1) * (zNum e % zDen e) := by
  have h1 : f * zSig e % zUnit e ≤ zUnit e - 1 := by
    have := Nat.mod_lt (f * zSig e) (z_unit_pos e)
    omega
  have h2 : f ≤ 2 ^ 53 - 1 := by have := hr.sig_lt; omega
  rw [zErr]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_right _ h2)

/-- The two error bounds the comparisons are decided by, at this
    significand. -/
theorem z_err_bounds (f : ℕ) (e : ℤ) (hr : Regular f e) :
    2 * zErr f e < zErrHalf e + 2 * zEdge e
      ∧ 2 * zErr f e + zErrHalf e < 4 * zEdge e := by
  have hle := z_err_le f e hr
  have hchk := z_checks e hr.range
  omega

/-- The power of ten is normalized in cleared form too. -/
theorem z_num_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 127 * zDen e ≤ zNum e ∧ zNum e < 2 ^ 128 * zDen e :=
  power10_ratio_normalized (powerIndex e)
    (by simpa [Finset.mem_Icc] using power_index_range e he)

/-- A fraction unit is negligible against the power of ten, which is what
    leaves both coarse boundaries well inside the two steps the residue below
    runs over: `zEdge ≤ 2^67·den` while `num ≥ 2^127·den`. -/
theorem z_edge_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    4 * zEdge e < zNum e ∧ zNum e + 4 * zEdge e < 2 * zMul e := by
  obtain ⟨hs6, hs9⟩ := exponent_shift_range e he
  obtain ⟨hlo, hhi⟩ := z_num_bounds e he
  have hden := z_den_pos e
  have hedge : 4 * zEdge e ≤ 2 ^ 69 * zDen e := by
    rw [zEdge]
    calc 4 * (zUnit e * zDen e) ≤ 4 * (2 ^ 67 * zDen e) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (by rw [zUnit]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ = 2 ^ 69 * zDen e := by ring
  have hmul : 2 ^ 128 * zDen e ≤ zMul e := by
    rw [zMul]
    calc 2 ^ 128 * zDen e = 2 ^ 64 * 2 ^ 64 * zDen e := by ring
      _ ≤ zUnit e * 2 ^ 64 * zDen e :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (by rw [zUnit]; exact Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h69 : 2 ^ 69 * zDen e < 2 ^ 127 * zDen e :=
    mul_lt_mul_of_pos_right (by norm_num) hden
  omega

/-! ### Refuting the exceptional windows

Everything above is analytic, and it decides both comparisons except within one
fraction unit of a boundary. What is left is a band of that width either side of
each boundary, minus the boundary itself; the certificates say those bands are
empty, which is what leaves the exact ties their room.

Both boundaries share one modular problem. Cleared, one coarse step is `zMul`
and the doubled gap is the residue of `2·num·f` in two steps, so the trim-down
boundary is `num` and the trim-up boundary `2·mul - num`. A violation of either
puts that residue in a window of relative width about `2^-63`, which is the kind
of question `ModWindows` answers with one multiplier per exponent.

Ties are not rare here and not refutable: `10^K` for `K` in `[-23, -1]` gives a
scaled ULP with a small denominator, and the boundary is then hit by a whole
residue class of significands, up to a fifth of them at `K = -1`. What makes
those cases correct is that each is an exact tie, resolved by parity, which is
exactly what excluding the boundary from the windows says.
-/

/-- The gap is under one coarse step by all but the errors' reach: the fraction
    accounts for all but one unit of the step, and the two truncations for less
    than one unit plus `2^53` denominators. -/
theorem gap_lt_mul_add (f : ℕ) (e : ℤ) (hr : Regular f e) :
    zGap f e < zMul e + 2 ^ 53 * zDen e := by
  have hs := (exponent_shift_range e hr.range).2
  have hden := z_den_pos e
  have hτ : zNum e % zDen e < zDen e := Nat.mod_lt _ hden
  have hgap := gap_eq_edge_fraction f e hs
  -- The fraction leaves one unit of the step unaccounted for.
  have hfrac : fractionalPart f e < 2 ^ 64 := by
    rw [fractionalPart]; exact Nat.mod_lt _ (by positivity)
  have hfr : zEdge e * fractionalPart f e + zEdge e ≤ zMul e := by
    rw [z_mul_eq_edge]
    calc zEdge e * fractionalPart f e + zEdge e
        = zEdge e * (fractionalPart f e + 1) := by ring
      _ ≤ zEdge e * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)
  -- Both truncations together stay under one unit plus the error's reach.
  have h1 : zDen e * (f * zSig e % zUnit e) < zEdge e := by
    rw [zEdge, Nat.mul_comm (zUnit e) (zDen e)]
    exact mul_lt_mul_of_pos_left (Nat.mod_lt _ (z_unit_pos e)) hden
  have h2 : f * (zNum e % zDen e) < 2 ^ 53 * zDen e :=
    Nat.mul_lt_mul'' (by have := hr.sig_lt; omega) hτ
  rw [zErr] at hgap
  omega

/-- The doubled gap read modulo two coarse steps. The truncated power of ten
    can leave the integral part one short of the exact one, and then the gap is
    a whole step and this residue wraps to zero. -/
def zRest (f : ℕ) (e : ℤ) : ℕ :=
  if zMul e ≤ zGap f e then zGap f e - zMul e else zGap f e

private theorem mod_of_add_mul {a q r m : ℕ} (h : a = m * q + r) (hlt : r < m) :
    a % m = r := by
  rw [h, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- The doubled gap, less a whole step where it took one, is the residue of
    `2·num·f` in two steps. -/
theorem rest_mod (f : ℕ) (e : ℤ) (hr : Regular f e) :
    2 * zNum e * f % (2 * zMul e) = 2 * zRest f e := by
  have hid := integral_add_gap f e (exponent_shift_range e hr.range).2
  have hden := z_den_pos e
  have hpow : 2 ^ 53 * zDen e ≤ zMul e := by
    rw [zMul]
    exact Nat.mul_le_mul_right _
      (calc (2 : ℕ) ^ 53 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ zUnit e * 2 ^ 64 := Nat.le_mul_of_pos_left _ (z_unit_pos e))
  have hwide := gap_lt_mul_add f e hr
  rw [zRest]
  split_ifs with h
  · obtain ⟨d, hd⟩ : ∃ d, zGap f e = zMul e + d := ⟨zGap f e - zMul e, by omega⟩
    rw [show zGap f e - zMul e = d from by omega]
    refine mod_of_add_mul (q := integralPart f e + 1) ?_ (by omega)
    calc 2 * zNum e * f = 2 * (integralPart f e * zMul e + zGap f e) := by
          rw [hid]; ring
      _ = 2 * zMul e * (integralPart f e + 1) + 2 * d := by rw [hd]; ring
  · refine mod_of_add_mul (q := integralPart f e) ?_ (by omega)
    calc 2 * zNum e * f = 2 * (integralPart f e * zMul e + zGap f e) := by
          rw [hid]; ring
      _ = 2 * zMul e * integralPart f e + 2 * zGap f e := by ring

/-- The residues the error bounds cannot decide: one fraction unit's reach
    either side of each coarse boundary, the boundaries themselves excluded,
    plus the overshoot of a whole step, which no significand reaches either. -/
private def expWindows (e : ℤ) : ModWindows where
  g := 2 * zNum e
  modulus := 2 * zMul e
  -- Only the minimum exponent carries significands below `2^52`, and the
  -- certificates need the smaller box everywhere else.
  f0 := if e = -1074 then 1 else 2 ^ 52 + 1
  f1 := 2 ^ 53 - 1
  windows :=
    let num : ℤ := zNum e
    let step : ℤ := 2 * zMul e
    let w : ℤ := 4 * zEdge e
    [(1, w), (num - w, num - 1), (num + 1, num + w),
      (step - num - w, step - num - 1), (step - num + 1, step - num + w)]

/-- Close `∃ q, (expWindows e).refutedBy q = true` for a literal exponent. -/
elab "exp_cert" : tactic => modCertTactic fun e => (expWindows e).search

private theorem exp_windows_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (expWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> exp_cert

/-- A doubled gap landing in a refuted window is impossible: it is the residue
    of `2·num·f` modulo two coarse steps. -/
private theorem no_window_hit {lo hi q : ℤ} (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcert : (expWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (expWindows e).windows)
    (hlo : lo ≤ 2 * (zRest f e : ℤ)) (hhi : 2 * (zRest f e : ℤ) ≤ hi) :
    False := by
  have hf0 : (expWindows e).f0 ≤ f := by
    simp only [expWindows]
    split_ifs with hcase
    · exact hr.pos
    · rcases hr.1.2.2 with h | h
      · omega
      · exact absurd h hcase
  have hf1 : f ≤ (expWindows e).f1 := by
    simp only [expWindows]
    have := hr.sig_lt
    omega
  have hmod : 0 < (expWindows e).modulus := by
    simp only [expWindows]
    have := z_mul_pos e
    omega
  exact (expWindows e).not_hit f hmod hcert hmem hf0 hf1 (rest_mod f e hr).symm
    (by push_cast; omega) (by push_cast; omega)

/-- The gap never passes a whole coarse step. The truncated power of ten can put
    the integral part one short of the exact one, which happens exactly when the
    scaled value is an integer, and Żmij's carry recovers it; anything beyond
    that would be an overshoot in the first window. -/
theorem gap_le_mul (f : ℕ) (e : ℤ) (hr : Regular f e) : zGap f e ≤ zMul e := by
  by_contra hcon
  obtain ⟨q, hcert⟩ := exp_windows_refuted e hr.range
  have hs := (exponent_shift_range e hr.range).2
  have hwide := gap_lt_mul_add f e hr
  have hrest : zRest f e = zGap f e - zMul e := by
    rw [zRest]
    split_ifs with h
    · rfl
    · omega
  -- The overshoot is under `2^53` denominators, well inside one fraction unit's
  -- reach, which is what the first window covers.
  have hreach : 2 ^ 54 * zDen e ≤ 4 * zEdge e := by
    rw [zEdge]
    calc 2 ^ 54 * zDen e ≤ 2 ^ 64 * zDen e :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ 4 * (zUnit e * zDen e) := by
          rw [zUnit, show (4 : ℕ) = 2 ^ 2 from by norm_num, ← Nat.mul_assoc,
            ← pow_add]
          exact Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact no_window_hit f e hr hcert (.head _) (by rw [hrest]; omega)
    (by rw [hrest]; omega)

/-- With the gap inside a step, the residue is the doubled gap itself, except
    where the gap is exactly a step and it wraps to zero. -/
theorem rest_eq (f : ℕ) (e : ℤ) (hr : Regular f e) :
    zRest f e = zGap f e ∨ (zGap f e = zMul e ∧ zRest f e = 0) := by
  have hle := gap_le_mul f e hr
  rw [zRest]
  split_ifs with h
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl rfl

/-- Either the doubled gap sits exactly on the boundary `b`, a genuine exact
    tie, or it is more than one fraction unit's reach away from it. A gap of
    exactly one step puts the doubled gap at `2·mul`, past every window, so
    interiority covers that case rather than a certificate. -/
private theorem gap_tie_or_far {b : ℤ} (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hb : 4 * (zEdge e : ℤ) < b ∧ b + 4 * (zEdge e : ℤ) < 2 * (zMul e : ℤ))
    (hbelow : (b - 4 * (zEdge e : ℤ), b - 1) ∈ (expWindows e).windows)
    (habove : (b + 1, b + 4 * (zEdge e : ℤ)) ∈ (expWindows e).windows) :
    2 * (zGap f e : ℤ) = b ∨ b + 4 * (zEdge e : ℤ) < 2 * (zGap f e : ℤ)
      ∨ 2 * (zGap f e : ℤ) + 4 * (zEdge e : ℤ) < b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hhi, hlo⟩ := hcon
  obtain ⟨q, hcert⟩ := exp_windows_refuted e hr.range
  rcases rest_eq f e hr with hrest | ⟨heq, -⟩
  · rcases lt_or_ge (2 * (zGap f e : ℤ)) b with h | h
    · exact no_window_hit f e hr hcert hbelow (by rw [hrest]; omega)
        (by rw [hrest]; omega)
    · exact no_window_hit f e hr hcert habove (by rw [hrest]; omega)
        (by rw [hrest]; omega)
  · rw [heq] at hhi
    omega

/-- The trim-down dichotomy, about the boundary `num`. -/
theorem down_tie_or_far (f : ℕ) (e : ℤ) (hr : Regular f e) :
    2 * (zGap f e : ℤ) = zNum e
      ∨ (zNum e : ℤ) + 4 * zEdge e < 2 * (zGap f e : ℤ)
      ∨ 2 * (zGap f e : ℤ) + 4 * (zEdge e : ℤ) < zNum e := by
  have hb := z_edge_bounds e hr.range
  exact gap_tie_or_far (b := (zNum e : ℤ)) f e hr
    ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2⟩
    (by simp [expWindows]) (by simp [expWindows])

/-- The trim-up dichotomy, about the boundary `2·mul - num`, which Żmij's carry
    reads as the fraction and the half-ULP word summing past `2^64`. -/
theorem up_tie_or_far (f : ℕ) (e : ℤ) (hr : Regular f e) :
    2 * (zGap f e : ℤ) + zNum e = 2 * (zMul e : ℤ)
      ∨ 2 * (zMul e : ℤ) + 4 * zEdge e < 2 * (zGap f e : ℤ) + zNum e
      ∨ 2 * (zGap f e : ℤ) + (zNum e : ℤ) + 4 * zEdge e < 2 * zMul e := by
  have hb := z_edge_bounds e hr.range
  have hnum : 0 < zNum e := by
    have := (z_num_bounds e hr.range).1
    have h : 0 < 2 ^ 127 * zDen e := by
      have := z_den_pos e
      positivity
    omega
  have hbz : 4 * (zEdge e : ℤ) < 2 * (zMul e : ℤ) - zNum e
      ∧ 2 * (zMul e : ℤ) - zNum e + 4 * (zEdge e : ℤ) < 2 * (zMul e : ℤ) := by
    obtain ⟨h1, h2⟩ := hb
    constructor
    · have : (zNum e : ℤ) + 4 * zEdge e < 2 * zMul e := by exact_mod_cast h2
      omega
    · have : 4 * (zEdge e : ℤ) < zNum e := by exact_mod_cast h1
      omega
  have := gap_tie_or_far (b := 2 * (zMul e : ℤ) - zNum e) f e hr hbz
    (by simp [expWindows]) (by simp [expWindows])
  omega

/-! ## The coarse decisions

Each flag is pinned to its candidate by two composed equivalences: `flag ↔ gap`
says what the comparison decides about `zGap`, and `roundtrips_iff_dist` says
when that gap admits a round-trip.

The first is where the work is. One unit of the fraction is worth one `zEdge` of
the gap, so the comparison is the exact one up to the two truncation errors, and
the dichotomies above leave only the exact ties inside that margin. There both
sides resolve the same way, the flag by the `+1` for even `f` and the
specification by the parity in `roundtrips_iff_dist`.
-/

/-- One unit of the fraction is worth one `zEdge` of the gap. -/
private theorem edge_succ_le (e : ℤ) {a b : ℕ} (h : a < b) :
    zEdge e * a + zEdge e ≤ zEdge e * b := by
  calc zEdge e * a + zEdge e = zEdge e * (a + 1) := by ring
    _ ≤ zEdge e * b := Nat.mul_le_mul_left _ (by omega)

/-- And two units two of them. -/
private theorem edge_two_le (e : ℤ) {a b : ℕ} (h : a + 2 ≤ b) :
    zEdge e * a + 2 * zEdge e ≤ zEdge e * b := by
  calc zEdge e * a + 2 * zEdge e = zEdge e * (a + 2) := by ring
    _ ≤ zEdge e * b := Nat.mul_le_mul_left _ h

/-- Twice the fraction's unit as a power of two, which is what `zHalf`
    truncates by. -/
private theorem two_unit_eq (e : ℤ) (hs : exponentShift e ≤ 9) :
    2 * zUnit e = 2 ^ (74 - exponentShift e) := by
  rw [zUnit, show 74 - exponentShift e = 73 - exponentShift e + 1 from by omega,
    pow_succ]
  ring

/-- The half-ULP word is positive and below `2^64`: the power of ten is
    normalized and the shift truncates it by between `2^65` and `2^68`. -/
theorem z_half_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    0 < zHalf e ∧ zHalf e < 2 ^ 64 := by
  obtain ⟨hs6, hs9⟩ := exponent_shift_range e he
  obtain ⟨hlo, hhi⟩ :=
    power10_significand_bounds (powerIndex e) (power_index_range e he)
  have hlo' : (2 : ℕ) ^ 127 ≤ zSig e := hlo
  have hhi' : zSig e < 2 ^ 128 := hhi
  have htwo := two_unit_eq e hs9
  have hpos : 0 < 2 * zUnit e := by have := z_unit_pos e; omega
  have hsmall : 2 * zUnit e ≤ 2 ^ 68 := by
    rw [htwo]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig : (2 : ℕ) ^ 65 ≤ 2 * zUnit e := by
    rw [htwo]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨?_, ?_⟩
  · have h1 : 1 ≤ zSig e / (2 * zUnit e) := (Nat.one_le_div_iff hpos).mpr
      (calc 2 * zUnit e ≤ 2 ^ 68 := hsmall
        _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        _ ≤ zSig e := hlo')
    rw [zHalf]
    omega
  · rw [zHalf, Nat.div_lt_iff_lt_mul hpos]
    calc zSig e < 2 ^ 128 := hhi'
      _ = 2 ^ 63 * 2 ^ 65 := by norm_num
      _ ≤ 2 ^ 64 * 2 ^ 65 := by norm_num
      _ ≤ 2 ^ 64 * (2 * zUnit e) := Nat.mul_le_mul_left _ hbig

/-- The fraction and the half-ULP word never sum to exactly `2^64`. Where they
    did, the dichotomy would make the value an exact tie with both truncations
    vanishing, and the power of ten being exact then forces
    `(2f+1)·zHalf = (c+1)·2^64`; but `2f+1` is odd and `zHalf` is positive and
    below `2^64`, so no significand can do it. This is what keeps Żmij's carry
    from firing on an odd significand at a tie, where the upper candidate does
    not round-trip. -/
theorem fraction_add_half_ne (f : ℕ) (e : ℤ) (hr : Regular f e) :
    fractionalPart f e + zHalf e ≠ 2 ^ 64 := by
  intro hS
  have hs := (exponent_shift_range e hr.range).2
  have hden := z_den_pos e
  have hedge := z_edge_pos e
  have hgap := gap_eq_edge_fraction f e hs
  have hnum := num_eq_edge_half e
  obtain ⟨-, herr2⟩ := z_err_bounds f e hr
  -- The doubled gap is within a fraction unit of the upper boundary, so the
  -- dichotomy makes it an exact tie and both truncations vanish.
  have hmul : zEdge e * fractionalPart f e + zEdge e * zHalf e = zMul e := by
    rw [show zEdge e * fractionalPart f e + zEdge e * zHalf e
        = zEdge e * (fractionalPart f e + zHalf e) from by ring, hS, z_mul_eq_edge]
  have hzero : 2 * zErr f e + zErrHalf e = 0 := by
    rcases up_tie_or_far f e hr with h | h | h <;> omega
  -- An exact power of ten with nothing below the half-ULP word, so one ULP is
  -- exactly twice that word and the gap is exactly the fraction.
  have hτ : zNum e % zDen e = 0 := by rw [zErrHalf] at hzero; omega
  have hsig : zSig e % (2 * zUnit e) = 0 := by
    rw [zErrHalf] at hzero
    rcases Nat.eq_zero_or_pos (zSig e % (2 * zUnit e)) with h | h
    · exact h
    · have : 0 < zDen e * (zSig e % (2 * zUnit e)) := Nat.mul_pos hden h
      omega
  have hnum' : zNum e = 2 * (zEdge e * zHalf e) := by rw [num_eq_edge_half]; omega
  have hgap' : zGap f e = zEdge e * fractionalPart f e := by omega
  -- Scaling the exact identity back up and cancelling `zEdge` leaves an odd
  -- multiple of `zHalf` equal to a multiple of `2^64`.
  have hid := integral_add_gap f e hs
  have hkey : zEdge e * ((integralPart f e + 1) * 2 ^ 64)
      = zEdge e * ((2 * f + 1) * zHalf e) := by
    have hstep : integralPart f e * zMul e = zEdge e * (integralPart f e * 2 ^ 64) := by
      rw [z_mul_eq_edge]; ring
    have hrhs : f * zNum e = zEdge e * (2 * f * zHalf e) := by rw [hnum']; ring
    have hlhs : zEdge e * fractionalPart f e + zEdge e * zHalf e
        = zEdge e * 2 ^ 64 := by rw [hmul, z_mul_eq_edge]
    calc zEdge e * ((integralPart f e + 1) * 2 ^ 64)
        = zEdge e * (integralPart f e * 2 ^ 64) + zEdge e * 2 ^ 64 := by ring
      _ = integralPart f e * zMul e
            + (zEdge e * fractionalPart f e + zEdge e * zHalf e) := by
          rw [hstep, hlhs]
      _ = f * zNum e + zEdge e * zHalf e := by rw [← hgap', ← hid]; ring
      _ = zEdge e * ((2 * f + 1) * zHalf e) := by rw [hrhs]; ring
  have hcancel : (integralPart f e + 1) * 2 ^ 64 = (2 * f + 1) * zHalf e :=
    Nat.eq_of_mul_eq_mul_left hedge hkey
  -- `2f+1` is odd, so the power of two has to divide `zHalf`, which is too
  -- small to admit it.
  have hcop : Nat.Coprime (2 ^ 64) (2 * f + 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ⟨f, by ring⟩)
  have hdvd : (2 : ℕ) ^ 64 ∣ zHalf e := by
    refine hcop.dvd_of_dvd_mul_right ⟨integralPart f e + 1, ?_⟩
    calc zHalf e * (2 * f + 1) = (2 * f + 1) * zHalf e := by ring
      _ = (integralPart f e + 1) * 2 ^ 64 := hcancel.symm
      _ = 2 ^ 64 * (integralPart f e + 1) := by ring
  obtain ⟨hpos, hlt⟩ := z_half_bounds e hr.range
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- What `roundDown` decides. The comparison is the exact bound on `zGap` up to
    the two truncations, and inside that margin `down_tie_or_far` leaves only an
    exact tie, where the fraction equals the half-ULP word exactly and the `+1`
    for even `f` resolves it the way the specification does. -/
theorem round_down_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundDown = true
      ↔ if f % 2 = 0 then 2 * zGap f e ≤ zNum e else 2 * zGap f e < zNum e := by
  have hs := (exponent_shift_range e hr.range).2
  have hgap := gap_eq_edge_fraction f e hs
  have hnum := num_eq_edge_half e
  obtain ⟨herr, -⟩ := z_err_bounds f e hr
  have hhalf := err_half_lt e
  have hdich := down_tie_or_far f e hr
  have hflag : (toDecimalCandidates f e).roundDown = true
      ↔ fractionalPart f e < zHalf e + (1 - f % 2) := by
    show decide (fractionalPart f e < halfUlp f e) = true ↔ _
    rw [decide_eq_true_eq, half_ulp_eq f e hs]
  rw [hflag]
  rcases Nat.lt_trichotomy (fractionalPart f e) (zHalf e) with hf | hf | hf
  · have hp := edge_succ_le e hf
    split_ifs <;> omega
  · have hp : zEdge e * fractionalPart f e = zEdge e * zHalf e := by rw [hf]
    split_ifs <;> omega
  · have hp := edge_succ_le e hf
    split_ifs <;> omega

/-- What `roundUp` decides. Żmij detects it as the carry out of a 64-bit
    addition, which is the fraction and the half-ULP word summing past `2^64`;
    `fraction_add_half_ne` rules out landing on `2^64` itself, and one short of
    it `up_tie_or_far` again leaves only an exact tie. -/
theorem round_up_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundUp = true
      ↔ if f % 2 = 0 then 2 * zMul e ≤ 2 * zGap f e + zNum e
        else 2 * zMul e < 2 * zGap f e + zNum e := by
  have hs := (exponent_shift_range e hr.range).2
  have hgap := gap_eq_edge_fraction f e hs
  have hnum := num_eq_edge_half e
  obtain ⟨-, herr2⟩ := z_err_bounds f e hr
  have hdich := up_tie_or_far f e hr
  have hne := fraction_add_half_ne f e hr
  have hmul := z_mul_eq_edge e
  have hsum : zEdge e * fractionalPart f e + zEdge e * zHalf e
      = zEdge e * (fractionalPart f e + zHalf e) := by ring
  have hflag : (toDecimalCandidates f e).roundUp = true
      ↔ 2 ^ 64 ≤ fractionalPart f e + (zHalf e + (1 - f % 2)) := by
    show decide (2 ^ 64 ≤ fractionalPart f e + halfUlp f e) = true ↔ _
    rw [decide_eq_true_eq, half_ulp_eq f e hs]
  rw [hflag]
  rcases Nat.lt_trichotomy (fractionalPart f e + zHalf e) (2 ^ 64) with hf | hf | hf
  · -- Short of the carry: either two units short, or one short and a tie.
    rcases Nat.lt_or_ge (fractionalPart f e + zHalf e + 1) (2 ^ 64) with h1 | h1
    · have hp := edge_two_le e (by omega : fractionalPart f e + zHalf e + 2 ≤ 2 ^ 64)
      split_ifs <;> omega
    · have heq : fractionalPart f e + zHalf e + 1 = 2 ^ 64 := by omega
      have hp : zEdge e * (fractionalPart f e + zHalf e) + zEdge e
          = zEdge e * 2 ^ 64 := by
        calc zEdge e * (fractionalPart f e + zHalf e) + zEdge e
            = zEdge e * (fractionalPart f e + zHalf e + 1) := by ring
          _ = zEdge e * 2 ^ 64 := by rw [heq]
      split_ifs <;> omega
  · exact absurd hf hne
  · have hp := edge_succ_le e hf
    split_ifs <;> omega

/-- The integral part sits `zGap` below the scaled value. -/
theorem integral_scaled (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    (integralPart f e : ℤ) * zMul e + zGap f e = f * zNum e := by
  exact_mod_cast integral_add_gap f e hs

/-- And its successor one whole step above that. -/
theorem successor_scaled (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    ((integralPart f e + 1 : ℕ) : ℤ) * zMul e + ((zGap f e : ℤ) - zMul e)
      = f * zNum e := by
  have := integral_scaled f e hs
  push_cast
  linarith

/-- `roundDown` fires exactly when the integral part round-trips. Both are a
    bound on `zGap` by `zNum`, the gap being that candidate's distance from the
    scaled value, and the lower end of the round-trip interval is free because
    a gap is never negative. -/
theorem round_down_iff_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundDown = true
      ↔ Roundtrips f e (integralPart f e * 10 ^ (decimalExponent e + 1)) := by
  rw [round_down_iff_gap f e hr,
    roundtrips_iff_dist f e hr.range
      (integral_scaled f e (exponent_shift_range e hr.range).2)]
  split_ifs <;> omega

/-- `roundUp` fires exactly when the successor round-trips. Its distance is
    signed, and the upper end of the interval is free because the gap never
    passes a whole step. -/
theorem round_up_iff_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundUp = true
      ↔ Roundtrips f e ((integralPart f e + 1 : ℕ) * 10 ^ (decimalExponent e + 1)) := by
  have hle := gap_le_mul f e hr
  have hnum : 0 < zNum e := by
    have := (z_num_bounds e hr.range).1
    have h : 0 < 2 ^ 127 * zDen e := by
      have := z_den_pos e
      positivity
    omega
  rw [round_up_iff_gap f e hr,
    roundtrips_iff_dist f e hr.range
      (successor_scaled f e (exponent_shift_range e hr.range).2)]
  split_ifs <;> omega

/-! ## The derived digit

Ten times the fraction word, rounded, is Żmij's last digit, and the `+6` in
`biasedHalf` is the rest of the error budget: it stands in for the part of the
gap the fraction word dropped, which is worth up to ten of the units the digit
is decided in. So the digit is a nearest one except within ten units of a digit
boundary, where a `+6` can be wrong by six either way.

What closes those cases is how rigid they are. Reaching a boundary asks twenty
times the fraction word to come within twenty of a multiple of `2^64`, and since
the fraction word also fixes the digit, that leaves eleven possible fraction
words in all, each an explicit constant. Each one fixes how much of the
truncation the `+6` would have to have got right, which is a bound on the
remainder below one fraction unit, and the certificates below say no significand
meets it. What survives is the exact midpoint at a quarter, where the truncation
vanishes and the digit is two: that is the tie, and Żmij's special case rounds
it to even.
-/

/-- What the fraction word and the truncation are read off: the cleared product
    below the integral part, the fraction word above one unit and the remainder
    below it. Both digit boundaries constrain the two together, so both are
    stated about this. -/
def zRes (f : ℕ) (e : ℤ) : ℕ := f * zSig e % (zUnit e * 2 ^ 64)

/-- Its two halves. -/
theorem z_res_split (f : ℕ) (e : ℤ) (hs : exponentShift e ≤ 9) :
    zRes f e = zUnit e * fractionalPart f e + f * zSig e % zUnit e := by
  have hdiv : f * zSig e % (zUnit e * 2 ^ 64) / zUnit e
      = f * zSig e / zUnit e % 2 ^ 64 := Nat.mod_mul_right_div_self _ _ _
  have hmod : f * zSig e % (zUnit e * 2 ^ 64) % zUnit e = f * zSig e % zUnit e :=
    Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)
  have hsplit := Nat.div_add_mod (f * zSig e % (zUnit e * 2 ^ 64)) (zUnit e)
  rw [hdiv, hmod] at hsplit
  rw [zRes, ← hsplit, fraction_quotient f e hs]

/-- Twice the signed distance from Żmij's fine output to the exact value, on the
    grid at `k` and cleared by `zMul`: the digit accounts for ten times the gap,
    and this is what it leaves. -/
def zDigitDist (f : ℕ) (e : ℤ) : ℤ :=
  20 * (zGap f e : ℤ) - 2 * (toDecimalCandidates f e).digit * zMul e

/-- The truncation stays under one fraction unit with room to spare: the
    remainder below the unit accounts for nearly all of it and the power-of-ten
    truncation for at most `2^53` denominators, which one unit dwarfs. -/
theorem z_err_lt (f : ℕ) (e : ℤ) (hr : Regular f e) :
    20 * zErr f e < 21 * zEdge e := by
  have hden := z_den_pos e
  have hunit : 20 * 2 ^ 53 ≤ zUnit e := by
    have hs := (exponent_shift_range e hr.range).2
    rw [zUnit]
    calc 20 * 2 ^ 53 ≤ 2 ^ 64 := by norm_num
      _ ≤ 2 ^ (73 - exponentShift e) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  -- The remainder below one unit, with the denominator cleared, is one unit
  -- short of the whole edge.
  have hrest : zDen e * (f * zSig e % zUnit e) + zDen e ≤ zEdge e := by
    have h : f * zSig e % zUnit e + 1 ≤ zUnit e := by
      have := Nat.mod_lt (f * zSig e) (z_unit_pos e)
      omega
    rw [zEdge]
    calc zDen e * (f * zSig e % zUnit e) + zDen e
        = zDen e * (f * zSig e % zUnit e + 1) := by ring
      _ ≤ zDen e * zUnit e := Nat.mul_le_mul (le_refl _) h
      _ = zUnit e * zDen e := by ring
  -- The power-of-ten truncation is smaller still, by a whole unit.
  have htau : 20 * (f * (zNum e % zDen e)) + zUnit e ≤ zEdge e := by
    have h1 : 20 * f ≤ zUnit e := by have := hr.sig_lt; omega
    have h2 : zNum e % zDen e ≤ zDen e - 1 := by
      have := Nat.mod_lt (zNum e) hden
      omega
    have hsucc : zDen e - 1 + 1 = zDen e := by omega
    rw [zEdge]
    calc 20 * (f * (zNum e % zDen e)) + zUnit e
        = 20 * f * (zNum e % zDen e) + zUnit e := by ring
      _ ≤ zUnit e * (zDen e - 1) + zUnit e :=
          Nat.add_le_add_right (Nat.mul_le_mul h1 h2) _
      _ = zUnit e * (zDen e - 1 + 1) := by ring
      _ = zUnit e * zDen e := by rw [hsucc]
  have := z_unit_pos e
  rw [zErr]
  omega

/-- A bound on the truncation is a bound on the remainder below one unit: the
    denominator divides out of both. -/
private theorem res_le_of_err (f : ℕ) (e : ℤ) {a : ℕ}
    (h : 20 * zErr f e ≤ a * zEdge e) :
    20 * (f * zSig e % zUnit e) ≤ a * zUnit e := by
  refine Nat.le_of_mul_le_mul_left ?_ (z_den_pos e)
  calc zDen e * (20 * (f * zSig e % zUnit e))
      = 20 * (zDen e * (f * zSig e % zUnit e)) := by ring
    _ ≤ 20 * zErr f e := by rw [zErr]; omega
    _ ≤ a * zEdge e := h
    _ = zDen e * (a * zUnit e) := by rw [zEdge]; ring

/-- And conversely, up to what the power-of-ten truncation can contribute. -/
private theorem res_ge_of_err (f : ℕ) (e : ℤ) (hr : Regular f e) {a : ℕ}
    (h : a * zEdge e ≤ 20 * zErr f e) :
    a * zUnit e ≤ 20 * (f * zSig e % zUnit e) + 20 * 2 ^ 53 := by
  have htau : f * (zNum e % zDen e) ≤ 2 ^ 53 * zDen e := by
    have h1 : f ≤ 2 ^ 53 := by have := hr.sig_lt; omega
    have h2 : zNum e % zDen e ≤ zDen e := le_of_lt (Nat.mod_lt _ (z_den_pos e))
    exact Nat.mul_le_mul h1 h2
  refine Nat.le_of_mul_le_mul_left ?_ (z_den_pos e)
  calc zDen e * (a * zUnit e) = a * zEdge e := by rw [zEdge]; ring
    _ ≤ 20 * zErr f e := h
    _ ≤ zDen e * (20 * (f * zSig e % zUnit e) + 20 * 2 ^ 53) := by
        rw [zErr]
        calc 20 * (zDen e * (f * zSig e % zUnit e) + f * (zNum e % zDen e))
            = zDen e * (20 * (f * zSig e % zUnit e))
              + 20 * (f * (zNum e % zDen e)) := by ring
          _ ≤ zDen e * (20 * (f * zSig e % zUnit e))
              + 20 * (2 ^ 53 * zDen e) := by omega
          _ = zDen e * (20 * (f * zSig e % zUnit e) + 20 * 2 ^ 53) := by ring

/-- The six fraction words that can reach a digit boundary from below, each with
    how far the truncation would have to reach for it to happen, in fifths of a
    fraction unit. -/
private def digitLowEdges : List (ℕ × ℕ) :=
  [(8301034833169298227, 1), (17524406870024074035, 1),
    (2767011611056432742, 2), (11990383647911208550, 2),
    (6456360425798343065, 3), (15679732462653118873, 3)]

/-- And the five that can reach one from above. The first is the quarter Żmij
    special-cases, where the reach needed is nothing at all: only the exact
    midpoint survives, so only a vanishing truncation does. -/
private def digitHighEdges : List (ℕ × ℕ) :=
  [(4611686018427387904, 0), (922337203685477580, 4),
    (10145709240540253388, 4), (4611686018427387903, 5),
    (13835058055282163711, 5)]

private def digitLowWindows (e : ℤ) : ModWindows where
  g := zSig e
  modulus := zUnit e * 2 ^ 64
  f0 := if e = -1074 then 1 else 2 ^ 52 + 1
  f1 := 2 ^ 53 - 1
  windows := digitLowEdges.map fun p =>
    ((zUnit e : ℤ) * p.1, (zUnit e : ℤ) * p.1 + p.2 * (zUnit e : ℤ) / 5)

private def digitHighWindows (e : ℤ) : ModWindows where
  g := zSig e
  modulus := zUnit e * 2 ^ 64
  f0 := if e = -1074 then 1 else 2 ^ 52 + 1
  f1 := 2 ^ 53 - 1
  windows := digitHighEdges.map fun p =>
    ((zUnit e : ℤ) * p.1
        + max (p.2 * (zUnit e : ℤ) / 5 - 2 ^ 53)
            (if zNum e % zDen e = 0 then 1 else 0),
      (zUnit e : ℤ) * p.1 + zUnit e - 1)

/-- Close the two digit certificates for a literal exponent. -/
elab "digit_low_cert" : tactic => modCertTactic fun e => (digitLowWindows e).search

elab "digit_high_cert" : tactic => modCertTactic fun e => (digitHighWindows e).search

private theorem digit_low_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (digitLowWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> digit_low_cert

private theorem digit_high_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (digitHighWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> digit_high_cert

/-- A fraction word together with a bound on the remainder below the unit is a
    point of `zRes`, which is the residue of `f·sig` modulo one coarse step, so
    a refuted window rules the pair out. -/
private theorem no_res_hit {lo hi q : ℤ} (f : ℕ) (e : ℤ) (hr : Regular f e)
    (W : ModWindows) (hg : W.g = zSig e) (hm : W.modulus = zUnit e * 2 ^ 64)
    (hf0 : W.f0 = if e = -1074 then 1 else 2 ^ 52 + 1) (hf1 : W.f1 = 2 ^ 53 - 1)
    (hcert : W.refutedBy q = true) (hmem : (lo, hi) ∈ W.windows)
    (hlo : lo ≤ (zRes f e : ℤ)) (hhi : (zRes f e : ℤ) ≤ hi) : False := by
  have h0 : W.f0 ≤ f := by
    rw [hf0]
    split_ifs with hcase
    · exact hr.pos
    · rcases hr.1.2.2 with h | h
      · omega
      · exact absurd h hcase
  have h1 : f ≤ W.f1 := by
    rw [hf1]
    have := hr.sig_lt
    omega
  have hmod : 0 < W.modulus := by
    rw [hm]
    have := z_unit_pos e
    positivity
  exact W.not_hit f hmod hcert hmem h0 h1
    (by rw [hg, hm, zRes, Nat.mul_comm]) hlo hhi

/-- No significand pairs one of the six low fraction words with a truncation
    that reaches the boundary. -/
private theorem no_digit_low (f : ℕ) (e : ℤ) (hr : Regular f e) {w j : ℕ}
    (hmem : (w, j) ∈ digitLowEdges) (hφ : fractionalPart f e = w)
    (hb : 20 * (f * zSig e % zUnit e) ≤ 4 * j * zUnit e) : False := by
  obtain ⟨q, hcert⟩ := digit_low_refuted e hr.range
  have hres : (zRes f e : ℤ)
      = (zUnit e : ℤ) * w + (f * zSig e % zUnit e : ℕ) := by
    rw [z_res_split f e (exponent_shift_range e hr.range).2, hφ]
    push_cast
    ring
  have hdiv : ((f * zSig e % zUnit e : ℕ) : ℤ) ≤ (j : ℤ) * (zUnit e : ℤ) / 5 := by
    refine Int.le_ediv_of_mul_le (by norm_num) ?_
    have : (20 : ℤ) * (f * zSig e % zUnit e : ℕ) ≤ 4 * j * (zUnit e : ℤ) := by
      exact_mod_cast hb
    linarith
  have hmem' : ((zUnit e : ℤ) * w, (zUnit e : ℤ) * w + (j : ℤ) * (zUnit e : ℤ) / 5)
      ∈ (digitLowWindows e).windows :=
    List.mem_map_of_mem (l := digitLowEdges) (f := fun p : ℕ × ℕ =>
      ((zUnit e : ℤ) * p.1, (zUnit e : ℤ) * p.1 + p.2 * (zUnit e : ℤ) / 5)) hmem
  exact no_res_hit f e hr (digitLowWindows e) rfl rfl rfl rfl hcert hmem'
    (by rw [hres]; omega) (by rw [hres]; omega)

/-- Nor with one of the five high words, the quarter included: there the
    truncation has to vanish, and it does not. -/
private theorem no_digit_high (f : ℕ) (e : ℤ) (hr : Regular f e) {w j : ℕ}
    (hmem : (w, j) ∈ digitHighEdges) (hφ : fractionalPart f e = w)
    (hb : 4 * j * zUnit e ≤ 20 * (f * zSig e % zUnit e) + 20 * 2 ^ 53)
    (hpos : 0 < zErr f e) : False := by
  obtain ⟨q, hcert⟩ := digit_high_refuted e hr.range
  have hres : (zRes f e : ℤ)
      = (zUnit e : ℤ) * w + (f * zSig e % zUnit e : ℕ) := by
    rw [z_res_split f e (exponent_shift_range e hr.range).2, hφ]
    push_cast
    ring
  have hunit : (0 : ℤ) < zUnit e := by exact_mod_cast z_unit_pos e
  have hdiv : (j : ℤ) * (zUnit e : ℤ) / 5 - 2 ^ 53
      ≤ ((f * zSig e % zUnit e : ℕ) : ℤ) := by
    have hb' : 4 * (j : ℤ) * (zUnit e : ℤ)
        ≤ 20 * (f * zSig e % zUnit e : ℕ) + 20 * 2 ^ 53 := by exact_mod_cast hb
    have := Int.ediv_le_ediv (by norm_num : (0 : ℤ) < 5)
      (show (j : ℤ) * (zUnit e : ℤ)
        ≤ 5 * (((f * zSig e % zUnit e : ℕ) : ℤ) + 2 ^ 53) from by linarith)
    rw [Int.mul_ediv_cancel_left _ (by norm_num)] at this
    omega
  -- The truncation is positive, so the remainder is too unless the power of ten
  -- is exact, which is the only case the window's own lower end has to cover.
  have hone : (if zNum e % zDen e = 0 then (1 : ℤ) else 0)
      ≤ ((f * zSig e % zUnit e : ℕ) : ℤ) := by
    split_ifs with hτ
    · rcases Nat.eq_zero_or_pos (f * zSig e % zUnit e) with hz | hz
      · rw [zErr, hτ, hz] at hpos
        simp at hpos
      · exact_mod_cast hz
    · positivity
  have hlt : ((f * zSig e % zUnit e : ℕ) : ℤ) ≤ (zUnit e : ℤ) - 1 := by
    have := Nat.mod_lt (f * zSig e) (z_unit_pos e)
    omega
  have hmem' : ((zUnit e : ℤ) * w
        + max ((j : ℤ) * (zUnit e : ℤ) / 5 - 2 ^ 53)
            (if zNum e % zDen e = 0 then 1 else 0),
      (zUnit e : ℤ) * w + zUnit e - 1) ∈ (digitHighWindows e).windows :=
    List.mem_map_of_mem (l := digitHighEdges) (f := fun p : ℕ × ℕ =>
      ((zUnit e : ℤ) * p.1
          + max (p.2 * (zUnit e : ℤ) / 5 - 2 ^ 53)
              (if zNum e % zDen e = 0 then 1 else 0),
        (zUnit e : ℤ) * p.1 + zUnit e - 1)) hmem
  exact no_res_hit f e hr (digitHighWindows e) rfl rfl rfl rfl hcert hmem'
    (by rw [hres]
        rcases max_cases ((j : ℤ) * (zUnit e : ℤ) / 5 - 2 ^ 53)
            (if zNum e % zDen e = 0 then (1 : ℤ) else 0) with ⟨h, -⟩ | ⟨h, -⟩ <;>
          rw [h] <;> omega)
    (by rw [hres]; omega)

/-- The biased quotient bounds the offset of twenty times the fraction word from
    the digit boundary below it: the `+6` is worth twelve of those units, so the
    offset can fall short of that boundary by at most twelve and of the one
    above by at least thirteen. -/
private theorem digit_offset_bounds {φ d m : ℕ} {v : ℤ} (hφ : φ < 2 ^ 64)
    (hfloor : 2 ^ 64 * d + m = φ * 10 + (2 ^ 63 + 6)) (hm : m < 2 ^ 64)
    (hv : v = 20 * φ + 2 ^ 64 - 2 * d * 2 ^ 64) :
    d ≤ 10 ∧ -12 ≤ v ∧ v ≤ 2 ^ 65 - 13 := by
  omega

/-- Falling short of the boundary below makes the offset a negative multiple of
    four, and since the fraction word fixes the digit too, each of its three
    values leaves two possible fraction words. -/
private theorem digit_low_cases {φ d : ℕ} {v : ℤ} (hφ : φ < 2 ^ 64)
    (hd : d ≤ 10) (hv : v = 20 * φ + 2 ^ 64 - 2 * d * 2 ^ 64)
    (hlo : -12 ≤ v) (hhi : v < 0) :
    ∃ w j : ℕ, (w, j) ∈ digitLowEdges ∧ (φ : ℤ) = w ∧ v = -(4 * (j : ℤ)) := by
  interval_cases d <;>
    first
      | omega
      | exact ⟨8301034833169298227, 1, by decide, by omega, by omega⟩
      | exact ⟨17524406870024074035, 1, by decide, by omega, by omega⟩
      | exact ⟨2767011611056432742, 2, by decide, by omega, by omega⟩
      | exact ⟨11990383647911208550, 2, by decide, by omega, by omega⟩
      | exact ⟨6456360425798343065, 3, by decide, by omega, by omega⟩
      | exact ⟨15679732462653118873, 3, by decide, by omega, by omega⟩

/-- Reaching past the boundary above leaves four, the quarter aside. -/
private theorem digit_high_cases {φ d : ℕ} {v : ℤ} (hφ : φ < 2 ^ 64)
    (hd : d ≤ 10) (hv : v = 20 * φ + 2 ^ 64 - 2 * d * 2 ^ 64)
    (hlo : 2 ^ 65 - 20 ≤ v) (hhi : v ≤ 2 ^ 65 - 13) :
    ∃ w j : ℕ, (w, j) ∈ digitHighEdges ∧ (φ : ℤ) = w
      ∧ v = 2 ^ 65 - 4 * (j : ℤ) := by
  interval_cases d <;>
    first
      | omega
      | exact ⟨922337203685477580, 4, by decide, by omega, by omega⟩
      | exact ⟨10145709240540253388, 4, by decide, by omega, by omega⟩
      | exact ⟨4611686018427387903, 5, by decide, by omega, by omega⟩
      | exact ⟨13835058055282163711, 5, by decide, by omega, by omega⟩

/-- A vanishing offset is an exact midpoint, and the only one Żmij does not
    special-case is three quarters, whose digit is eight. -/
private theorem digit_mid_even {φ d : ℕ} (hφ : φ < 2 ^ 64) (hd : d ≤ 10)
    (hsp : φ ≠ 2 ^ 62) (hv : (0 : ℤ) = 20 * φ + 2 ^ 64 - 2 * d * 2 ^ 64) :
    d % 2 = 0 := by
  interval_cases d <;> omega

/-- Żmij's digit is a nearest one on the grid at `k`, ties to even. Away from a
    boundary the `+6` cannot matter; at one the fraction word is one of eleven
    constants, and all but the quarter are refuted. -/
theorem digit_nearest (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (-(zMul e : ℤ) ≤ zDigitDist f e ∧ zDigitDist f e ≤ zMul e)
      ∧ (zDigitDist f e = zMul e ∨ zDigitDist f e = -(zMul e : ℤ)
          → (toDecimalCandidates f e).digit % 2 = 0) := by
  have hs := (exponent_shift_range e hr.range).2
  have hedge : (0 : ℤ) < zEdge e := by exact_mod_cast z_edge_pos e
  have herr : (0 : ℤ) ≤ (zErr f e : ℤ) := Int.natCast_nonneg _
  have herrlt : 20 * (zErr f e : ℤ) < 21 * zEdge e := by
    exact_mod_cast z_err_lt f e hr
  have hmul : (zMul e : ℤ) = zEdge e * 2 ^ 64 := by exact_mod_cast z_mul_eq_edge e
  obtain ⟨φ, hφ⟩ : ∃ φ, fractionalPart f e = φ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, (toDecimalCandidates f e).digit = d := ⟨_, rfl⟩
  have hφlt : φ < 2 ^ 64 := by
    rw [← hφ, fractionalPart]
    exact Nat.mod_lt _ (by norm_num)
  -- Twenty times the fraction word, less the boundary below it: the whole
  -- argument is a comparison of this offset against the truncation.
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = 20 * φ + 2 ^ 64 - 2 * d * 2 ^ 64 := ⟨_, rfl⟩
  have hidlo : zDigitDist f e + zMul e = zEdge e * v + 20 * zErr f e := by
    have hgap : (zGap f e : ℤ) = zEdge e * φ + zErr f e := by
      rw [← hφ]
      exact_mod_cast gap_eq_edge_fraction f e hs
    rw [zDigitDist, hd, hgap, hmul, hv]
    push_cast
    ring
  have hidhi : zDigitDist f e - zMul e
      = zEdge e * (v - 2 ^ 65) + 20 * zErr f e := by
    linear_combination hidlo - 2 * hmul
  -- Name the two sides so that the bounds below are linear in them.
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = zEdge e * v + 20 * zErr f e := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = zEdge e * (v - 2 ^ 65) + 20 * zErr f e := ⟨_, rfl⟩
  rw [← hA] at hidlo
  rw [← hB] at hidhi
  have hmulpos : (0 : ℤ) < zMul e := by exact_mod_cast z_mul_pos e
  rw [hd]
  by_cases hsp : φ = 2 ^ 62
  · -- The quarter: the one exact midpoint, whose digit Żmij rounds to even.
    have hd2 : d = 2 := by
      rw [← hd, toDecimalCandidates]
      dsimp only
      rw [hφ]
      simp only [hsp, ite_true]
    have hv2 : v = 2 ^ 65 := by rw [hv, hsp, hd2]; ring
    have hzero : zErr f e = 0 := by
      by_contra hne
      exact no_digit_high f e hr (w := 4611686018427387904) (j := 0) (by decide)
        (hφ.trans hsp) (by omega) (by omega)
    have hB0 : B = 0 := by
      rw [hB, hv2, show ((zErr f e : ℕ) : ℤ) = 0 from by rw [hzero]; rfl]
      ring
    exact ⟨⟨by omega, by omega⟩, fun _ => by omega⟩
  -- Away from it the digit is the biased quotient, which bounds the offset both
  -- ways: the `+6` is worth twelve of the doubled units, so the offset misses
  -- the boundary below by at most that and the one above by at least it.
  have hdq : d = (φ * 10 + biasedHalf) / 2 ^ 64 := by
    rw [← hd, toDecimalCandidates]
    dsimp only
    rw [hφ]
    simp only [hsp, ite_false]
  rw [biasedHalf] at hdq
  obtain ⟨hd10, hvlo, hvhi⟩ :=
    digit_offset_bounds (m := (φ * 10 + (2 ^ 63 + 6)) % 2 ^ 64) hφlt
      (by rw [hdq]; exact Nat.div_add_mod _ _) (Nat.mod_lt _ (by norm_num)) hv
  clear hdq
  by_cases hneg : v < 0
  · -- Below the boundary.
    obtain ⟨w, j, hmem, hw, hvj⟩ := digit_low_cases hφlt hd10 hv hvlo hneg
    have hfar : 0 < A := by
      by_contra hcon0
      have hcon := not_lt.mp hcon0
      rw [hA, hvj] at hcon
      refine no_digit_low f e hr hmem (by omega) (res_le_of_err f e ?_)
      have h : 20 * (zErr f e : ℤ) ≤ 4 * (j : ℤ) * zEdge e := by linarith
      exact_mod_cast h
    have hbelow : B < 0 := by
      have h : zEdge e * (v - 2 ^ 65) ≤ zEdge e * (-(2 ^ 65)) :=
        mul_le_mul_of_nonneg_left (by omega) (le_of_lt hedge)
      rw [hB]
      linarith
    exact ⟨⟨by omega, by omega⟩, fun h => by omega⟩
  by_cases hpos : 2 ^ 65 - 20 ≤ v
  · -- Above it.
    obtain ⟨w, j, hmem, hw, hvj⟩ := digit_high_cases hφlt hd10 hv hpos hvhi
    have hj : 4 ≤ j := by omega
    have hfar : B < 0 := by
      by_contra hcon0
      have hcon := not_lt.mp hcon0
      rw [hB, hvj] at hcon
      have hreach : 4 * j * zEdge e ≤ 20 * zErr f e := by
        have h : (4 * j * zEdge e : ℤ) ≤ 20 * (zErr f e : ℤ) := by linarith
        exact_mod_cast h
      have hjpos : 0 < 4 * j * zEdge e :=
        Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (z_edge_pos e)
      exact no_digit_high f e hr hmem (by omega)
        (res_ge_of_err f e hr hreach) (by omega)
    have habove : 0 < A := by
      have h : zEdge e * (2 ^ 65 - 20) ≤ zEdge e * v :=
        mul_le_mul_of_nonneg_left hpos (le_of_lt hedge)
      rw [hA]
      linarith
    exact ⟨⟨by omega, by omega⟩, fun h => by omega⟩
  -- Everywhere else the offset clears the truncation on both sides. The one
  -- exception is a vanishing offset, which is an exact midpoint: there the
  -- fraction word is three quarters and the digit is eight.
  have hedgev : 0 ≤ zEdge e * v := mul_nonneg (le_of_lt hedge) (by omega)
  have hbelow : B < 0 := by
    have h : zEdge e * (v - 2 ^ 65) ≤ zEdge e * (-21) :=
      mul_le_mul_of_nonneg_left (by omega) (le_of_lt hedge)
    rw [hB]
    linarith
  have habove : 0 ≤ A := by rw [hA]; omega
  refine ⟨⟨by omega, by omega⟩, fun h => ?_⟩
  -- A midpoint forces the offset to vanish, and only one fraction word does.
  have hv0 : v = 0 := by
    have hz : zEdge e * v = 0 := by rw [hA] at habove hidlo; omega
    rcases mul_eq_zero.mp hz with h' | h'
    · omega
    · exact h'
  exact digit_mid_even hφlt hd10 hsp (by rw [← hv0]; exact hv)

/-! ## The grid at k

Everything so far has been stated on the grid at `k+1`, where the coarse
candidates live, or in cleared integers. The exact method asks for the grid at
`k`, one power of ten finer: `10^(-k) = 10·10^K`. Two things have to be said
there. One ULP has to fall between one and ten steps of it, which is what makes
`k` the right exponent to report and is checked per exponent. And Żmij's output
has to be read on it: the coarse candidates as multiples of ten, and the fine
one as the integral part with the digit appended.
-/

/-- The power of ten is normalized against the grid step: one ULP is `10·zNum`
    of the `zMul` the step is worth, so it is at least one step and less than
    ten. -/
def zGridHolds (e : ℤ) : Bool :=
  decide (zNum e < zMul e ∧ zMul e ≤ 10 * zNum e)

theorem z_grid_all : ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, zGridHolds e = true := by
  decide +kernel

theorem z_grid (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    zNum e < zMul e ∧ zMul e ≤ 10 * zNum e := by
  have hcert := z_grid_all e (by simpa [Finset.mem_Icc] using he)
  simpa only [zGridHolds, decide_eq_true_eq] using hcert

theorem z_num_pos (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) : 0 < zNum e := by
  have hlow := (z_num_bounds e he).1
  have h : 0 < 2 ^ 127 * zDen e := by
    have := z_den_pos e
    positivity
  omega

/-- The grid at `k` is the one at `k+1` scaled by ten. -/
private theorem z_grid_pow (e : ℤ) :
    (10 : ℚ) ^ (-decimalExponent e) = 10 * 10 ^ powerIndex e := by
  rw [show -decimalExponent e = powerIndex e + 1 from by rw [powerIndex]; ring,
    zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0)]
  ring

/-- The value on the grid at `k`, cleared by `zMul`. -/
theorem z_value_scaled_grid (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    value f e * 10 ^ (-decimalExponent e) * (zMul e : ℚ)
      = ((10 * (f * zNum e) : ℕ) : ℚ) := by
  have h := z_value_scaled f e he
  rw [z_grid_pow]
  push_cast at h ⊢
  linear_combination 10 * h

/-- Half a ULP on the grid at `k`, cleared: five `zNum`. -/
theorem z_half_ulp_grid (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ulp e * 10 ^ (-decimalExponent e) / 2 * (zMul e : ℚ)
      = ((5 * zNum e : ℕ) : ℚ) := by
  have h := z_half_ulp_scaled e he
  rw [z_grid_pow]
  push_cast at h ⊢
  linear_combination 5 * h

/-- One ULP is at least one step of the grid at `k` and less than ten. This is
    the one obligation of the exact method that is about `k` alone. -/
theorem ulp_scaled_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    1 ≤ ulp e * 10 ^ (-decimalExponent e)
      ∧ ulp e * 10 ^ (-decimalExponent e) < 10 := by
  have hpos : (0 : ℚ) < (zMul e : ℚ) := by exact_mod_cast z_mul_pos e
  have hstep : ulp e * 10 ^ (-decimalExponent e) * (zMul e : ℚ)
      = 10 * (zNum e : ℚ) := by
    have h := z_half_ulp_grid e he
    push_cast at h
    linear_combination 2 * h
  obtain ⟨hhigh, hlow⟩ := z_grid e he
  refine ⟨(mul_le_mul_iff_of_pos_right hpos).mp ?_,
    (mul_lt_mul_iff_of_pos_right hpos).mp ?_⟩
  · rw [one_mul, hstep]
    exact_mod_cast hlow
  · rw [hstep]
    exact_mod_cast (by omega : 10 * zNum e < 10 * zMul e)

/-- Żmij's significand: the integral part on the grid at `k`, with the digit
    appended unless a coarse candidate was taken. -/
theorem to_decimal_fst (f : ℕ) (e : ℤ) :
    (toDecimal f e).1
      = (integralPart f e
            + (if (toDecimalCandidates f e).roundUp then 1 else 0)) * 10
        + (if (toDecimalCandidates f e).roundUp
              || (toDecimalCandidates f e).roundDown
            then 0 else (toDecimalCandidates f e).digit) := rfl

/-- A coarse candidate seen on the grid at `k`: ten times its significand one
    grid up. -/
private theorem roundtrips_ten (f : ℕ) (e : ℤ) (c d : ℕ) (h : d = c * 10) :
    Roundtrips f e (d * 10 ^ decimalExponent e)
      ↔ Roundtrips f e (c * 10 ^ (decimalExponent e + 1)) := by
  rw [show (d : ℚ) * 10 ^ decimalExponent e
      = (c : ℚ) * 10 ^ (decimalExponent e + 1) from by
    rw [zpow_add_one₀ (by norm_num : (10 : ℚ) ≠ 0), h]
    push_cast
    ring]

/-! ## Żmij trims whenever it can

The exact method takes the coarse case exactly when the rounding interval
contains a multiple of ten, that is, when a digit can be dropped. Żmij makes
the same choice through `roundDown` and `roundUp`: it trims when either of its
two coarse candidates round-trips, which is what `round_down_iff_roundtrips`
and `round_up_iff_roundtrips` already say. All that is left is to rule out any
other multiple of ten, and the rounding interval is too narrow to hold one.
-/

/-- A multiple of ten that round-trips is one of Żmij's two coarse candidates.
    Cleared by `zMul`, the lower one sits `10·zGap` below the scaled value, and
    that gap is under one step of the coarse grid, let alone one step plus half
    a ULP. This bracket is all `coarse_roundtrip_adjacent` needs. -/
theorem coarse_candidate_cases (f : ℕ) (e : ℤ) (hr : Regular f e) (d : ℕ)
    (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ decimalExponent e)) :
    d = integralPart f e * 10 ∨ d = integralPart f e * 10 + 10 := by
  have hmul : (0 : ℚ) < (zMul e : ℚ) := by exact_mod_cast z_mul_pos e
  have hval := z_value_scaled_grid f e hr.range
  have hhalf := z_half_ulp_grid e hr.range
  have hid : (integralPart f e : ℚ) * (zMul e : ℚ) + (zGap f e : ℚ)
      = (f : ℚ) * (zNum e : ℚ) := by
    exact_mod_cast integral_add_gap f e (exponent_shift_range e hr.range).2
  have hgap0 : (0 : ℚ) ≤ (zGap f e : ℚ) := by positivity
  have hnum0 : (0 : ℚ) < (zNum e : ℚ) := by exact_mod_cast z_num_pos e hr.range
  have hgaple : (zGap f e : ℚ) ≤ (zMul e : ℚ) := by
    exact_mod_cast gap_le_mul f e hr
  push_cast at hval hhalf
  exact coarse_roundtrip_adjacent f e (decimalExponent e)
    (ulp_scaled_bounds e hr.range).2 (by omega) h10
    (le_of_mul_le_mul_right (by push_cast; linarith) hmul)
    (lt_of_mul_lt_mul_right (by push_cast; linarith) hmul.le) hround

/-- If the rounding interval contains a multiple of ten, Żmij trims. -/
theorem trim_of_coarse_roundtrip (f : ℕ) (e : ℤ) (hr : Regular f e) (d : ℕ)
    (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ decimalExponent e)) :
    ((toDecimalCandidates f e).roundUp
      || (toDecimalCandidates f e).roundDown) = true := by
  rw [Bool.or_eq_true]
  rcases coarse_candidate_cases f e hr d h10 hround with rfl | rfl
  · exact Or.inr ((round_down_iff_roundtrips f e hr).mpr
      ((roundtrips_ten f e (integralPart f e) _ rfl).mp hround))
  · exact Or.inl ((round_up_iff_roundtrips f e hr).mpr
      ((roundtrips_ten f e (integralPart f e + 1) _ (by ring)).mp hround))

/-- Trimmed output is a multiple of ten that round-trips: it is whichever of the
    two coarse candidates fired. -/
theorem coarse_output_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e)
    (htrim : ((toDecimalCandidates f e).roundUp
      || (toDecimalCandidates f e).roundDown) = true) :
    (toDecimal f e).1 % 10 = 0
      ∧ Roundtrips f e ((toDecimal f e).1 * 10 ^ decimalExponent e) := by
  have hd : (toDecimal f e).1
      = (integralPart f e
          + (if (toDecimalCandidates f e).roundUp then 1 else 0)) * 10 := by
    rw [to_decimal_fst, htrim]
    simp
  rw [hd]
  refine ⟨by omega, ?_⟩
  cases hu : (toDecimalCandidates f e).roundUp
  · -- Only `roundDown` fired, so the integral part itself round-trips.
    have hdown : (toDecimalCandidates f e).roundDown = true := by
      rw [hu, Bool.false_or] at htrim
      exact htrim
    exact (roundtrips_ten f e (integralPart f e) _ (by simp)).mpr
      ((round_down_iff_roundtrips f e hr).mp hdown)
  · exact (roundtrips_ten f e (integralPart f e + 1) _ (by simp)).mpr
      ((round_up_iff_roundtrips f e hr).mp hu)

/-- Untrimmed output is a nearest candidate on the grid at `k`, ties to even:
    the integral part accounts for ten times its own distance and the digit for
    the rest, which is `digit_nearest`. -/
theorem fine_output_nearest (f : ℕ) (e : ℤ) (hr : Regular f e)
    (htrim : ((toDecimalCandidates f e).roundUp
      || (toDecimalCandidates f e).roundDown) = false) :
    let x := value f e * 10 ^ (-decimalExponent e)
    |((toDecimal f e).1 : ℚ) - x| ≤ 1 / 2
      ∧ (|((toDecimal f e).1 : ℚ) - x| = 1 / 2 → (toDecimal f e).1 % 2 = 0) := by
  intro x
  have hu : (toDecimalCandidates f e).roundUp = false :=
    (Bool.or_eq_false_iff.mp htrim).1
  have hd : (toDecimal f e).1
      = integralPart f e * 10 + (toDecimalCandidates f e).digit := by
    rw [to_decimal_fst, htrim, hu]
    simp
  have hid : (integralPart f e : ℤ) * zMul e + zGap f e = f * zNum e := by
    exact_mod_cast integral_add_gap f e (exponent_shift_range e hr.range).2
  obtain ⟨hle, -, heq⟩ := scaled_cmp_of_int_eq (c := (toDecimal f e).1)
    (m := zMul e) (a := 2) (b := zMul e) (x := x) (thr := 1 / 2)
    (dist := 10 * (zGap f e : ℤ) - (toDecimalCandidates f e).digit * zMul e)
    (z_mul_pos e) two_pos (z_value_scaled_grid f e hr.range) (by push_cast; ring)
    (by rw [hd]; push_cast; linear_combination 10 * hid)
  have hdd : 2 * (10 * (zGap f e : ℤ)
      - (toDecimalCandidates f e).digit * zMul e) = zDigitDist f e := by
    rw [zDigitDist]
    ring
  push_cast at hle heq
  rw [hdd] at hle heq
  obtain ⟨⟨hlo, hhi⟩, heven⟩ := digit_nearest f e hr
  refine ⟨hle.mpr ⟨hlo, hhi⟩, fun h => ?_⟩
  have hdig := heven (heq.mp h)
  omega

/-! ## Żmij refines the exact method

Nothing above is needed beyond `ulp_scaled_bounds` and the three semantic
obligations `coarse_output_roundtrips`, `fine_output_nearest`, and
`trim_of_coarse_roundtrip`. In particular no claim is made that Żmij's packed
decisions agree with the exact ones: its truncated comparisons are matched to
the existence of an exact coarse candidate, not to any exact comparison, and
its one special case is a packed midpoint rather than an exact one.
-/

/-- Żmij implements the exact method: it trims exactly when an exact coarse
    candidate exists. One direction is `trim_of_coarse_roundtrip`; the other
    holds because trimmed output is itself a multiple of ten that
    round-trips. -/
theorem exact_candidate (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let (d, k) := toDecimal f e
    ExactCandidate f e k d := by
  show ExactCandidate f e (decimalExponent e) (toDecimal f e).1
  by_cases htrim : ((toDecimalCandidates f e).roundUp
      || (toDecimalCandidates f e).roundDown) = true
  · exact Or.inl (coarse_output_roundtrips f e hr htrim)
  · rw [Bool.not_eq_true] at htrim
    obtain ⟨hle, heven⟩ := fine_output_nearest f e hr htrim
    refine Or.inr ⟨fun ⟨d, h10, hround⟩ => ?_, hle, heven⟩
    rw [trim_of_coarse_roundtrip f e hr d h10 hround] at htrim
    exact Bool.noConfusion htrim

/-- Żmij is correct on regularly spaced positive binary64 values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid. -/
theorem correct (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let (d, k) := toDecimal f e
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  obtain ⟨hfine, hcoarse⟩ := ulp_scaled_bounds e hr.range
  exact exact_candidate_correct f e (decimalExponent e) hr.pos hfine hcoarse
    (exact_candidate f e hr)
