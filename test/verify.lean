-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import exact

/-! # Correctness of yy

`exact.lean` proves that an exact, Schubfach-like selection rule produces a
shortest, correctly rounded decimal whenever the decimal grid step is at most
one ULP and strictly greater than a tenth of one. This file proves that yy
implements that rule.

The whole argument is that each of yy's three packed Boolean decisions is an
exact arithmetic predicate. yy computes them from a truncated power of ten and
from words it has already dropped bits from, so a decision could in principle
differ from the exact one; the narrow regions where that could happen are
discharged by finite modular certificates. Once the three characterizations are
in hand, the rest is a short assembly into `ExactCandidate`. No claim is made
that yy's packed comparisons agree with the exact ones case by case—a packed
midpoint need not be an exact midpoint—only that the output is right.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`;
* `h`: the shift `exponentShift e`, aligning `f·2^e` with `10^k`.

## What the three decisions mean

Each of yy's flags is characterized once, as an exact integer comparison:

    round_d0_iff_gap :  roundD0 ↔ trimGap ≤ trimNum
    round_u0_iff_gap :  roundU0 ↔ trimScale ≤ trimGap + trimNum
    round_u1_iff_gap :  roundU1 ↔ trimMul < 2·oneGap

The first two are strict for odd `f` and the third non-strict for odd `sigHi`,
which is each tie rule written into its bound: the coarse candidates are ties in
the binary rounding interval, resolved by the parity of `f`, while the unit step
is a decimal tie, resolved by the parity of the digit being emitted.

`## yy's arithmetic model` is there to prove those three. It supplies the
quantities they are stated in—`trimGap`, `trimNum`, `trimScale`, `trimMul`,
`oneGap`—and keeps the rest below them: the packed words, the exact identities
behind them, the truncation error, bounds on that error, and the `ModWindows`
certificates closing the regions the bounds leave open.

The coarse pair carries a second equivalence, on the other side:

    round_d0_iff_roundtrips :  roundD0 ↔ sigTen round-trips
    round_u0_iff_roundtrips :  roundU0 ↔ sigTen + 10 round-trips

The two boundaries mean different things and stay separate. `*_iff_gap` says the
finite-precision implementation reaches the correct exact decision;
`*_iff_roundtrips` connects the integer scale that decision is made in to the
semantic specification. Consumers read one direction or the other:
`coarse_output_roundtrips` uses `→`, `trim_of_coarse_roundtrip` uses `←`.

## Dependencies

    yy_correct
      ← ulp_scaled_bounds
      ← yy_exact_candidate
          ← coarse_output_roundtrips
          ← fine_output_nearest
          ← trim_of_coarse_roundtrip

    coarse_output_roundtrips, trim_of_coarse_roundtrip
      ← round_d0_iff_roundtrips, round_u0_iff_roundtrips

    fine_output_nearest
      ← round_u1_iff_gap

`ulp_scaled_bounds` is the other thing `exact_candidate_correct` asks for: at
yy's exponent one ULP spans between one and ten grid steps, so the fine case has
a grid to be correctly rounded on.
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

/-! ## yy's arithmetic model

Everything from here to `## The coarse decisions` is machinery for the three
flag equivalences: the algorithm as yy computes it, the packed quantities its
comparisons are made of, the exact identities those quantities satisfy, bounds
on how far truncation can move them, and the certificates that close what the
bounds leave open. The subsections are stages of one proof, not interfaces.
`ulp_scaled_bounds`, at the end, is the exception: it is an obligation in its
own right and is proved here because it is the same arithmetic.
-/

/-! ### yy's conversion

The truncated power of ten, the words yy computes from it, and the shift that
aligns the two. `toDecimalCandidates` is the algorithm itself: the three packed
Booleans and the two candidates they choose between, which is what the whole
file is about. The alignment lemmas come last because `exponent_shift_align`
is stated against `power10Exponent`.
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
    normalization check and the whole trim layer stay in `Nat`. -/
theorem power10_significand_nat (k : ℤ) :
    power10Significand k = power10Num k / power10Den k := by
  rw [power10Significand, power10_exact_ratio]
  exact Nat.floor_div_eq_div _ _

/-- The fixed-point exponent does normalize `10^k`, over the range yy's decimal
    exponents reach. Beyond it the approximation eventually drifts from
    `⌊k·log₂10⌋ + 1`, so this is where the range is pinned down. In ratio form
    the check is two comparisons of naturals per exponent. -/
theorem power10_ratio_normalized :
    ∀ k ∈ Finset.Icc (-292 : ℤ) 324,
      2 ^ 127 * power10Den k ≤ power10Num k ∧
        power10Num k < 2 ^ 128 * power10Den k := by
  -- This and the two checks like it below enumerate up to 2046 exponents.
  -- `+kernel` keeps them out of the elaborator, whose recursion and
  -- exponentiation guards they would otherwise trip.
  decide +kernel

/-- Hence the significand is a normalized 128-bit number: its top bit is set,
    which is what makes `power10Exponent` an exponent for a 128-bit significand,
    and it still fits in 128 bits. -/
theorem power10_significand_bounds (k : ℤ) (hk : -292 ≤ k ∧ k ≤ 324) :
    2 ^ 127 ≤ power10Significand k ∧ power10Significand k < 2 ^ 128 := by
  obtain ⟨hlo, hhi⟩ :=
    power10_ratio_normalized k (by simpa [Finset.mem_Icc] using hk)
  rw [power10_significand_nat]
  exact ⟨(Nat.le_div_iff_mul_le (power10_den_pos k)).mpr hlo,
    (Nat.div_lt_iff_lt_mul (power10_den_pos k)).mpr hhi⟩

/-- Approximation of floor(e·log₁₀ 2) used as yy's decimal exponent. -/
def decimalExponent (e : ℤ) : ℤ :=
  e * 315_653 / 2 ^ 20

/-- Shift chosen to align the binary exponent with the power of ten. -/
def exponentShift (e : ℤ) : ℕ :=
  Int.toNat (e + (-decimalExponent e * 217_707) / 2 ^ 16)

/-- The 128-bit decimal significand ⌊f·2^(h+1)·⌊10^(-k)·2^128⌋ / 2^64⌋. -/
def scaledSignificand (f : ℕ) (e : ℤ) : ℕ :=
  let k := decimalExponent e
  let h := exponentShift e
  let p10 := power10Significand (-k)
  f * 2 ^ (h + 1) * p10 / 2 ^ 64

/-- High 64-bit word of the decimal significand. -/
def sigHi (f : ℕ) (e : ℤ) : ℕ := scaledSignificand f e / 2 ^ 64

/-- Low 64-bit word of the decimal significand. -/
def sigLo (f : ℕ) (e : ℤ) : ℕ := scaledSignificand f e % 2 ^ 64

/-- yy's `ten`: `sigHi` with its last decimal digit cleared, the trim-down
    candidate. -/
def sigTen (f : ℕ) (e : ℤ) : ℕ := sigHi f e - sigHi f e % 10

/-- The trim-down candidate is a multiple of ten. -/
theorem sig_ten_mod_ten (f : ℕ) (e : ℤ) : sigTen f e % 10 = 0 := by
  rw [sigTen]; omega

structure DecimalCandidates where
  k : ℤ
  decOne : ℕ
  roundU1 : Bool
  decTen : ℕ
  roundD0 : Bool
  roundU0 : Bool

def toDecimalCandidates (f : ℕ) (e : ℤ) : DecimalCandidates :=
  let k := decimalExponent e
  let h := exponentShift e

  let p10 := power10Significand (-k)
  let p10Hi := p10 / 2 ^ 64

  let sig := scaledSignificand f e
  let sigHi := sig / 2 ^ 64
  let sigLo := sig % 2 ^ 64

  let one := sigHi % 10
  let ten := sigHi - one
  let c := one * 2 ^ 60 + sigLo / 2 ^ 4
  let halfUlp := p10Hi / 2 ^ (4 - h)
  let t0 := 10 * 2 ^ 60
  let t1 := c + halfUlp

  let roundU1 : Bool :=
    if sigLo = 2 ^ 63 then
      sigHi % 2 = 1
    else
      2 ^ 63 < sigLo

  let roundD0 : Bool :=
    if halfUlp = c then
      f % 2 = 0
    else
      c < halfUlp

  let roundU0 : Bool :=
    if t1 + 1 = t0 then
      f % 2 = 0
    else if k = 0 ∧ t1 = t0 then
      f % 2 = 0
    else
      t0 ≤ t1

  {
    k := k
    roundU1 := roundU1
    decOne := sigHi + if roundU1 then 1 else 0
    decTen := ten + if roundU0 then 10 else 0
    roundD0 := roundD0
    roundU0 := roundU0
  }

/-- Converts a regularly spaced binary floating-point value f·2^e to a decimal
    significand and exponent using yy's full path. -/
def toDecimal (f : ℕ) (e : ℤ) : ℕ × ℤ :=
  let c := toDecimalCandidates f e
  (if c.roundD0 || c.roundU0 then c.decTen else c.decOne, c.k)

/-- The shift used by yy's regular path is less than 4. -/
theorem exponent_shift_lt_four (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    exponentShift e < 4 := by
  unfold exponentShift decimalExponent
  omega

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. The two
    fixed-point constants multiply to just over one, by a part in 2^17.4, and
    that is exactly enough for `omega`'s rational relaxation to still admit a
    shift of `-1`. Ruling it out is a Diophantine fact about the constants
    rather than a magnitude bound, so it is checked; all the arithmetic here is
    small. -/
theorem exponent_shift_nonneg :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971,
      0 ≤ e + (-decimalExponent e * 217_707) / 2 ^ 16 := by
  decide +kernel

/-- The shift undoes the power-of-ten exponent: `h + 1 - pe = e`. Both sides
    scale the same fixed-point quotient, so once the shift is known not to have
    been clamped this is arithmetic, whatever the decimal exponent is. -/
theorem exponent_shift_align (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    (exponentShift e : ℤ) + 1 - power10Exponent (-decimalExponent e) = e := by
  have hnonneg := exponent_shift_nonneg e (by simpa [Finset.mem_Icc] using he)
  unfold exponentShift power10Exponent
  omega

/-! ### The packed quantities

yy's `roundD0` and `roundU0` compare the packed value `c` (the last decimal
digit of the integral part, followed by the top 60 bits of `sigLo`) with
`halfUlp`. Both sides are truncated at the same window unit `U`. With

    h = exponentShift e,   p10 = trimSig e,
    N = 10·2^(128-h),     U = 2^(68-h),   W = 2·f·p10 % N

one has `c = W / U`, `halfUlp = p10 / U`, `10·2^60 = N / U`, and
`ten·2^(128-h) + W = 2·f·p10`. Thus the two tests use only the pair
`(W, p10)` measured in units of `U`, and the boundary analysis becomes exact
integer arithmetic rather than an error estimate.

This subsection supplies those quantities with the denominator cleared, the
facts checked about them per exponent, the two bounds the comparisons decide,
and the sizes the rest of the argument measures against. What each comparison
discards is defined at the end, and the subsection after this one states the
comparisons in these quantities exactly.
-/

/-- Numerator of the exact power of ten `10^(-k)·2^(128-pe)` for the decimal
    exponent associated with `e`. The trim layer works entirely with the three
    naturals `trimNum`, `trimDen` and `trimSig`. -/
def trimNum (e : ℤ) : ℕ := power10Num (-decimalExponent e)

/-- Denominator of that power of ten. -/
def trimDen (e : ℤ) : ℕ := power10Den (-decimalExponent e)

/-- Its 128-bit truncation, the `p10` of the comparisons. -/
def trimSig (e : ℤ) : ℕ := power10Significand (-decimalExponent e)

theorem trim_den_pos (e : ℤ) : 0 < trimDen e := power10_den_pos _

/-- The truncation is the floor of the fraction: `p10 = num / den`, so the whole
    trim layer is natural-number division. -/
theorem trim_sig_nat (e : ℤ) : trimSig e = trimNum e / trimDen e :=
  power10_significand_nat _

/-- The power-of-ten significand yy uses is normalized. Only the range matters:
    `-decimalExponent e` runs over exactly `[-292, 324]` as `e` runs over yy's
    exponents, which is the interval `power10_ratio_normalized` enumerated. -/
theorem trim_sig_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 127 ≤ trimSig e ∧ trimSig e < 2 ^ 128 :=
  power10_significand_bounds _ (by unfold decimalExponent; omega)

/-- Modulus of the packed comparison: the window wraps every 10·2^(128-h). -/
def trimModulus (e : ℤ) : ℕ := 10 * 2 ^ (128 - exponentShift e)

/-- One unit in the last place of the packed comparison. -/
def trimUnit (e : ℤ) : ℕ := 2 ^ (68 - exponentShift e)

/--
yy produces two candidates from the same product `2·f·p10`, differing only in
the step `m` between admissible values: `2^(128-h)` for `sigHi` and ten times
that for its multiple of ten. In both, the candidate is the quotient
`2·f·p10 / m` and `stepResidue` is the exact remainder above it, in units of
`2^(h-128)` of the scaled value.
-/
def stepResidue (m f : ℕ) (e : ℤ) : ℕ := 2 * f * trimSig e % m

/-- The remainder above the multiple-of-ten candidate:
    `ten·2^(128-h) + trimResidue = 2·f·p10`. -/
def trimResidue (f : ℕ) (e : ℤ) : ℕ := stepResidue (trimModulus e) f e

/-- `scaledSignificand` is the shifted product with the low 64 bits dropped. -/
theorem scaled_significand_eq (f : ℕ) (e : ℤ) :
    scaledSignificand f e =
      2 ^ exponentShift e * (2 * f * trimSig e) / 2 ^ 64 := by
  show f * 2 ^ (exponentShift e + 1) * trimSig e / 2 ^ 64 = _
  congr 1
  rw [pow_succ]
  ring

/-- `sigHi` is the top 64 bits of the shifted 192-bit product. -/
theorem sig_hi_eq (f : ℕ) (e : ℤ) :
    sigHi f e = 2 ^ exponentShift e * (2 * f * trimSig e) / 2 ^ 128 := by
  show scaledSignificand f e / 2 ^ 64 = _
  rw [scaled_significand_eq, Nat.div_div_eq_div_mul, ← pow_add]

/-- `sigLo` is bits 64–127 of the shifted 192-bit product. -/
theorem sig_lo_eq (f : ℕ) (e : ℤ) :
    sigLo f e
      = 2 ^ exponentShift e * (2 * f * trimSig e) % 2 ^ 128 / 2 ^ 64 := by
  show scaledSignificand f e % 2 ^ 64 = _
  rw [scaled_significand_eq, ← Nat.mod_mul_right_div_self, ← pow_add]

/-- A power of two splits into the shift and what is left of the window. -/
theorem pow_shift_split (e : ℤ) (n : ℕ) (hn : exponentShift e ≤ n) :
    (2 : ℕ) ^ n = 2 ^ exponentShift e * 2 ^ (n - exponentShift e) := by
  rw [← pow_add]
  congr 1
  omega

/-- Splitting a value at bit 128 and then discarding the low 68 bits is the same
    as discarding them directly; this is what packs the last digit into `c`. -/
theorem div_window (r : ℕ) :
    r / 2 ^ 128 * 2 ^ 60 + r % 2 ^ 128 / 2 ^ 68 = r / 2 ^ 68 := by
  conv_rhs => rw [← Nat.div_add_mod r (2 ^ 128)]
  rw [show (2 : ℕ) ^ 128 = 2 ^ 68 * 2 ^ 60 from by norm_num, mul_assoc,
    Nat.mul_add_div (by positivity)]
  ring

/-- `halfUlp` is the power-of-ten significand truncated to the window unit. -/
theorem trim_half_ulp_eq (e : ℤ) (hsh : exponentShift e < 4) :
    trimSig e / 2 ^ 64 / 2 ^ (4 - exponentShift e)
      = trimSig e / trimUnit e := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, trimUnit,
    show 64 + (4 - exponentShift e) = 68 - exponentShift e from by omega]

/-- `c` is the window residue truncated to the window unit. -/
theorem trim_c_eq (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    sigHi f e % 10 * 2 ^ 60 + sigLo f e / 2 ^ 4
      = trimResidue f e / trimUnit e := by
  set h := exponentShift e with hh
  set z := 2 * f * trimSig e
  set r := 2 ^ h * z % (2 ^ 128 * 10) with hr
  have hpos : 0 < (2 : ℕ) ^ h := by positivity
  have h68 : (2 : ℕ) ^ 68 = 2 ^ h * 2 ^ (68 - h) := by
    rw [← pow_add]
    congr 1
    omega
  have hmodulus : (2 : ℕ) ^ 128 * 10 = 2 ^ h * trimModulus e := by
    rw [trimModulus, ← hh, pow_shift_split e 128 (by omega)]
    ring
  have hresidue : r = 2 ^ h * trimResidue f e := by
    rw [hr, hmodulus, Nat.mul_mod_mul_left]
    rfl
  have hscaled : trimResidue f e / trimUnit e = r / 2 ^ 68 := by
    rw [hresidue, h68, trimUnit, ← hh, Nat.mul_div_mul_left _ _ hpos]
  have hhi : sigHi f e % 10 = r / 2 ^ 128 := by
    rw [sig_hi_eq, hr, Nat.mod_mul_right_div_self]
  have hlo : sigLo f e / 2 ^ 4 = r % 2 ^ 128 / 2 ^ 68 := by
    have hmod : 2 ^ h * z % 2 ^ 128 = r % 2 ^ 128 := by
      rw [hr, Nat.mod_mod_of_dvd _ ⟨10, rfl⟩]
    rw [sig_lo_eq, hmod, Nat.div_div_eq_div_mul, ← pow_add]
  rw [hhi, hlo, hscaled, div_window]

/-- `sigHi` is the quotient at the unit step. The multiple-of-ten candidate uses
    the coarse step, which is ten unit steps. -/
theorem sig_hi_quotient (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    sigHi f e = 2 * f * trimSig e / 2 ^ (128 - exponentShift e) := by
  rw [sig_hi_eq, pow_shift_split e 128 (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

theorem sig_hi_ten_quotient (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    sigTen f e = 10 * (2 * f * trimSig e / trimModulus e) := by
  rw [sigTen]
  -- Dividing the unit-step quotient by ten is dividing by the coarse step.
  have hdiv : sigHi f e / 10 = 2 * f * trimSig e / trimModulus e := by
    rw [sig_hi_quotient f e hsh, Nat.div_div_eq_div_mul,
      show 2 ^ (128 - exponentShift e) * 10 = trimModulus e from by
        rw [trimModulus]; ring]
  have hmod := Nat.div_add_mod (sigHi f e) 10
  rw [← hdiv]
  omega

/-! ### The bounds the comparisons decide

The two multiple-of-ten candidates are within half a ULP exactly when

    trim down:  W + (2f-1)·p10Exact ≤ 2·f·p10,
    trim up:    N + 2·f·p10 ≤ W + (2f+1)·p10Exact,

writing `p10Exact` for the exact power of ten `10^(-k)·2^(128-pe)`, which
satisfies `p10 ≤ p10Exact < p10 + 1`. Substituting the window identity
`ten·2^(128-h) + W = 2·f·p10` and `p10Exact·s = 2^(128-h)`, and writing
`ten = 10·M`, both read as comparisons of the exact binary rounding boundary
with the decimal grid the trim targets:

    trim down:  2^(e-1)·(2f-1) ≤ M·10^(k+1),
    trim up:    (M+1)·10^(k+1) ≤ 2^(e-1)·(2f+1).

So the quantity to control is `Λ = M·10^(k+1) - 2^(e-1)·(2f∓1)`. Exact ties are
the case `Λ = 0`: since `2f∓1` is odd it carries no twos, so the boundary can
only land on `10^(k+1)·ℤ` when `e - 1 ≥ k + 1` supplies them, and the remaining
power of two is a unit modulo `5^(k+1)`, leaving the single residue class
`2f∓1 ≡ 0 (mod 5^(k+1))`—an arithmetic progression in `f`, not a magnitude
condition. With `2f∓1 < 2^54` this needs `5^(k+1) < 2^54`, so ties exist only
for `k ≤ 22`; there the two bounds hold with equality, which is exactly why the
parity test turns them into `≤` for even `f` and `<` for odd `f`. What must be
ruled out is a near miss, `Λ ≠ 0` of the wrong sign.

A magnitude bound cannot do that on its own. For `k ≥ 0` and `e ≥ k + 2`, both
terms of `Λ` are divisible by `2^(k+1)`, so the scaled defect is a multiple of
`2^(129-h)/5^k` while `trim_low_bits` only bounds it by `2^69`; that forces
`Λ = 0` only while `5^k ≤ 2^61`, i.e. `k ≤ 26`. Beyond that the quantum is
smaller than the uncertainty and the separation becomes genuinely arithmetic,
so the development below clears denominators instead. Writing `num/den` for the
exact power of ten and `τ = num % den`, the two bounds become

    trim down:  trimGap ≤ num,
    trim up:    trimScale ≤ trimGap + num,

and `trim_gap_mod` identifies `trimGap` with `2·num·f mod trimScale` as long as
it has not wrapped, which the packed comparisons guarantee.

Clearing the denominator serves the development above the certificates too. The
bounds are then linear in products `omega` treats as atoms, so each follows from
the packed comparisons by integer arithmetic alone. Dividing `den` back out to
state them over `ℚ` trades that for casts and field lemmas, and for restating as
hypotheses the facts about `%` and `/` that `omega` already knows.
-/

/-- The exact distance from a candidate to the scaled value, with the
    denominator of the exact power of ten cleared: the residue contributes
    `den·W` and the truncation `p10Exact - p10 = τ/den` costs `2·f·τ`. -/
def stepGap (m f : ℕ) (e : ℤ) : ℕ :=
  trimDen e * stepResidue m f e + 2 * f * (trimNum e % trimDen e)

/-- The distance to the multiple-of-ten candidate, and the window modulus with
    the same denominator cleared. -/
def trimGap (f : ℕ) (e : ℤ) : ℕ := stepGap (trimModulus e) f e

/-- The power-of-ten truncation error carried by the gap, `2·f·τ`. -/
def trimErr (f : ℕ) (e : ℤ) : ℕ := 2 * f * (trimNum e % trimDen e)

/-- The gap is `den` times the residue plus the truncation error. -/
theorem trim_gap_eq (f : ℕ) (e : ℤ) :
    trimGap f e = trimDen e * trimResidue f e + trimErr f e := rfl

def trimScale (e : ℤ) : ℕ := trimModulus e * trimDen e

/-- One window unit with the denominator cleared: the resolution of the packed
    comparison and the scale of the narrow windows refuted below. -/
def trimEdge (e : ℤ) : ℕ := trimUnit e * trimDen e

/-- Everything about the truncated power of ten that has to be checked per
    exponent, as one predicate so the kernel sweeps the range once. Narrowness
    is `2·p10 + 2 ≤ N`, which keeps the gap from wrapping the window modulus.
    The other two are `2^54·(p10Exact - p10) ≤ p10 % U` and its complement
    `2^54·(p10Exact - p10) ≤ U - p10 % U`, with the denominator cleared: the
    truncation error fits in the bits the packed comparison discards, measured
    from either end of the window unit. Truncation is expressed as natural
    division so the check reduces directly in the kernel. -/
def trimChecksHold (e : ℤ) : Bool :=
  let num := trimNum e
  let den := trimDen e
  let low := num / den % trimUnit e
  decide (2 * (num / den) + 2 ≤ trimModulus e
    ∧ 2 ^ 54 * (num % den) ≤ low * den
    ∧ 2 ^ 54 * (num % den) + low * den ≤ trimUnit e * den)

theorem trim_checks_all :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, trimChecksHold e = true := by
  decide +kernel

/-- The three checked facts for one exponent, with the truncation read back as
    `trimSig`. Which bits of the power of ten survive truncation is not a
    magnitude property, which is why these are checked rather than derived. -/
theorem trim_checks (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 * trimSig e + 2 ≤ trimModulus e
      ∧ 2 ^ 54 * (trimNum e % trimDen e) ≤ trimSig e % trimUnit e * trimDen e
      ∧ 2 ^ 54 * (trimNum e % trimDen e) + trimSig e % trimUnit e * trimDen e
        ≤ trimUnit e * trimDen e := by
  have hcert := trim_checks_all e (by simpa [Finset.mem_Icc] using he)
  simp only [trimChecksHold, decide_eq_true_eq] at hcert
  rw [trim_sig_nat]
  exact hcert

/-- The discarded low bits `p10 % U` dominate the power-of-ten truncation error
    `p10Exact - p10 = τ/den`: the margin used when a packed comparison is strict
    on the low side. -/
theorem trim_low_bits (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 54 * (trimNum e % trimDen e)
      ≤ trimSig e % trimUnit e * trimDen e := (trim_checks e he).2.1

/-- The complementary distance to the next window unit dominates the same
    truncation error: the margin used when a packed comparison falls short of
    its boundary, which is what the completeness directions need. -/
theorem trim_high_bits (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 54 * (trimNum e % trimDen e) + trimSig e % trimUnit e * trimDen e
      ≤ trimUnit e * trimDen e := (trim_checks e he).2.2

/-! The comparisons that decide those bounds are themselves packed: `roundD0`
compares `W / U` with `p10 / U`, while `roundU0` compares their sum with
`N / U`. They see the exact quantities only up to one window unit `U`;
`round_d0_iff_gap` and `round_u0_iff_gap` recover the exact bound each decides.

Because truncation is one-sided, the soundness directions are asymmetric: the
plain `roundU0` test is safe whenever it fires, while the one-LSB-offset test
`t1 + 1 = t0` and the trim-down tests may accept one unit early.

Completeness reads the same comparisons in the opposite direction. A test that
does not fire bounds the exact gap from the other side, again with at most one
unit of uncertainty. There the relevant margin is the distance from the
discarded low bits of `p10` to the next window boundary, rather than the low
bits themselves; this is why `trimChecksHold` certifies both sides of the unit.
-/

/-- `p10Exact ≥ 2^127`, with the denominator cleared. -/
theorem trim_num_lower (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 127 * trimDen e ≤ trimNum e := by
  have hdiv : 2 ^ 127 ≤ trimNum e / trimDen e := by
    rw [← trim_sig_nat]; exact (trim_sig_bounds e he).1
  exact (Nat.le_div_iff_mul_le (trim_den_pos e)).mp hdiv

/-- The resolution of the packed comparison is negligible against the power of
    ten: `U ≤ 2^68` while `p10Exact ≥ 2^127`. -/
theorem trim_two_edge_lt_num (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 * trimEdge e < trimNum e := by
  have hu : trimUnit e ≤ 2 ^ 68 := by
    rw [trimUnit]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hedge : trimEdge e ≤ 2 ^ 68 * trimDen e := by
    rw [trimEdge]; exact Nat.mul_le_mul_right _ hu
  have hnum := trim_num_lower e he
  have hden := trim_den_pos e
  omega

/-! With the denominator cleared the power of ten splits as `den·p10 + τ = num`,
and every candidate satisfies one identity: scaled back up by `m·den`, the
quotient at step `m` plus the gap is `2·f·num`. `step_quotient_add_gap` states
it for a generic step, and the unit and coarse candidates both instantiate it.

The rest are the sizes that identity is used with. The truncation error is
below `2^54·den`, since `τ < den` and `2·f < 2^54`; one ULP is narrower than
one coarse step, which is the narrowness certificate cleared; and the gap
overshoots the coarse step by less than `num`. At `k = 0` the power of ten is
exact and `τ` vanishes, the one case the arguments below have to separate out.
-/

theorem trim_unit_pos (e : ℤ) : 0 < trimUnit e := by
  rw [trimUnit]; positivity

/-- `den·p10 + τ = num`: the truncated power of ten and the bits it dropped. -/
theorem trim_num_split (e : ℤ) :
    trimDen e * trimSig e + trimNum e % trimDen e = trimNum e := by
  rw [trim_sig_nat]; exact Nat.div_add_mod _ _

/-- One ULP of the value is narrower than one step of the coarse decimal grid:
    `2·num < scale`. This depends on the low bits of the truncated power of ten,
    not just its magnitude, so it is checked separately for each exponent. -/
theorem trim_two_num_lt_scale (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 * trimNum e < trimScale e := by
  have hstep : trimDen e * (2 * trimSig e + 2) ≤ trimDen e * trimModulus e :=
    Nat.mul_le_mul_left _ (trim_checks e he).1
  have hexp : trimDen e * (2 * trimSig e + 2)
      = 2 * (trimDen e * trimSig e) + 2 * trimDen e := by ring
  have hsplit := trim_num_split e
  have hscale : trimDen e * trimModulus e = trimScale e := by
    rw [trimScale]; ring
  have hmod : trimNum e % trimDen e < trimDen e := Nat.mod_lt _ (trim_den_pos e)
  omega

/-- Whatever the step, the candidate scaled back up plus the gap is the scaled
    value `2·f·num`: `Nat.div_add_mod` recovers the product from the quotient
    and `trim_num_split` the power of ten from its truncation. -/
theorem step_quotient_add_gap (m f : ℕ) (e : ℤ) :
    2 * f * trimSig e / m * (m * trimDen e) + stepGap m f e
      = 2 * f * trimNum e := by
  rw [stepGap, stepResidue]
  calc 2 * f * trimSig e / m * (m * trimDen e)
        + (trimDen e * (2 * f * trimSig e % m)
          + 2 * f * (trimNum e % trimDen e))
      = trimDen e * (m * (2 * f * trimSig e / m) + 2 * f * trimSig e % m)
          + 2 * f * (trimNum e % trimDen e) := by ring
    _ = 2 * f * (trimDen e * trimSig e + trimNum e % trimDen e) := by
        rw [Nat.div_add_mod]; ring
    _ = 2 * f * trimNum e := by rw [trim_num_split]

/-- The truncation error of the power of ten, `2·f·τ` with `τ < den`
    and `2·f < 2^54`. -/
theorem trim_trunc_lt (f : ℕ) (e : ℤ) (hr : Regular f e) :
    2 * f * (trimNum e % trimDen e) < 2 ^ 54 * trimDen e :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (by have := hr.sig_lt; omega))
    (mul_lt_mul_of_pos_left (Nat.mod_lt _ (trim_den_pos e)) (by positivity))

/-- At `k = 0` the power-of-ten significand is exactly `2^127`, so it has no
    low bits for the truncation to drop. -/
theorem trim_power_of_k_zero (e : ℤ) (hk : decimalExponent e = 0) :
    trimNum e = 2 ^ 127 * trimDen e ∧ trimSig e = 2 ^ 127 := by
  have heq : trimNum e = 2 ^ 127 * trimDen e := by
    rw [trimNum, trimDen, hk]
    decide
  exact ⟨heq, by rw [trim_sig_nat, heq, Nat.mul_div_cancel _ (trim_den_pos e)]⟩

/-- The gap can overshoot the coarse step, but by less than `num`: the residue
    stays below the step and `num ≥ 2^127·den` absorbs the truncation error.
    This is the side of the trim-up bound that needs no flag hypothesis. -/
theorem trim_gap_lt_scale_add (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimGap f e < trimScale e + trimNum e := by
  have hres : trimDen e * trimResidue f e < trimScale e := by
    rw [trimResidue, stepResidue, trimScale, Nat.mul_comm (trimModulus e)]
    exact mul_lt_mul_of_pos_left
      (Nat.mod_lt _ (by rw [trimModulus]; positivity)) (trim_den_pos e)
  have hlow : trimErr f e < 2 ^ 54 * trimDen e := trim_trunc_lt f e hr
  have htrunc : 2 ^ 54 * trimDen e ≤ trimNum e :=
    le_trans
      (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
      (trim_num_lower e hr.range)
  rw [trim_gap_eq]
  omega

/-- What the trim-down comparison throws away, with the denominator cleared: the
    bits of `p10` below the window unit, plus the remainder `τ` that truncating
    the power of ten dropped in the first place. -/
def trimDrop (e : ℤ) : ℕ :=
  trimNum e % trimDen e + trimSig e % trimUnit e * trimDen e

/-- What the trim-up comparison throws away: the same, plus the low bits of the
    residue, which that comparison truncates as well. -/
def trimDropU (f : ℕ) (e : ℤ) : ℕ :=
  trimDrop e + trimResidue f e % trimUnit e * trimDen e

/-- Splitting two values at the window unit. -/
private theorem sum_split (den u w p : ℕ) :
    den * w + den * p
      = den * (w % u) + den * (p % u) + u * den * (w / u + p / u) := by
  calc den * w + den * p
      = den * (u * (w / u) + w % u) + den * (u * (p / u) + p % u) := by
        rw [Nat.div_add_mod, Nat.div_add_mod]
    _ = den * (w % u) + den * (p % u) + u * den * (w / u + p / u) := by ring

/-! ### The comparisons and their error

Each packed comparison is now an exact identity in the quantities above, off
the boundary it decides by exactly the bits it discarded: `packed_iff` for the
trim-down test, `trim_packed_sum` for the trim-up one. The three bounds after
them say how far those bits can move a decision. The truncation error never
exceeds what the trim-down comparison discards; that in turn is less than the
error plus one window edge; and the trim-up comparison, which truncates the
residue as well, discards less than two edges. What survives is a narrow window
at either boundary.
-/

/-- The packed boundary `n` window units above `p10`, scaled: it differs from
    the exact boundary `num` by exactly the discarded bits. -/
theorem trim_packed_boundary (e : ℤ) (n : ℕ) :
    trimDen e * ((trimSig e / trimUnit e + n) * trimUnit e) + trimDrop e
      = trimNum e + n * trimEdge e := by
  have hexp : trimDen e * ((trimSig e / trimUnit e + n) * trimUnit e)
      + (trimNum e % trimDen e + trimSig e % trimUnit e * trimDen e)
      = trimDen e * (trimUnit e * (trimSig e / trimUnit e)
          + trimSig e % trimUnit e) + trimNum e % trimDen e
        + n * (trimUnit e * trimDen e) := by ring
  rw [trimDrop, trimEdge, hexp, Nat.div_add_mod, trim_num_split]

/-- The trim-down comparison in exact quantities. `n = 0` is yy's strict test
    and `n = 1` its non-strict one, one window edge further out. -/
theorem packed_iff (f : ℕ) (e : ℤ) (n : ℕ) :
    trimResidue f e / trimUnit e < trimSig e / trimUnit e + n
      ↔ trimGap f e + trimDrop e
        < trimNum e + trimErr f e + n * trimEdge e := by
  have hb := trim_packed_boundary e n
  have hg := trim_gap_eq f e
  rw [Nat.div_lt_iff_lt_mul (trim_unit_pos e),
    show trimResidue f e < (trimSig e / trimUnit e + n) * trimUnit e
      ↔ trimDen e * trimResidue f e
        < trimDen e * ((trimSig e / trimUnit e + n) * trimUnit e) from
      (Nat.mul_lt_mul_left (trim_den_pos e)).symm]
  omega

/-- The trim-up comparison in exact quantities: the packed sum counts window
    edges below `gap + num`, and what it discards is `err + dropU`. All three of
    yy's trim-up tests are comparisons of that count with `scale / edge`. -/
theorem trim_packed_sum (f : ℕ) (e : ℤ) :
    trimGap f e + trimNum e
      = trimErr f e + trimDropU f e
        + trimEdge e
          * (trimResidue f e / trimUnit e + trimSig e / trimUnit e) := by
  have hsplit :=
    sum_split (trimDen e) (trimUnit e) (trimResidue f e) (trimSig e)
  have hnum := trim_num_split e
  have hgap := trim_gap_eq f e
  have hw : trimDen e * (trimResidue f e % trimUnit e)
      = trimResidue f e % trimUnit e * trimDen e := by ring
  have hp : trimDen e * (trimSig e % trimUnit e)
      = trimSig e % trimUnit e * trimDen e := by ring
  rw [trimDropU, trimDrop, trimEdge]
  omega

/-- The coarse step is `10·2^60` window edges, the constant yy compares to: the
    modulus is that many window units. -/
theorem trim_scale_eq_edge (e : ℤ) (hsh : exponentShift e < 4) :
    trimScale e = trimEdge e * (10 * 2 ^ 60) := by
  rw [trimScale, trimEdge, trimModulus, trimUnit,
    show 128 - exponentShift e = (68 - exponentShift e) + 60 from by omega,
    pow_add]
  ring

/-- The truncation error never exceeds the bits the trim-down comparison
    discards: that is what `trim_low_bits` certifies, per exponent. -/
theorem trim_err_le_drop (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimErr f e ≤ trimDrop e := by
  have hbig : trimErr f e ≤ 2 ^ 54 * (trimNum e % trimDen e) :=
    Nat.mul_le_mul_right _ (by have := hr.sig_lt; omega)
  have hlow := trim_low_bits e hr.range
  rw [trimDrop]
  omega

/-- One window unit above the truncation error is more than the trim-down
    comparison discards: `τ < den` and the low bits of `p10` are below `U`. -/
theorem trim_drop_lt_err_add_edge (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimDrop e < trimErr f e + trimEdge e := by
  have hlow : trimSig e % trimUnit e * trimDen e < trimEdge e := by
    rw [trimEdge]
    exact mul_lt_mul_of_pos_right (Nat.mod_lt _ (trim_unit_pos e))
      (trim_den_pos e)
  have hτ : trimNum e % trimDen e ≤ trimErr f e :=
    Nat.le_mul_of_pos_left _ (by have := hr.pos; omega)
  rw [trimDrop]
  omega

/-- The trim-up comparison discards less than two window edges. This is where
    `trim_high_bits` is needed: the truncation error has to fit beside the
    discarded low bits of `p10` within one edge, leaving the second edge for the
    low bits of the residue. -/
theorem trim_err_dropU_lt (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimErr f e + trimDropU f e < 2 * trimEdge e := by
  have hbig : trimErr f e ≤ 2 ^ 54 * (trimNum e % trimDen e) :=
    Nat.mul_le_mul_right _ (by have := hr.sig_lt; omega)
  have hhigh := trim_high_bits e hr.range
  have hτ : trimNum e % trimDen e < trimDen e := Nat.mod_lt _ (trim_den_pos e)
  have hres : trimResidue f e % trimUnit e * trimDen e + trimDen e
      ≤ trimUnit e * trimDen e :=
    calc trimResidue f e % trimUnit e * trimDen e + trimDen e
        = (trimResidue f e % trimUnit e + 1) * trimDen e := by ring
      _ ≤ trimUnit e * trimDen e :=
        Nat.mul_le_mul_right _ (Nat.mod_lt _ (trim_unit_pos e))
  rw [trimDropU, trimDrop, trimEdge]
  omega

/-! ### Refuting the exceptional trim windows

Everything above is analytic. What is left is a band of width one window edge on
either side of each boundary, minus the boundary itself; the certificates say
those bands are empty. The two boundaries share one modular problem, since both
ask where `2·num·f mod scale` can land.

Each bound is needed in both directions, so each of the two boundaries
contributes a window on either side of it; the boundary value itself lies in
none of them, which is what leaves the exact ties above their room. Soundness
and completeness for both boundaries therefore reduce to one modular question
per exponent, of the kind `ModWindows` answers. Writing `num/den` for the exact
power of ten, the progression is `g = 2·num` modulo `modulus = N·den`, the
residue is the gap, and any violation forces it into a window of width below
`den·U`, a relative width of `U/N ≈ 2^(-63.3)`. This is where verify.py counts
solutions with `floor_sum`; here a refutation certificate reaches the same
conclusion with one small check per window.

A Nadezhin-style separation proof, as used in Schubfach, was considered but
still requires a finite Diophantine check over the binary64 significand range.
The direct modular-window formulation below matches yy more closely and is
substantially simpler.
-/

/-- Scaling the window residue by `den` and adding back the truncation error
    `2·f·τ` preserves the residue modulo `n·den`, provided the sum has not
    wrapped. -/
theorem trim_mod_shift (p den τ n f : ℕ)
    (hlt : den * (2 * f * p % n) + 2 * f * τ < n * den) :
    2 * (p * den + τ) * f % (n * den)
      = den * (2 * f * p % n) + 2 * f * τ := by
  have hsplit := Nat.div_add_mod (2 * f * p) n
  have hkey : 2 * (p * den + τ) * f
      = n * den * (2 * f * p / n)
        + (den * (2 * f * p % n) + 2 * f * τ) := by
    calc 2 * (p * den + τ) * f = den * (2 * f * p) + 2 * f * τ := by ring
      _ = den * (n * (2 * f * p / n) + 2 * f * p % n) + 2 * f * τ := by
          rw [hsplit]
      _ = n * den * (2 * f * p / n)
            + (den * (2 * f * p % n) + 2 * f * τ) := by ring
  rw [hkey, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem trim_gap_mod (f : ℕ) (e : ℤ) (hlt : trimGap f e < trimScale e) :
    2 * trimNum e * f % trimScale e = trimGap f e := by
  rw [trimGap, stepGap, stepResidue, trim_sig_nat, trimScale] at hlt ⊢
  rw [show 2 * trimNum e * f
      = 2 * (trimNum e / trimDen e * trimDen e + trimNum e % trimDen e) * f
      from by rw [Nat.div_add_mod']]
  exact trim_mod_shift _ _ _ _ _ hlt

/-- The gaps the error bounds cannot decide: within one window edge of `num` or
    of `scale - num`, the two boundaries themselves excluded, plus the exact tie
    `scale - num` wherever the power of ten is exact and `k` is not zero, which
    no significand can reach either. -/
private def expWindows (e : ℤ) : ModWindows where
  g := 2 * trimNum e
  modulus := trimScale e
  f0 := 1
  f1 := 2 ^ 53 - 1
  windows :=
    let num : ℤ := trimNum e
    let edge : ℤ := trimEdge e
    let scale : ℤ := trimScale e
    [(num - edge, num - 1), (num + 1, num + edge),
      (scale - num - edge, scale - num - 1),
      (scale - num + 1, scale - num + edge - 1)]
      ++ if trimNum e % trimDen e = 0 ∧ decimalExponent e ≠ 0 then
        [(scale - num, scale - num)]
      else []

/-- Close `∃ q, (expWindows e).refutedBy q = true` for a literal exponent. -/
elab "exp_cert" : tactic => modCertTactic fun e => (expWindows e).search

private theorem exp_windows_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (expWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> exp_cert

/-- A gap landing in a refuted window is impossible: the gap is the residue of
    `2·num·f` modulo the window modulus, as long as it has not wrapped. -/
private theorem no_window_hit {lo hi q : ℤ} (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcert : (expWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (expWindows e).windows)
    (hwrap : trimGap f e < trimScale e)
    (hlo : lo ≤ (trimGap f e : ℤ)) (hhi : (trimGap f e : ℤ) ≤ hi) :
    False := by
  obtain ⟨⟨hf_pos, hf_hi, -⟩, -⟩ := hr
  refine (expWindows e).not_hit f ?_ hcert hmem ?_ ?_
    (trim_gap_mod f e hwrap).symm hlo hhi <;> simp only [expWindows]
  · rw [trimScale, trimModulus]
    exact Nat.mul_pos (by positivity) (trim_den_pos e)
  · omega
  · omega

/-- Either the gap sits exactly on a boundary, a genuine exact tie, or it is
    outside the windows either side of it, where the packed comparison cannot be
    wrong. Both boundaries take this form, and `b` and `hi` say which windows
    are meant: `hi` is the last residue the upper one covers, a full edge above
    the trim-down boundary and one short of that above the trim-up one.
    Refuting the one residue fewer is what leaves the trim-up conclusion
    non-strict, which is the form `round_u0_iff_gap` needs for even `f`. -/
private theorem gap_tie_or_far {b hi : ℤ} (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcap : hi < (trimScale e : ℤ))
    (hbelow : (b - trimEdge e, b - 1) ∈ (expWindows e).windows)
    (habove : (b + 1, hi) ∈ (expWindows e).windows) :
    (trimGap f e : ℤ) = b ∨ hi < (trimGap f e : ℤ)
      ∨ (trimGap f e : ℤ) + trimEdge e < b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hhi, hlo⟩ := hcon
  obtain ⟨q, hcert⟩ := exp_windows_refuted e hr.range
  have hwrap : trimGap f e < trimScale e := by omega
  rcases lt_or_ge (trimGap f e : ℤ) b with h | h
  · exact no_window_hit f e hr hcert hbelow hwrap (by omega) (by omega)
  · exact no_window_hit f e hr hcert habove hwrap (by omega) (by omega)

/-- The trim-down dichotomy, about the boundary `num`. -/
theorem d0_gap_tie_or_far (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimGap f e = trimNum e
      ∨ trimNum e + trimEdge e < trimGap f e
      ∨ trimGap f e + trimEdge e < trimNum e := by
  have hedge := trim_two_edge_lt_num e hr.range
  have hnarrow := trim_two_num_lt_scale e hr.range
  have := gap_tie_or_far (b := (trimNum e : ℤ))
    (hi := (trimNum e : ℤ) + trimEdge e) f e hr (by omega)
    (by simp [expWindows]) (by simp [expWindows])
  omega

/-- The trim-up dichotomy, the same statement about the boundary `scale - num`,
    which the packed comparison reads as `gap + num` against `scale`. -/
theorem u0_sum_tie_or_far (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimGap f e + trimNum e = trimScale e
      ∨ trimScale e + trimEdge e ≤ trimGap f e + trimNum e
      ∨ trimGap f e + trimNum e + trimEdge e < trimScale e := by
  have hedge := trim_two_edge_lt_num e hr.range
  have hnarrow := trim_two_num_lt_scale e hr.range
  have := gap_tie_or_far (b := (trimScale e : ℤ) - trimNum e)
    (hi := (trimScale e : ℤ) - trimNum e + trimEdge e - 1) f e hr (by omega)
    (by simp [expWindows]) (by simp [expWindows])
  omega

/-- An exact tie in the trim-up comparison needs `k = 0` when the power of ten
    is exact: that is the residue the fifth window refutes elsewhere. -/
theorem u0_exact_tie_k_zero (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hτ : trimNum e % trimDen e = 0)
    (htie : trimGap f e + trimNum e = trimScale e) :
    decimalExponent e = 0 := by
  by_contra hk
  obtain ⟨q, hcert⟩ := exp_windows_refuted e hr.range
  have hnum : 0 < trimNum e :=
    lt_of_lt_of_le (Nat.mul_pos (by positivity) (trim_den_pos e))
      (trim_num_lower e hr.range)
  -- The fifth window is present exactly under these two hypotheses.
  have hmem : ((trimScale e : ℤ) - trimNum e, (trimScale e : ℤ) - trimNum e)
      ∈ (expWindows e).windows := by
    refine List.mem_append_right _ ?_
    rw [ite_eq_left ⟨hτ, hk⟩]
    exact List.mem_singleton_self _
  exact no_window_hit f e hr hcert hmem (by omega) (by omega) (by omega)

/-- At `k = 0` the power of ten is exactly `2^127`, a whole number of window
    units, so the trim-up comparison discards nothing and its ties are exact. -/
theorem u0_err_dropU_k_zero (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hk : decimalExponent e = 0) :
    trimErr f e + trimDropU f e = 0 := by
  have hsh := exponent_shift_lt_four e hr.range
  obtain ⟨hnum, hsig⟩ := trim_power_of_k_zero e hk
  have hunit : trimUnit e ∣ trimSig e := by
    rw [hsig, trimUnit]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨cp, hcp⟩ := hunit
  obtain ⟨cw, hcw⟩ : trimUnit e ∣ trimResidue f e := by
    refine (Nat.dvd_mod_iff ?_).mpr (Dvd.dvd.mul_left ⟨cp, hcp⟩ _)
    rw [trimModulus, trimUnit]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) 10
  have hτ : trimNum e % trimDen e = 0 := by rw [hnum, Nat.mul_mod_left]
  rw [trimErr, trimDropU, trimDrop, hτ, hcp, hcw]
  simp

/-- The trim-up comparison sees an exact tie only where the power of ten is
    exact, and that needs `k = 0`. -/
theorem u0_tie_k_zero (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hzero : trimErr f e + trimDropU f e = 0)
    (htie : trimGap f e + trimNum e = trimScale e) :
    decimalExponent e = 0 := by
  have herr : 2 * f * (trimNum e % trimDen e) = 0 := by
    rw [trimErr] at hzero; omega
  rcases Nat.mul_eq_zero.mp herr with h | h
  · have := hr.pos; omega
  · exact u0_exact_tie_k_zero f e hr h htie

/-! ### Exact scaling

Everything above is integer arithmetic and everything below is a claim about
the exact value; `scaled_cmp_of_int_eq` is the one crossing, and it asks for
two things. `trim_value_scaled` says that the scale `trimMul` sends the scaled
value to the integer `2·f·num`, so each candidate sits a signed integer
distance from it: `-trimGap` for the trim-down candidate, `trimScale - trimGap`
for the trim-up one, and `-oneGap` for `sigHi`. The power of ten enters only
here, through `trim_mul_eq`, which expresses `trimMul` as `trimNum` times the
inverse scale `s = 2^(1-e)·10^k`. The other is what a threshold is worth in
that scale: half a ULP is `trimNum`, and half a grid step is `trimMul` over two
copies of it. Every candidate bound is then an interval condition on that
integer distance, and the consumers below never leave `ℤ`.
-/

/-- The unit step, cleared. The coarse step is ten of them. -/
def trimMul (e : ℤ) : ℕ := 2 ^ (128 - exponentShift e) * trimDen e

/-- The candidate scale factor is positive. -/
theorem trim_mul_pos (e : ℤ) : 0 < trimMul e := by
  rw [trimMul]
  exact Nat.mul_pos (by positivity) (trim_den_pos e)

theorem trim_scale_eq_ten_mul (e : ℤ) : trimScale e = 10 * trimMul e := by
  simp only [trimScale, trimMul, trimModulus]
  ring

/-- Twice the bound on the power-of-ten truncation error fits inside one grid
    step: `trimMul ≥ 2^125·den`, while the doubled bound is `2^55·den`. -/
theorem trim_two_trunc_le_mul (e : ℤ) (hsh : exponentShift e < 4) :
    2 ^ 55 * trimDen e ≤ trimMul e := by
  rw [trimMul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Half a grid step, cleared: half a unit step times `den`. -/
theorem trim_mul_eq_two_half (e : ℤ) (hsh : exponentShift e < 4) :
    trimMul e = 2 * (trimDen e * 2 ^ (127 - exponentShift e)) := by
  rw [trimMul, show (2 : ℕ) ^ (128 - exponentShift e)
      = 2 * 2 ^ (127 - exponentShift e) from by
    rw [← pow_succ']; congr 1; omega]
  ring

/-- `trimMul` clears the denominator in `power10_exact_ratio`, leaving `trimNum`
    times the binary-decimal scaling factor. -/
theorem trim_mul_eq (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    (trimMul e : ℚ)
      = (trimNum e : ℚ) * (2 ^ (1 - e) * 10 ^ decimalExponent e) := by
  set k := decimalExponent e
  set pe := power10Exponent (-k)
  have hd : (0 : ℚ) < (trimDen e : ℚ) := by
    exact_mod_cast trim_den_pos e
  have hnum : (10 : ℚ) ^ (-k) * 2 ^ (128 - pe) * trimDen e = trimNum e := by
    rw [power10_exact_ratio, ← trimNum, ← trimDen,
      div_mul_cancel₀ _ (ne_of_gt hd)]
  -- The inverse scale `s = 2^(1-e)·10^k` turns the power-of-ten factor into
  -- `2^(128-h)`, which is where the shift alignment is spent.
  have hscale : (10 : ℚ) ^ (-k) * 2 ^ (128 - pe) * (2 ^ (1 - e) * 10 ^ k)
      = 2 ^ (128 - exponentShift e) := by
    have h10 : (10 : ℚ) ^ (-k) * 10 ^ k = 1 := by
      rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp
    have halign : (exponentShift e : ℤ) + 1 - pe = e :=
      exponent_shift_align e he
    have hsh := exponent_shift_lt_four e he
    calc (10 : ℚ) ^ (-k) * 2 ^ (128 - pe) * (2 ^ (1 - e) * 10 ^ k)
        = (10 ^ (-k) * 10 ^ k) * (2 ^ (128 - pe) * 2 ^ (1 - e)) := by
          ring
      _ = (2 : ℚ) ^ ((128 - pe) + (1 - e)) := by
          rw [h10, one_mul, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = 2 ^ (128 - exponentShift e) := by
          rw [show (128 - pe) + (1 - e) = ((128 - exponentShift e : ℕ) : ℤ)
                from by omega, zpow_natCast]
  rw [trimMul]
  push_cast
  rw [← hscale, ← hnum]
  ring

/-- The scale sends half a scaled ULP to `trimNum`. -/
theorem trim_mul_half_ulp (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    let k := decimalExponent e
    ulp e * 10 ^ (-k) / 2 * (trimMul e : ℚ) = (trimNum e : ℚ) := by
  intro k
  calc ulp e * 10 ^ (-k) / 2 * (trimMul e : ℚ)
      = (trimNum e : ℚ) * (2 ^ e * 2 ^ (1 - e) / 2)
          * (10 ^ (-k) * 10 ^ k) := by
        rw [ulp, trim_mul_eq e he]; ring
    _ = (trimNum e : ℚ) := by
        rw [← zpow_add₀ (two_ne_zero' ℚ) e (1 - e),
          show e + (1 - e) = 1 from by ring, zpow_one,
          ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) (-k) k,
          show -k + k = 0 from by ring, zpow_zero]
        ring

/-- The one yy-specific fact the generic bridge needs: `trimMul` sends the
    scaled value to the integer `2·f·num`, so every candidate distance is an
    integer. -/
theorem trim_value_scaled (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    value f e * 10 ^ (-decimalExponent e) * (trimMul e : ℚ)
      = ((2 * f * trimNum e : ℤ) : ℚ) := by
  push_cast
  rw [← trim_mul_half_ulp e he, value, ulp]
  ring

/-- Half a ULP is worth `trimNum` in one copy of the scale: the threshold the
    bridge takes for both multiple-of-ten candidates. -/
theorem trim_half_ulp_scaled (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ulp e * 10 ^ (-decimalExponent e) / 2 * ((1 : ℕ) * (trimMul e : ℚ))
      = ((trimNum e : ℕ) : ℚ) := by
  rw [Nat.cast_one, one_mul]
  exact trim_mul_half_ulp e he

/-- A candidate round-trips exactly when its signed distance stays within
    `trimNum`, strictly so for odd `f`. This is the only use either direction of
    the coarse argument makes of `ℚ`, so soundness and completeness below are
    the two directions of one integer comparison rather than two proofs. -/
theorem roundtrips_iff_dist (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) {c : ℕ}
    {dist : ℤ} (hc : (c : ℤ) * trimMul e + dist = 2 * f * trimNum e) :
    Roundtrips f e (c * 10 ^ decimalExponent e)
      ↔ if f % 2 = 0 then -(trimNum e : ℤ) ≤ dist ∧ dist ≤ trimNum e
        else -(trimNum e : ℤ) < dist ∧ dist < trimNum e := by
  obtain ⟨hle, hlt, -⟩ := scaled_cmp_of_int_eq (trim_mul_pos e) one_pos
    (trim_value_scaled f e he) (trim_half_ulp_scaled e he) hc
  refine (roundtrips_iff_scaled f e (decimalExponent e) c).trans ?_
  split_ifs
  · exact hle.trans (by omega)
  · exact hlt.trans (by omega)

/-- The trim-down candidate sits `trimGap` below the scaled value: it is the
    quotient at the coarse step, which is ten unit steps. -/
theorem dec_ten_down_scaled (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    (sigTen f e : ℤ) * trimMul e + trimGap f e = 2 * f * trimNum e := by
  have h : sigTen f e * trimMul e + trimGap f e = 2 * f * trimNum e :=
    calc sigTen f e * trimMul e + trimGap f e
        = 2 * f * trimSig e / trimModulus e * trimScale e + trimGap f e := by
          rw [sig_hi_ten_quotient f e hsh, trim_scale_eq_ten_mul]
          ring
      _ = 2 * f * trimNum e := step_quotient_add_gap _ f e
  exact_mod_cast h

/-- The trim-up candidate sits `trimScale - trimGap` above it, the coarse step
    being ten unit steps. Its distance is signed, and the sign is why the
    identity is stated in `ℤ`. -/
theorem dec_ten_up_scaled (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    ((sigTen f e + 10 : ℕ) : ℤ) * trimMul e
        + ((trimGap f e : ℤ) - trimScale e)
      = 2 * f * trimNum e := by
  have hten : (trimScale e : ℤ) = 10 * trimMul e := by
    exact_mod_cast trim_scale_eq_ten_mul e
  push_cast
  linear_combination dec_ten_down_scaled f e hsh - hten

/-- One ULP spans `[1, 10)` grid steps at yy's exponent. One grid step is
    `2^(128-h)·den` while half a ULP is `num ≥ 2^127·den`, which gives the first
    bound; the second is the narrowness certificate of the packed comparison. -/
theorem ulp_scaled_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    1 ≤ ulp e * 10 ^ (-decimalExponent e) ∧
      ulp e * 10 ^ (-decimalExponent e) < 10 := by
  have hsh := exponent_shift_lt_four e he
  have hpos : (0 : ℚ) < (trimMul e : ℚ) := by exact_mod_cast trim_mul_pos e
  have hstep : (ulp e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = 2 * (trimNum e : ℚ) := by
    linear_combination 2 * trim_mul_half_ulp e he
  have hlow : (trimMul e : ℚ) ≤ 2 * (trimNum e : ℚ) := by
    have h1 : trimMul e ≤ 2 ^ 128 * trimDen e := by
      rw [trimMul]
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 := trim_num_lower e he
    exact_mod_cast (show trimMul e ≤ 2 * trimNum e by omega)
  have hhigh : 2 * (trimNum e : ℚ) < 10 * (trimMul e : ℚ) := by
    have hn : 2 * trimNum e < trimScale e := trim_two_num_lt_scale e he
    rw [trim_scale_eq_ten_mul] at hn
    exact_mod_cast hn
  refine ⟨(mul_le_mul_iff_of_pos_right hpos).mp ?_,
    (mul_lt_mul_iff_of_pos_right hpos).mp ?_⟩
  · rw [one_mul, hstep]; exact hlow
  · rw [hstep]; exact hhigh

/-! ## The coarse decisions

Each trim flag is pinned to its candidate by two composed equivalences.
`flag ↔ gap` says what the packed comparison decides about `trimGap`, and
`roundtrips_iff_dist` says when that same gap admits a round-trip; together they
give `flag ↔ round-trips`, which consumers read in whichever direction they
need.

The first equivalence is where the work is. Because yy compares quantities
truncated to window units, a packed tie can hide which side of the exact
rounding boundary the candidate lies on. For even `f`, ties are accepted, so a
rejection implies at least one full window unit of separation, enough to
dominate the power-of-ten truncation error. For odd `f`, ties are rejected, so
the ambiguous packed-tie cases can lie just inside that boundary;
`d0_gap_tie_or_far` and `u0_sum_tie_or_far` confine each comparison to either a
stable side or one of those narrow windows, which the certificates then close.
The one window that survives is the `roundU0` tie at `k = 0`, one unit farther
out, where the power-of-ten approximation is exact and the tie is a genuine one
that yy resolves the exact way.
-/

/-! ### The trim-down decision -/

/-- What `roundD0` decides, from the stable/exceptional split alone. -/
theorem round_d0_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then trimGap f e ≤ trimNum e
        else trimGap f e < trimNum e := by
  have hsh := exponent_shift_lt_four e hr.range
  -- yy's test is `c ≤ p` for even `f` and `c < p` for odd `f`, that is
  -- `c < p + 1` and `c < p + 0`.
  have hflag : (toDecimalCandidates f e).roundD0
      = if trimSig e / trimUnit e = trimResidue f e / trimUnit e then
          decide (f % 2 = 0)
        else decide (trimResidue f e / trimUnit e < trimSig e / trimUnit e) := by
    rw [← trim_c_eq f e hsh, ← trim_half_ulp_eq e hsh]
    rfl
  have hpacked : (toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then
          trimResidue f e / trimUnit e < trimSig e / trimUnit e + 1
        else trimResidue f e / trimUnit e < trimSig e / trimUnit e + 0 := by
    rw [hflag]
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  rw [hpacked, packed_iff, packed_iff]
  have herr := trim_err_le_drop f e hr
  have hdrop := trim_drop_lt_err_add_edge f e hr
  rcases d0_gap_tie_or_far f e hr with htie | hfar
  · -- A genuine exact tie, accepted for even `f` and rejected for odd `f` by
    -- the packed comparison and the exact one alike.
    rw [htie]
    split_ifs <;> omega
  · -- Far from the boundary: the approximation cannot matter.
    split_ifs
    · rw [show trimNum e + trimErr f e + 1 * trimEdge e
          = trimNum e + (trimErr f e + trimEdge e) from by ring]
      exact (comparison_stable_of_far (l := trimDrop e)
        (r := trimErr f e + trimEdge e) (w := trimEdge e)
        (by omega) (by omega) hfar).1
    · rw [show trimNum e + trimErr f e + 0 * trimEdge e
          = trimNum e + trimErr f e from by ring]
      exact (comparison_stable_of_far (l := trimDrop e) (r := trimErr f e)
        (w := trimEdge e) (by omega) (by omega) hfar).2

/-- `roundD0` fires exactly when the trim-down candidate round-trips. Both are
    a bound on `trimGap` by `trimNum`, since the gap is that candidate's
    distance from the scaled value, and the lower end of the round-trip
    interval is free because a gap is never negative. -/
theorem round_d0_iff_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundD0 = true
      ↔ Roundtrips f e (sigTen f e * 10 ^ decimalExponent e) := by
  rw [round_d0_iff_gap f e hr, roundtrips_iff_dist f e hr.range
    (dec_ten_down_scaled f e (exponent_shift_lt_four e hr.range))]
  split_ifs <;> omega

/-! ### The trim-up decision -/

/-- What `roundU0` decides. The packed sum `s` counts window edges below
    `gap + num`, and the coarse step is `10·2^60` of them, so the dichotomy
    places `s` relative to that constant: more than one edge below the boundary
    puts `s + 1` short of it, more than one edge above puts `s` past it, and an
    exact tie leaves only `s` one short or `s` exact with nothing discarded.
    Those last two are yy's two special branches. -/
theorem round_u0_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundU0 = true
      ↔ if f % 2 = 0 then trimScale e ≤ trimGap f e + trimNum e
        else trimScale e < trimGap f e + trimNum e := by
  have hsh := exponent_shift_lt_four e hr.range
  have hflag : (toDecimalCandidates f e).roundU0
      = (if trimResidue f e / trimUnit e + trimSig e / trimUnit e + 1
            = 10 * 2 ^ 60 then decide (f % 2 = 0)
        else if decimalExponent e = 0
            ∧ trimResidue f e / trimUnit e + trimSig e / trimUnit e
              = 10 * 2 ^ 60 then decide (f % 2 = 0)
        else decide (10 * 2 ^ 60
          ≤ trimResidue f e / trimUnit e + trimSig e / trimUnit e)) := by
    rw [← trim_c_eq f e hsh, ← trim_half_ulp_eq e hsh]
    rfl
  have hid := trim_packed_sum f e
  have hD := trim_err_dropU_lt f e hr
  have hscale := trim_scale_eq_edge e hsh
  have hE : 0 < trimEdge e :=
    Nat.mul_pos (trim_unit_pos e) (trim_den_pos e)
  rw [hflag]
  set s := trimResidue f e / trimUnit e + trimSig e / trimUnit e with hs
  rcases u0_sum_tie_or_far f e hr with htie | hhi | hlo
  -- An exact tie. Since the discarded error is under two edges, the packed sum
  -- is either one edge short of the step or exactly on it with nothing
  -- discarded, and both are branches yy takes for even `f` alone, as the exact
  -- comparison does.
  · have hle : s ≤ 10 * 2 ^ 60 := Nat.le_of_mul_le_mul_left (by omega) hE
    have hnear : 10 * 2 ^ 60 < s + 2 := by
      have hexp : trimEdge e * (s + 2) = trimEdge e * s + 2 * trimEdge e := by
        ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdge e) (by omega)
    rcases Nat.lt_or_ge s (10 * 2 ^ 60) with hlt | hge
    · rw [ite_eq_left (by omega)]
      split_ifs with hpar <;> simp only [decide_eq_true_eq] <;> omega
    · have heq : s = 10 * 2 ^ 60 := by omega
      rw [heq] at hid
      rw [ite_eq_right (by omega), ite_eq_left
        ⟨u0_tie_k_zero f e hr (by omega) htie, heq⟩]
      split_ifs with hpar <;> simp only [decide_eq_true_eq] <;> omega
  -- More than one edge above the boundary, so `s` has passed the step and the
  -- plain test fires. A packed tie is out of reach: it would need `k = 0`,
  -- where nothing is discarded and the sum would be the boundary itself.
  · have hge : 10 * 2 ^ 60 < s + 1 := by
      have hexp : trimEdge e * (s + 1) = trimEdge e * s + trimEdge e := by ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdge e) (by omega)
    have hnot : ¬(decimalExponent e = 0 ∧ s = 10 * 2 ^ 60) := by
      rintro ⟨hk, heq⟩
      have hzero := u0_err_dropU_k_zero f e hr hk
      rw [heq] at hid
      omega
    rw [ite_eq_right (by omega), ite_eq_right hnot]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  -- More than one edge below it, so even `s + 1` falls short and no test fires.
  · have hlt : s + 1 < 10 * 2 ^ 60 := by
      have hexp : trimEdge e * (s + 1) = trimEdge e * s + trimEdge e := by ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdge e) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega

/-- `roundU0` fires exactly when the trim-up candidate round-trips. Its
    distance `trimGap - trimScale` is signed: the flag is the lower end of the
    round-trip interval, and the upper end is free because the gap never
    reaches a coarse step plus half a ULP. -/
theorem round_u0_iff_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundU0 = true
      ↔ Roundtrips f e ((sigTen f e + 10 : ℕ) * 10 ^ decimalExponent e) := by
  have hroom := trim_gap_lt_scale_add f e hr
  rw [round_u0_iff_gap f e hr, roundtrips_iff_dist f e hr.range
    (dec_ten_up_scaled f e (exponent_shift_lt_four e hr.range))]
  split_ifs <;> omega

/-! ## The unit-step decision

`decOne` is `sigHi` rounded to nearest using the discarded word `sigLo`. In
the scale `trimMul = 2^(128-h)·den`, `sigHi` sits `oneGap` below the scaled
value and rounding up adds one whole `trimMul`. The `roundU1` test bounds the
remainder relative to half a unit step, with only the bits below `sigLo` unseen.

`decOne` is never asked to round-trip directly: it is emitted only when nothing
coarser round-trips, and then the exact method's fine case derives the
round-trip from the half-step bound, the grid at `decimalExponent e` being no
coarser than one ULP. So the only obligation here is that bound, a comparison
of `2·oneGap` with `trimMul` in which a midpoint goes up only from an odd
`sigHi`. That is one bound per parity, which is what `round_u1_iff_gap` states.
-/

/-- The residue at the unit step: `sigHi·2^(128-h) + oneResidue` is the
    product `2·f·p10`. -/
def oneResidue (f : ℕ) (e : ℤ) : ℕ :=
  stepResidue (2 ^ (128 - exponentShift e)) f e

/-- The gap at the unit step, the distance from `sigHi` to the scaled value once
    the denominator is cleared. -/
def oneGap (f : ℕ) (e : ℤ) : ℕ := stepGap (2 ^ (128 - exponentShift e)) f e

/-- `sigLo` is the unit-step remainder with its low `64 - h` bits discarded, so
    the packed test sees the remainder only in units of `2^(64-h)`. -/
theorem sig_lo_eq_residue_div (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    sigLo f e = oneResidue f e / 2 ^ (64 - exponentShift e) := by
  rw [sig_lo_eq, oneResidue, stepResidue, pow_shift_split e 128 (by omega),
    Nat.mul_mod_mul_left, pow_shift_split e 64 (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- What `roundU1` decides about the remainder. yy compares the discarded word
    with half its range, which is the remainder against half a unit step,
    `2^(127-h)`, blind to the `2^(64-h)` bits below `sigLo`. Half a step divides
    down to exactly `2^63`, so the whole band `[half, half + 2^(64-h))` reads as
    a packed tie, which yy resolves by the parity of `sigHi`: an odd one rounds
    up from the band, an even one waits until the remainder has left it. -/
theorem one_round_half (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    (toDecimalCandidates f e).roundU1 = true
      ↔ if sigHi f e % 2 = 0
        then 2 ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e)
          ≤ oneResidue f e
        else 2 ^ (127 - exponentShift e) ≤ oneResidue f e := by
  have hpos : (0 : ℕ) < 2 ^ (64 - exponentShift e) := by positivity
  have hlo := sig_lo_eq_residue_div f e hsh
  have hpow : (2 : ℕ) ^ 63 * 2 ^ (64 - exponentShift e)
      = 2 ^ (127 - exponentShift e) := by
    rw [← pow_add]
    congr 1
    omega
  have hround : (toDecimalCandidates f e).roundU1
      = if sigLo f e = 2 ^ 63 then decide (sigHi f e % 2 = 1)
        else decide (2 ^ 63 < sigLo f e) := rfl
  -- Reaching half a step is `sigLo ≥ 2^63`, and leaving the tie band is
  -- `sigLo > 2^63`; both are the same division.
  have hhalf : 2 ^ (127 - exponentShift e) ≤ oneResidue f e
      ↔ 2 ^ 63 ≤ sigLo f e := by
    rw [hlo, Nat.le_div_iff_mul_le hpos, hpow]
  have hpast : 2 ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e)
      ≤ oneResidue f e ↔ 2 ^ 63 < sigLo f e := by
    rw [Nat.lt_iff_add_one_le, hlo, Nat.le_div_iff_mul_le hpos, add_mul, one_mul,
      hpow]
  rw [hround, hhalf, hpast]
  rcases lt_trichotomy (sigLo f e) (2 ^ 63) with hs | hs | hs
  · rw [ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · rw [ite_eq_left hs]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · rw [ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega

/-- `sigHi` sits exactly `oneGap` below the scaled value: `step_quotient_add_gap`
    at the unit step. -/
theorem sig_hi_scaled (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    (sigHi f e : ℤ) * trimMul e + oneGap f e = 2 * f * trimNum e := by
  have h : sigHi f e * trimMul e + oneGap f e = 2 * f * trimNum e := by
    rw [sig_hi_quotient f e hsh]; exact step_quotient_add_gap _ f e
  exact_mod_cast h

/-! Rounding up needs no additional separation: when `roundU1` fires, the packed
remainder has reached half a unit step, hence the exact gap has reached at
least half a step, since power-of-ten truncation only increases it.

Rounding down and exact midpoints are subtler. The packed test sees the
remainder only down to `2^(64-h)`, while the exact gap also contains the
truncation term `2·f·(num % den)`. Thus the packed comparison alone cannot
exclude a gap just past half a step or guarantee that an exact midpoint appears
as a packed midpoint. `one_residue_below_half` and `one_tie_band_even` are the
certificates that close those two windows, one window family per exponent.
-/

/-- The unit-step gap is the denominator-cleared remainder plus the
    power-of-ten truncation error. -/
theorem one_gap_split (f : ℕ) (e : ℤ) :
    oneGap f e
      = trimDen e * oneResidue f e + 2 * f * (trimNum e % trimDen e) := by
  rw [oneGap, stepGap, ← oneResidue]

/-- The gap exceeds a whole step only by the power-of-ten truncation error,
    which is under half a step, so rounding up always lands within one and a
    half steps of the value. -/
theorem one_gap_lt_step_and_half (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hsh : exponentShift e < 4) : 2 * oneGap f e < 3 * trimMul e := by
  have hres : trimDen e * oneResidue f e < trimMul e := by
    rw [trimMul, Nat.mul_comm (2 ^ (128 - exponentShift e)) (trimDen e)]
    exact mul_lt_mul_of_pos_left
      (by rw [oneResidue, stepResidue]; exact Nat.mod_lt _ (by positivity))
      (trim_den_pos e)
  have htrunc := trim_trunc_lt f e hr
  have hhalf := trim_two_trunc_le_mul e hsh
  rw [one_gap_split]
  omega

/-! ### Refuting the unit-step windows

Two bands of the remainder are left undecided, both at the midpoint
`2^(127-h)` of the unit step. Just below it the truncation error `2·f·τ` can
carry the exact gap past half a step while yy rounds down; at and just above it
yy reads a packed tie and resolves it by the parity of `sigHi`, which the exact
gap knows nothing about.

An odd `sigHi` rounds up, so the tie band is dangerous only for an even one.
That parity is the next bit of the same product, which the doubled modulus
`2^(129-h)` sees: the residue stays below one unit step exactly when `sigHi` is
even. Both bands are windows there, refuted per exponent the way `expWindows`
refutes the coarse ones.

An exact power-of-ten approximation has no truncation error, so the band below
the midpoint is harmless and the midpoint is a genuine tie, resolved to even.
Those exponents refute the band above the midpoint only.
-/

/-- The residue in the doubled modulus, one bit wider than the unit step. -/
def oneParityResidue (f : ℕ) (e : ℤ) : ℕ :=
  stepResidue (2 ^ (129 - exponentShift e)) f e

/-- That bit, split off: the doubled residue carries one whole unit step above
    the remainder exactly when `sigHi` is odd. -/
theorem one_parity_residue_split (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    oneParityResidue f e
      = 2 ^ (128 - exponentShift e) * (sigHi f e % 2) + oneResidue f e := by
  have hw : (2 : ℕ) ^ (129 - exponentShift e)
      = 2 ^ (128 - exponentShift e) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hhi : oneParityResidue f e / 2 ^ (128 - exponentShift e)
      = sigHi f e % 2 := by
    rw [oneParityResidue, stepResidue, hw, Nat.mod_mul_right_div_self,
      ← sig_hi_quotient f e hsh]
  have hlo : oneParityResidue f e % 2 ^ (128 - exponentShift e)
      = oneResidue f e := by
    rw [oneParityResidue, stepResidue, Nat.mod_mod_of_dvd _ ⟨2, hw⟩, oneResidue,
      stepResidue]
  conv_lhs => rw [← Nat.div_add_mod (oneParityResidue f e)
    (2 ^ (128 - exponentShift e))]
  rw [hhi, hlo]

/-- The undecided bands as windows on the doubled residue. The truncation error
    is below `2^54·den`, so `2^54` bounds its reach in remainder units. -/
private def oneWindows (e : ℤ) : ModWindows where
  g := 2 * trimSig e
  modulus := 2 ^ (129 - exponentShift e)
  f0 := 1
  f1 := 2 ^ 53 - 1
  windows :=
    let half : ℤ := 2 ^ (127 - exponentShift e)
    let band : ℤ := 2 ^ (64 - exponentShift e)
    let w : ℤ := 2 ^ (128 - exponentShift e)
    -- The packed tie band above the midpoint, for an even `sigHi`.
    (half + 1, half + band - 1) ::
      if trimNum e % trimDen e = 0 then []
      else
        -- The midpoint, which only an even `sigHi` reaches wrongly, and the
        -- truncation error's reach below it, which either parity reaches.
        [(half - 2 ^ 54, half), (w + half - 2 ^ 54, w + half - 1)]

/-- Close `∃ q, (oneWindows e).refutedBy q = true` for a literal exponent. -/
elab "one_cert" : tactic => modCertTactic fun e => (oneWindows e).search

private theorem one_windows_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (oneWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> one_cert

/-- A doubled residue landing in a refuted window is impossible: it is the
    residue of `2·p10·f` modulo one bit more than the unit step. -/
private theorem one_no_window_hit {lo hi q : ℤ} (f : ℕ) (e : ℤ)
    (hr : Regular f e)
    (hcert : (oneWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (oneWindows e).windows)
    (hlo : lo ≤ (oneParityResidue f e : ℤ))
    (hhi : (oneParityResidue f e : ℤ) ≤ hi) :
    False := by
  obtain ⟨⟨hf_pos, hf_hi, -⟩, -⟩ := hr
  refine (oneWindows e).not_hit f ?_ hcert hmem ?_ ?_ ?_ hlo hhi <;>
    simp only [oneWindows]
  · positivity
  · omega
  · omega
  · rw [oneParityResidue, stepResidue, Nat.mul_right_comm]

/-- A truncated power-of-ten approximation adds the midpoint and the truncation
    error's reach below it, one for each parity of `sigHi`. -/
private theorem one_windows_truncated (e : ℤ)
    (hτ : trimNum e % trimDen e ≠ 0) :
    ((2 : ℤ) ^ (127 - exponentShift e) - 2 ^ 54,
        (2 : ℤ) ^ (127 - exponentShift e)) ∈ (oneWindows e).windows ∧
      ((2 : ℤ) ^ (128 - exponentShift e) + 2 ^ (127 - exponentShift e) - 2 ^ 54,
          (2 : ℤ) ^ (128 - exponentShift e) + 2 ^ (127 - exponentShift e) - 1)
        ∈ (oneWindows e).windows := by
  simp only [oneWindows, ite_eq_right hτ]
  exact ⟨.tail _ (.head _), .tail _ (.tail _ (.head _))⟩

/-- Below the midpoint the truncation error cannot reach it: a remainder short
    of half a unit step is short of it by more than `2^54`. -/
theorem one_residue_below_half (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hτ : trimNum e % trimDen e ≠ 0)
    (hres : oneResidue f e < 2 ^ (127 - exponentShift e)) :
    oneResidue f e + 2 ^ 54 < 2 ^ (127 - exponentShift e) := by
  by_contra hcon
  have hsh := exponent_shift_lt_four e hr.range
  obtain ⟨q, hcert⟩ := one_windows_refuted e hr.range
  obtain ⟨hbelow, habove⟩ := one_windows_truncated e hτ
  -- The remainder is in the last `2^54` below the midpoint; the parity of
  -- `sigHi` decides which of the two windows holds it.
  have hlo : (2 : ℤ) ^ (127 - exponentShift e)
      ≤ (oneResidue f e : ℤ) + 2 ^ 54 := by
    exact_mod_cast
      (show 2 ^ (127 - exponentShift e) ≤ oneResidue f e + 2 ^ 54 from by omega)
  have hhi : (oneResidue f e : ℤ) + 1
      ≤ (2 : ℤ) ^ (127 - exponentShift e) := by
    exact_mod_cast hres
  have hsplit := one_parity_residue_split f e hsh
  rcases Nat.mod_two_eq_zero_or_one (sigHi f e) with hpar | hpar
  -- Even `sigHi`: the doubled residue is the remainder itself.
  · have hp : (oneParityResidue f e : ℤ) = (oneResidue f e : ℤ) := by
      rw [hsplit, hpar]; push_cast; ring
    exact one_no_window_hit f e hr hcert hbelow (by rw [hp]; linarith)
      (by rw [hp]; linarith)
  -- Odd `sigHi`: one whole window above it.
  · have hp : (oneParityResidue f e : ℤ)
        = (2 : ℤ) ^ (128 - exponentShift e) + (oneResidue f e : ℤ) := by
      rw [hsplit, hpar]; push_cast; ring
    exact one_no_window_hit f e hr hcert habove (by rw [hp]; linarith)
      (by rw [hp]; linarith)

/-- In the packed tie band, an even `sigHi` occurs only at a genuine midpoint:
    the remainder is exactly at the unit-step midpoint and the power-of-ten
    approximation is exact. Hence the exact value is a tie too, which yy
    resolves to even. -/
theorem one_tie_band_even (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hpar : sigHi f e % 2 = 0)
    (hlo : 2 ^ (127 - exponentShift e) ≤ oneResidue f e)
    (hhi : oneResidue f e
      < 2 ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e)) :
    oneResidue f e = 2 ^ (127 - exponentShift e)
      ∧ trimNum e % trimDen e = 0 := by
  have hsh := exponent_shift_lt_four e hr.range
  obtain ⟨q, hcert⟩ := one_windows_refuted e hr.range
  have hp : (oneParityResidue f e : ℤ) = (oneResidue f e : ℤ) := by
    rw [one_parity_residue_split f e hsh, hpar]; push_cast; ring
  -- Bounds for the part of the tie band strictly above the midpoint.
  have hup : (oneParityResidue f e : ℤ)
      ≤ (2 : ℤ) ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e) - 1 := by
    rw [hp]
    have hz : (oneResidue f e : ℤ) + 1
        ≤ (2 : ℤ) ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e) := by
      exact_mod_cast (show oneResidue f e + 1
        ≤ 2 ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e) from hhi)
    linarith
  have hdown (hgt : 2 ^ (127 - exponentShift e) < oneResidue f e) :
      (2 : ℤ) ^ (127 - exponentShift e) + 1 ≤ (oneParityResidue f e : ℤ) := by
    rw [hp]
    exact_mod_cast
      (show 2 ^ (127 - exponentShift e) + 1 ≤ oneResidue f e from hgt)
  -- The region strictly above the midpoint is refuted, leaving only
  -- the midpoint.
  have hband (hgt : 2 ^ (127 - exponentShift e) < oneResidue f e) : False :=
    one_no_window_hit f e hr hcert (.head _) (hdown hgt) hup
  have hmid : oneResidue f e = 2 ^ (127 - exponentShift e) := by
    rcases Nat.eq_or_lt_of_le hlo with heq | hgt
    · exact heq.symm
    · exact (hband hgt).elim
  -- A truncated power-of-ten approximation refutes the midpoint too, so it is
  -- exact here.
  refine ⟨hmid, ?_⟩
  by_contra hτ
  obtain ⟨hwin, -⟩ := one_windows_truncated e hτ
  have hz : (oneParityResidue f e : ℤ) = (2 : ℤ) ^ (127 - exponentShift e) := by
    rw [hp, hmid]; push_cast; ring
  exact one_no_window_hit f e hr hcert hwin
    (by rw [hz]; exact sub_le_self _ (by positivity)) (by rw [hz])

/-! ### What roundU1 decides -/

/-- Strictly below the packed midpoint the exact gap is strictly below half a
    step. When the power of ten is exact the remainder is a whole `den` short;
    otherwise it is `2^54·den` short, which is what the certificate says. -/
theorem one_below_half (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hlt : oneResidue f e < 2 ^ (127 - exponentShift e)) :
    2 * oneGap f e < trimMul e := by
  have hsh := exponent_shift_lt_four e hr.range
  have hden := trim_den_pos e
  have htrunc := trim_trunc_lt f e hr
  have hstep := trim_mul_eq_two_half e hsh
  have hgap := one_gap_split f e
  by_cases hτ : trimNum e % trimDen e = 0
  · have hmono : trimDen e * (oneResidue f e + 1)
        ≤ trimDen e * 2 ^ (127 - exponentShift e) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : trimDen e * (oneResidue f e + 1)
        = trimDen e * oneResidue f e + trimDen e := by ring
    rw [hτ] at hgap
    omega
  · have hroom := one_residue_below_half f e hr hτ hlt
    have hmono : trimDen e * (oneResidue f e + 2 ^ 54)
        ≤ trimDen e * 2 ^ (127 - exponentShift e) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : trimDen e * (oneResidue f e + 2 ^ 54)
        = trimDen e * oneResidue f e + 2 ^ 54 * trimDen e := by ring
    omega

/-- yy's unit-step decision is the exact one: it rounds up exactly when the gap
    has passed half a step, with an exact midpoint going up only from an odd
    `sigHi`. The remainder reaching half a step is what carries the gap there,
    the truncation error being too small to close the distance on its own; the
    tie band above it is where the two could disagree, and the certificate
    leaves only the genuine midpoint, which both sides resolve to even. -/
theorem round_u1_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundU1 = true
      ↔ if sigHi f e % 2 = 0 then trimMul e < 2 * oneGap f e
        else trimMul e ≤ 2 * oneGap f e := by
  have hsh := exponent_shift_lt_four e hr.range
  have hden := trim_den_pos e
  have hgap := one_gap_split f e
  have hstep := trim_mul_eq_two_half e hsh
  -- One remainder unit is worth `trimDen` of the cleared gap, so a remainder at
  -- or past half a step puts the gap at or past half a step too.
  have hmono (n : ℕ) (h : n ≤ oneResidue f e) :
      trimDen e * n ≤ trimDen e * oneResidue f e := Nat.mul_le_mul_left _ h
  rw [one_round_half f e hsh]
  split_ifs with hpar
  -- Even `sigHi`: yy waits for the remainder to leave the tie band, and below
  -- the band the certificate leaves only the genuine midpoint, where the gap is
  -- half a step exactly and the strict comparison declines as yy does.
  · refine ⟨fun hres => ?_, fun hlt => ?_⟩
    · have hb : (0 : ℕ) < 2 ^ (64 - exponentShift e) := by positivity
      have hexp : trimDen e
          * (2 ^ (127 - exponentShift e) + 2 ^ (64 - exponentShift e))
          = trimDen e * 2 ^ (127 - exponentShift e)
            + trimDen e * 2 ^ (64 - exponentShift e) := by ring
      have := hmono _ hres
      have : 0 < trimDen e * 2 ^ (64 - exponentShift e) := by positivity
      omega
    · by_contra hcon
      rcases Nat.lt_or_ge (oneResidue f e) (2 ^ (127 - exponentShift e)) with
        hlo | hlo
      · have := one_below_half f e hr hlo
        omega
      · obtain ⟨hres, hτ⟩ :=
          one_tie_band_even f e hr hpar hlo (by omega)
        rw [hgap, hres, hτ] at hlt
        omega
  -- Odd `sigHi`: yy rounds up from the tie band, and the non-strict comparison
  -- accepts it, so only the remainder short of half a step has to be excluded.
  · refine ⟨fun hres => ?_, fun hle => ?_⟩
    · have := hmono _ hres
      omega
    · by_contra hcon
      have := one_below_half f e hr (by omega)
      omega

/-- `decOne` sits `oneGap` below the scaled value, less one whole step when it
    rounds up. -/
theorem dec_one_scaled (f : ℕ) (e : ℤ) (hsh : exponentShift e < 4) :
    let c := toDecimalCandidates f e
    (c.decOne : ℤ) * trimMul e
        + ((oneGap f e : ℤ) - if c.roundU1 = true then (trimMul e : ℤ) else 0)
      = 2 * f * trimNum e := by
  intro c
  have h := sig_hi_scaled f e hsh
  show ((sigHi f e + if c.roundU1 then 1 else 0 : ℕ) : ℤ) * _ + _ = _
  cases c.roundU1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    push_cast <;> linarith

/-- `decOne` is a nearest value on the grid at `decimalExponent e`, ties to
    even. Half a step is one `trimMul` over two of them, so `round_u1_iff_gap`
    bounds the distance either way, and it is a bound on the same parity of
    `sigHi` that decides which way `decOne` went, so a tie lands on even. -/
theorem dec_one_nearest (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let c := toDecimalCandidates f e
    let x := value f e * 10 ^ (-decimalExponent e)
    |(c.decOne : ℚ) - x| ≤ 1 / 2 ∧
      (|(c.decOne : ℚ) - x| = 1 / 2 → c.decOne % 2 = 0) := by
  intro c x
  have hsh := exponent_shift_lt_four e hr.range
  have hmul := trim_mul_pos e
  obtain ⟨hle, -, heq⟩ := scaled_cmp_of_int_eq (a := 2) (b := trimMul e)
    (thr := 1 / 2) (trim_mul_pos e) two_pos (trim_value_scaled f e hr.range)
    (by push_cast; ring) (dec_one_scaled f e hsh)
  have hwide := one_gap_lt_step_and_half f e hr hsh
  have hflag := round_u1_iff_gap f e hr
  rw [hle, heq]
  cases hu1 : c.roundU1
  -- yy stayed put, so the gap is within half a step, and a tie there is
  -- reachable only from an even `sigHi`, which `decOne` inherits.
  · have hone : c.decOne = sigHi f e := by
      show (sigHi f e + if c.roundU1 then 1 else 0) = _
      rw [hu1]; simp
    rw [hu1] at hflag
    simp only [Bool.false_eq_true, false_iff] at hflag
    rw [ite_eq_right (by simp)]
    split_ifs at hflag <;> omega
  -- yy stepped up, so the gap had passed half a step, and a tie there is
  -- reachable only from an odd `sigHi`, which the step makes even.
  · have hone : c.decOne = sigHi f e + 1 := by
      show (sigHi f e + if c.roundU1 then 1 else 0) = _
      rw [hu1]; simp
    rw [hu1] at hflag
    simp only [true_iff] at hflag
    rw [ite_eq_left (by simp)]
    split_ifs at hflag <;> omega

/-! ## From decisions to exact candidates

The two output theorems read the three equivalences and nothing beneath them.
On the coarse path, yy emits a multiple of ten, and whichever flag selected it
says it round-trips. On the fine path, it emits `decOne`, whose half-step bound
already implies that it round-trips because the grid step at `decimalExponent e`
is at most one ULP.

`coarse_candidate_cases` is the one thing here that goes back to the arithmetic,
and it asks something else of it: that the rounding interval is too narrow to
hold a multiple of ten besides yy's two is a fact about the interval, not about
a decision, so no equivalence could supply it.
-/

/-- On the coarse path, yy emits a multiple of ten that round-trips. Which of
    the two multiple-of-ten candidates `decTen` denotes is decided by `roundU0`;
    whether both trim flags fire is irrelevant. -/
theorem coarse_output_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true →
    let d := (toDecimal f e).1
    d % 10 = 0 ∧ Roundtrips f e ((d : ℚ) * 10 ^ decimalExponent e) := by
  intro c htrim d
  have hy : d = c.decTen := by
    show (if c.roundD0 || c.roundU0 then c.decTen else c.decOne) = _
    rw [htrim]
    rfl
  have hten : c.decTen = sigTen f e + (if c.roundU0 then 10 else 0) := rfl
  rw [hy]
  have h10 := sig_ten_mod_ten f e
  refine ⟨by rw [hten]; cases c.roundU0 <;> simp <;> omega, ?_⟩
  cases hu0 : c.roundU0
  · -- Only `roundD0` fired, so `decTen` is the trim-down candidate.
    have hd0 : c.roundD0 = true := by
      rw [hu0, Bool.or_false] at htrim; exact htrim
    rw [hten, hu0]
    simpa using (round_d0_iff_roundtrips f e hr).mp hd0
  · rw [hten, hu0]
    simpa using (round_u0_iff_roundtrips f e hr).mp hu0

/-- On the fine path, yy emits `decOne`, a nearest value on its own grid. -/
theorem fine_output_nearest (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = false →
    let d := (toDecimal f e).1
    let x := value f e * 10 ^ (-decimalExponent e)
    |(d : ℚ) - x| ≤ 1 / 2 ∧ (|(d : ℚ) - x| = 1 / 2 → d % 2 = 0) := by
  intro c htrim d
  rw [show d = c.decOne from by
    show (if c.roundD0 || c.roundU0 then _ else _) = _
    rw [htrim]
    rfl]
  exact dec_one_nearest f e hr

/-! ### yy trims whenever it can

The exact method takes the coarse case exactly when the rounding interval
contains a multiple of ten, that is, when a digit can be dropped. yy makes the
same choice through `roundD0` and `roundU0`: it trims when either of its two
coarse candidates round-trips, which is what `round_d0_iff_roundtrips` and
`round_u0_iff_roundtrips` already say. All that is left is to rule out any
other multiple of ten.

The rounding interval is narrower than one coarse step, so yy's two coarse
candidates are the only multiples of ten it can contain. It is therefore enough
to recognize those two. When neither round-trips, yy keeps `decOne`, which lies
on the grid one decimal digit finer.
-/

/-- A multiple of ten that round-trips is one of yy's two coarse candidates,
    `sigTen` or `sigTen + 10`. After scaling by `trimMul`, the lower one sits
    `trimGap` below the scaled value, and that gap is less than one coarse step
    plus half a ULP, with the extra room covering the power-of-ten truncation
    error. This bracket is all `coarse_roundtrip_adjacent` needs to restrict the
    possibilities to those two. -/
theorem coarse_candidate_cases (f : ℕ) (e : ℤ) (hr : Regular f e) (d : ℕ)
    (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ decimalExponent e)) :
    d = sigTen f e ∨ d = sigTen f e + 10 := by
  -- The bracket is one-sided each way rather than an absolute value, so this
  -- consumer takes the distance identity and not the interval bridge.
  have hmul : (0 : ℚ) < (trimMul e : ℚ) := by exact_mod_cast trim_mul_pos e
  have hdown := scaled_dist_eq (trim_value_scaled f e hr.range)
    (dec_ten_down_scaled f e (exponent_shift_lt_four e hr.range))
  push_cast at hdown
  have hhalf := trim_mul_half_ulp e hr.range
  have hgap0 : (0 : ℚ) ≤ (trimGap f e : ℚ) := by positivity
  have hnum0 : (0 : ℚ) ≤ (trimNum e : ℚ) := by positivity
  have hgap : (trimGap f e : ℚ) < (trimScale e : ℚ) + (trimNum e : ℚ) := by
    exact_mod_cast trim_gap_lt_scale_add f e hr
  have hstep : (trimScale e : ℚ) = 10 * (trimMul e : ℚ) := by
    exact_mod_cast trim_scale_eq_ten_mul e
  exact coarse_roundtrip_adjacent f e (decimalExponent e)
    (ulp_scaled_bounds e hr.range).2 (sig_ten_mod_ten f e) h10
    (le_of_mul_le_mul_right (by linarith) hmul)
    (lt_of_mul_lt_mul_right (by linarith) hmul.le) hround

/-- If the rounding interval contains a multiple of ten, yy trims. -/
theorem trim_of_coarse_roundtrip (f : ℕ) (e : ℤ) (hr : Regular f e) (d : ℕ)
    (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ decimalExponent e)) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true := by
  intro c
  rw [Bool.or_eq_true]
  rcases coarse_candidate_cases f e hr d h10 hround with rfl | rfl
  · exact Or.inl ((round_d0_iff_roundtrips f e hr).mpr hround)
  · exact Or.inr ((round_u0_iff_roundtrips f e hr).mpr hround)

/-! ## yy refines the exact method

Nothing above is needed beyond `ulp_scaled_bounds` and the three semantic
obligations `coarse_output_roundtrips`, `fine_output_nearest`, and
`trim_of_coarse_roundtrip`. In particular no claim is made that yy's packed
decisions agree with the exact ones: a packed midpoint need not be an exact
midpoint, and the trim flags are matched to the existence of an exact coarse
candidate, not to any exact comparison.
-/

/-- yy implements the exact method: it trims exactly when an exact coarse
    candidate exists. One direction is `trim_of_coarse_roundtrip`; the other
    holds because trimmed output is itself a multiple of ten that
    round-trips. -/
theorem yy_exact_candidate (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let (d, k) := toDecimal f e
    ExactCandidate f e k d := by
  set c := toDecimalCandidates f e
  by_cases htrim : (c.roundD0 || c.roundU0) = true
  · exact Or.inl (coarse_output_roundtrips f e hr htrim)
  · rw [Bool.not_eq_true] at htrim
    obtain ⟨hle, heven⟩ := fine_output_nearest f e hr htrim
    refine Or.inr ⟨fun ⟨d, h10, hround⟩ => ?_, hle, heven⟩
    rw [trim_of_coarse_roundtrip f e hr d h10 hround] at htrim
    exact Bool.noConfusion htrim

/-- yy is correct on regularly spaced positive binary64 values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid. -/
theorem yy_correct (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let (d, k) := toDecimal f e
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  obtain ⟨hfine, hcoarse⟩ := ulp_scaled_bounds e hr.range
  exact exact_candidate_correct f e (decimalExponent e) hr.pos hfine hcoarse
    (yy_exact_candidate f e hr)
