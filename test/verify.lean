-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import exact

/-! # Correctness of yy

`exact.lean` proves that the exact, Schubfach-like method produces a shortest,
correctly rounded decimal whenever the decimal grid step is at most one ULP and
strictly greater than a tenth of a ULP, and refutes narrow modular windows on
demand. Everything specific to yy is here: the truncated power-of-ten
significand, the packed comparisons, and the windows those comparisons leave
ambiguous, which together show that yy's output is a candidate of that method,
`yy_exact_candidate`. Composing that with the grid bounds at yy's exponent,
`ulp_scaled_bounds`, gives `yy_correct`. No claim is made that yy's packed
decisions agree with the exact ones; only that its output does.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`;
* `h`: the shift `decimalShift e`, aligning `f·2^e` with `10^k`.

## Proof structure

The proof is layered, each layer exposing a small interface to the one above
it. This section gives those interfaces, then where in the file each part of
the argument lives, then the dependencies between them.

### 1. Exact specification (`exact.lean`)

`ExactCandidate` describes the only facts needed about a conversion result:

* coarse case: it is a multiple of ten that round-trips;
* fine case: no multiple of ten round-trips, and the result is a nearest point
  on the current decimal grid, ties to even.

`exact_candidate_correct` proves that either case gives a shortest, correctly
rounded decimal after removing trailing zeros, given only that the grid is no
coarser than one ULP and strictly coarser than a tenth of one.

Thus this file has only two things to prove: that yy's exponent meets those
grid bounds,

    ulp_scaled_bounds

and

    yy_exact_candidate :
      let (d, k) := toDecimal f e
      ExactCandidate f e k d

### 2. Semantic obligations of yy

There are two possible outputs, chosen by yy's trim decision.

* Coarse:
    `coarse_output_roundtrips`
  says yy emits a multiple of ten that round-trips.

* Fine:
    `fine_output_nearest`
  says yy emits a nearest point on the grid at `decimalExponent e`, ties to
  even.

`trim_of_coarse_roundtrip` supplies completeness: if any multiple of ten
round-trips, yy takes the coarse path.

These three facts are assembled by `yy_exact_candidate`.

### 3. File organization

The modeled algorithm and its power-of-ten significand:

    ## The truncated power of ten
    ## yy's conversion
    ## Exponent alignment

The trim path, from packed comparisons to exact inequalities:

    ## The packed trim comparison
    ## Trim bounds in exact arithmetic
    ## Refuting the trim windows
    ## From packed comparisons to trim bounds
    ## From integer bounds to half-ULP bounds

The unit-step path, following an analogous route:

    ## The unit-step candidate
    ## Correct rounding at the unit step
    ### Refuting the unit-step windows
    ### Nearest at the unit step

The two paths are then assembled into the exact-method obligations:

    ## The multiple-of-ten candidates
    ## yy's coarse and fine outputs
    ## Completeness of the trim decision
    ## yy refines the exact method

### 4. Proof dependencies

The main correctness argument has the following structure:

    yy_correct
      ← ulp_scaled_bounds
      ← yy_exact_candidate
          ← coarse_output_roundtrips
          ← fine_output_nearest
          ← trim_of_coarse_roundtrip

The lower-level arithmetic establishing those interface theorems is organized
around the two packed comparisons and the unit step:

    coarse_output_roundtrips, trim_of_coarse_roundtrip
      ← round_d0_iff_gap, round_u0_iff_gap
          ← trim_gap_separated
              ← ModWindows

    fine_output_nearest
      ← dec_one_nearest
          ← one_midpoint_separated
              ← ModWindows
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

/-! ## The truncated power of ten -/

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
  -- This and the three checks like it below enumerate up to 2046 exponents.
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

/-! ## yy's conversion -/

/-- Approximation of floor(e·log₁₀ 2) used as yy's decimal exponent. -/
def decimalExponent (e : ℤ) : ℤ :=
  e * 315_653 / 2 ^ 20

/-- Shift chosen to align the binary exponent with the power of ten. -/
def decimalShift (e : ℤ) : ℕ :=
  Int.toNat (e + (-decimalExponent e * 217_707) / 2 ^ 16)

/-- The 128-bit decimal significand ⌊f·2^(h+1)·⌊10^(-k)·2^128⌋ / 2^64⌋. -/
def scaledSignificand (f : ℕ) (e : ℤ) : ℕ :=
  let k := decimalExponent e
  let h := decimalShift e
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
  let h := decimalShift e

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

/-! ## Exponent alignment -/

/-- The shift used by yy's regular path is less than 4. -/
theorem decimal_shift_lt_four (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    decimalShift e < 4 := by
  unfold decimalShift decimalExponent
  omega

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. The two
    fixed-point constants multiply to just over one, by a part in 2^17.4, and
    that is exactly enough for `omega`'s rational relaxation to still admit a
    shift of `-1`. Ruling it out is a Diophantine fact about the constants
    rather than a magnitude bound, so it is checked; all the arithmetic here is
    small. -/
theorem decimal_shift_nonneg :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971,
      0 ≤ e + (-decimalExponent e * 217_707) / 2 ^ 16 := by
  decide +kernel

/-- The shift undoes the power-of-ten exponent: `h + 1 - pe = e`. Both sides
    scale the same fixed-point quotient, so once the shift is known not to have
    been clamped this is arithmetic, whatever the decimal exponent is. -/
theorem decimal_shift_align (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    (decimalShift e : ℤ) + 1 - power10Exponent (-decimalExponent e) = e := by
  have hnonneg := decimal_shift_nonneg e (by simpa [Finset.mem_Icc] using he)
  unfold decimalShift power10Exponent
  omega

/-! ## The packed trim comparison

yy's `roundD0` and `roundU0` compare the packed value `c` (the last decimal
digit of the integral part, followed by the top 60 bits of `sigLo`) with
`halfUlp`. Both sides are truncated at the same window unit `U`. With

    h = decimalShift e,   p10 = trimSig e,
    N = 10·2^(128-h),     U = 2^(68-h),   W = 2·f·p10 % N

one has `c = W / U`, `halfUlp = p10 / U`, `10·2^60 = N / U`, and
`ten·2^(128-h) + W = 2·f·p10`. Thus the two tests use only the pair
`(W, p10)` measured in units of `U`, and the boundary analysis becomes exact
integer arithmetic rather than an error estimate.
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
def trimModulus (e : ℤ) : ℕ := 10 * 2 ^ (128 - decimalShift e)

/-- One unit in the last place of the packed comparison. -/
def trimUnit (e : ℤ) : ℕ := 2 ^ (68 - decimalShift e)

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
      2 ^ decimalShift e * (2 * f * trimSig e) / 2 ^ 64 := by
  show f * 2 ^ (decimalShift e + 1) * trimSig e / 2 ^ 64 = _
  congr 1
  rw [pow_succ]
  ring

/-- `sigHi` is the top 64 bits of the shifted 192-bit product. -/
theorem sig_hi_eq (f : ℕ) (e : ℤ) :
    sigHi f e = 2 ^ decimalShift e * (2 * f * trimSig e) / 2 ^ 128 := by
  show scaledSignificand f e / 2 ^ 64 = _
  rw [scaled_significand_eq, Nat.div_div_eq_div_mul, ← pow_add]

/-- `sigLo` is bits 64–127 of the shifted 192-bit product. -/
theorem sig_lo_eq (f : ℕ) (e : ℤ) :
    sigLo f e
      = 2 ^ decimalShift e * (2 * f * trimSig e) % 2 ^ 128 / 2 ^ 64 := by
  show scaledSignificand f e % 2 ^ 64 = _
  rw [scaled_significand_eq, ← Nat.mod_mul_right_div_self, ← pow_add]

/-- A power of two splits into the shift and what is left of the window. -/
theorem pow_shift_split (e : ℤ) (n : ℕ) (hn : decimalShift e ≤ n) :
    (2 : ℕ) ^ n = 2 ^ decimalShift e * 2 ^ (n - decimalShift e) := by
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
theorem trim_half_ulp_eq (e : ℤ) (hsh : decimalShift e < 4) :
    trimSig e / 2 ^ 64 / 2 ^ (4 - decimalShift e)
      = trimSig e / trimUnit e := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, trimUnit,
    show 64 + (4 - decimalShift e) = 68 - decimalShift e from by omega]

/-- `c` is the window residue truncated to the window unit. -/
theorem trim_c_eq (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    sigHi f e % 10 * 2 ^ 60 + sigLo f e / 2 ^ 4
      = trimResidue f e / trimUnit e := by
  set h := decimalShift e with hh
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
theorem sig_hi_quotient (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    sigHi f e = 2 * f * trimSig e / 2 ^ (128 - decimalShift e) := by
  rw [sig_hi_eq, pow_shift_split e 128 (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

theorem sig_hi_ten_quotient (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    sigTen f e = 10 * (2 * f * trimSig e / trimModulus e) := by
  rw [sigTen]
  -- Dividing the unit-step quotient by ten is dividing by the coarse step.
  have hdiv : sigHi f e / 10 = 2 * f * trimSig e / trimModulus e := by
    rw [sig_hi_quotient f e hsh, Nat.div_div_eq_div_mul,
      show 2 ^ (128 - decimalShift e) * 10 = trimModulus e from by
        rw [trimModulus]; ring]
  have hmod := Nat.div_add_mod (sigHi f e) 10
  rw [← hdiv]
  omega

/-- The window modulus is a whole number of window units. -/
theorem trim_modulus_eq (e : ℤ) (hsh : decimalShift e < 4) :
    trimModulus e = trimUnit e * (10 * 2 ^ 60) := by
  rw [trimModulus, trimUnit,
    show 128 - decimalShift e = (68 - decimalShift e) + 60 from by omega,
    pow_add]
  ring

/-! ## Trim bounds in exact arithmetic

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

/-- The residue with that same denominator cleared: the share of the gap the
    truncated power of ten accounts for, before its truncation error. `omega`
    reads this and its unfolding as two atoms, so a proof folds it throughout
    and unfolds only where a product has to be distributed. -/
def trimResidueScaled (f : ℕ) (e : ℤ) : ℕ := trimDen e * trimResidue f e

/-- The gap is the scaled residue plus the power-of-ten truncation error. -/
theorem trim_gap_split (f : ℕ) (e : ℤ) :
    trimGap f e
      = trimResidueScaled f e + 2 * f * (trimNum e % trimDen e) := rfl

def trimScale (e : ℤ) : ℕ := trimModulus e * trimDen e

/-- How far a gap can be from the multiple-of-ten candidate and still be
    accepted by a packed comparison: `den·(p10 + U)`. Written as `num / den`
    rather than `trimSig` so the certificate remains purely natural-number
    computation. -/
def trimBnd (e : ℤ) : ℕ := trimDen e * (trimNum e / trimDen e + trimUnit e)

/-- One window unit with the denominator cleared: the resolution of the packed
    comparison and the scale of the narrow windows refuted below. -/
def trimEdge (e : ℤ) : ℕ := trimUnit e * trimDen e

/-- Integer form of `2·p10 + 2 ≤ N`, where `N = trimModulus`. The truncation is
    expressed as natural division so the finite check reduces directly in the
    kernel. -/
def trimNarrowHolds (e : ℤ) : Bool :=
  decide (2 * (trimNum e / trimDen e) + 2 ≤ trimModulus e)

theorem trim_narrow_all :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, trimNarrowHolds e = true := by
  decide +kernel

/-- Integer form of `2^54·(p10Exact - p10) ≤ p10 % U` and of its complement
    `2^54·(p10Exact - p10) ≤ U - p10 % U`, with the denominator cleared. The
    truncation error fits in the bits the packed comparison discards, measured
    from either end of the window unit. -/
def trimWindowMarginsHolds (e : ℤ) : Bool :=
  let num := trimNum e
  let den := trimDen e
  let low := num / den % trimUnit e
  decide (2 ^ 54 * (num % den) ≤ low * den
    ∧ 2 ^ 54 * (num % den) + low * den ≤ trimUnit e * den)

theorem trim_window_margins_all :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, trimWindowMarginsHolds e = true := by
  decide +kernel

/-- The discarded low bits `p10 % U` dominate the power-of-ten truncation error
    `p10Exact - p10 = τ/den`: the margin used when a packed comparison is strict
    on the low side. Which bits of the power of ten survive truncation is not a
    magnitude property, so this is checked per exponent. -/
theorem trim_low_bits (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 54 * (trimNum e % trimDen e)
      ≤ trimSig e % trimUnit e * trimDen e := by
  have hcert := trim_window_margins_all e (by simpa [Finset.mem_Icc] using he)
  simp only [trimWindowMarginsHolds, decide_eq_true_eq] at hcert
  rw [trim_sig_nat]
  exact hcert.1

/-- The complementary distance to the next window unit dominates the same
    truncation error: the margin used when a packed comparison falls short of
    its boundary, which is what the completeness directions need. -/
theorem trim_high_bits (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 ^ 54 * (trimNum e % trimDen e) + trimSig e % trimUnit e * trimDen e
      ≤ trimUnit e * trimDen e := by
  have hcert := trim_window_margins_all e (by simpa [Finset.mem_Icc] using he)
  simp only [trimWindowMarginsHolds, decide_eq_true_eq] at hcert
  rw [trim_sig_nat]
  exact hcert.2

/-! ## Refuting the trim windows

The comparisons that decide those bounds are themselves packed: `roundD0`
compares `W / U` with `p10 / U`, while `roundU0` compares their sum with
`N / U`. They see the exact quantities only up to one window unit `U`;
`dec_ten_down` and `dec_ten_up` translate their outcomes back into exact bounds.

Because truncation is one-sided, the soundness directions are asymmetric: the
plain `roundU0` test is safe whenever it fires, while the one-LSB-offset test
`t1 + 1 = t0` and the trim-down tests may accept one unit early.

Completeness reads the same comparisons in the opposite direction. A test that
does not fire bounds the exact gap from the other side, again with at most one
unit of uncertainty. There the relevant margin is the distance from the
discarded low bits of `p10` to the next window boundary, rather than the low
bits themselves; this is why `trimWindowMarginsHolds` certifies both sides of
the unit.

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

/--
The four windows a violation would have to hit around `num` and `modulus - num`.
The outward windows extend to `bnd`, while the inward windows extend by one
`edge`; soundness uses the outward pair and completeness the inward pair. The
trim quantities are computed once here so the search can retry a window without
recomputing the power of ten.

Those four express what packed truncation leaves undecided, and they stop one
short of `scale - num` on either side, that residue being an exact tie rather
than an ambiguity. The fifth window is that residue alone, and it asks the other
question: whether an exact tie is possible at all. Where the power-of-ten
approximation is exact it is possible only at `k = 0`, which `roundU0` has a
branch for, so certifying the residue empty elsewhere is what lets
`trim_scale_lt` rule out the rest. Both halves of the condition are needed:
with an inexact power-of-ten approximation the residue is reachable, at 73
exponents, by significands whose packed comparison is no tie, and
`trim_tie_gap_eq` disposes of those instead.
-/
private def trimWindows (e : ℤ) : ModWindows where
  g := 2 * trimNum e
  modulus := trimScale e
  f0 := 1
  f1 := 2 ^ 53 - 1
  windows :=
    let num : ℤ := trimNum e
    let bnd : ℤ := trimBnd e
    let edge : ℤ := trimEdge e
    let scale : ℤ := trimScale e
    [(num + 1, bnd - 1), (num - edge + 1, num - 1),
      (scale - bnd, scale - num - 1),
      (scale - num + 1, scale - num + edge - 1)]
      ++ if trimNum e % trimDen e = 0 ∧ decimalExponent e ≠ 0 then
        [(scale - num, scale - num)]
      else []

/-- Close `∃ q, (trimWindows e).refutedBy q = true` for a literal exponent. -/
elab "trim_cert" : tactic => modCertTactic fun e => (trimWindows e).search

private theorem trim_windows_refuted (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ∃ q, (trimWindows e).refutedBy q = true := by
  obtain ⟨hlo, hhi⟩ := he
  interval_cases e <;> trim_cert

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

/-- A gap landing in a refuted window is impossible: the gap is the residue of
    `2·num·f` modulo the window modulus, as long as it has not wrapped. -/
private theorem trim_no_window_hit {lo hi q : ℤ} (f : ℕ) (e : ℤ)
    (hr : Regular f e)
    (hcert : (trimWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (trimWindows e).windows)
    (hwrap : trimGap f e < trimScale e)
    (hlo : lo ≤ (trimGap f e : ℤ))
    (hhi : (trimGap f e : ℤ) ≤ hi) :
    False := by
  obtain ⟨⟨hf_pos, hf_hi, -⟩, -⟩ := hr
  refine (trimWindows e).not_hit f ?_ hcert hmem ?_ ?_ ?_ hlo hhi <;>
    simp only [trimWindows]
  · rw [trimScale, trimModulus]
    exact Nat.mul_pos (by positivity) (trim_den_pos e)
  · omega
  · omega
  · exact (trim_gap_mod f e hwrap).symm

/-- `p10 + U` is far below the window modulus, so a gap bounded by
    `den·(p10 + U)` has not wrapped. -/
theorem trim_bnd_le_scale (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    trimBnd e ≤ trimScale e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e he
  rw [trimBnd, ← trim_sig_nat]
  have hu_le : trimUnit e ≤ 2 ^ 68 := by
    rw [trimUnit]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn_ge : 10 * 2 ^ 125 ≤ trimModulus e := by
    rw [trimModulus]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hp_lt : trimSig e < 2 ^ 128 := (trim_sig_bounds e he).2
  have hgap : (2 : ℕ) ^ 128 + 2 ^ 68 ≤ 10 * 2 ^ 125 := by norm_num
  have hwindow : trimSig e + trimUnit e ≤ trimModulus e := by omega
  rw [trimScale, Nat.mul_comm (trimModulus e)]
  exact Nat.mul_le_mul_left _ hwindow

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

/-! ## From packed comparisons to trim bounds

Truncating to blocks of `U` is what the packed comparisons do, so each trim
bound has to turn a comparison of block counts back into one of the untruncated
values. The first two facts below do that, non-strictly and strictly, since the
discarded low bits are worth less than one block; the third says that truncating
a sum never overshoots it. All three are stated for a generic block size `u` and
always instantiated with `U`.
-/

theorem add_mod_lt_of_div_le {a b u : ℕ} (hu : 0 < u)
    (hle : a / u ≤ b / u) : a + b % u < b + u := by
  have ha := Nat.div_add_mod a u
  have hb := Nat.div_add_mod b u
  have hmod : a % u < u := Nat.mod_lt _ hu
  have hscaled : u * (a / u) ≤ u * (b / u) := Nat.mul_le_mul_left _ hle
  omega

theorem add_mod_succ_le_of_div_lt {a b u : ℕ} (hu : 0 < u)
    (hlt : a / u < b / u) : a + b % u + 1 ≤ b := by
  have ha := Nat.div_add_mod a u
  have hb := Nat.div_add_mod b u
  have hmod : a % u < u := Nat.mod_lt _ hu
  have hscaled : u * (a / u) + u ≤ u * (b / u) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

theorem mul_div_add_div_le (a b u : ℕ) :
    u * (a / u + b / u) ≤ a + b := by
  have ha := Nat.div_add_mod a u
  have hb := Nat.div_add_mod b u
  calc
    u * (a / u + b / u) = u * (a / u) + u * (b / u) := by ring
    _ ≤ a + b := by omega

theorem trim_unit_pos (e : ℤ) : 0 < trimUnit e := by
  rw [trimUnit]; positivity

/-- `den·p10 + τ = num`: the truncated power of ten and the bits it dropped. -/
theorem trim_num_split (e : ℤ) :
    trimDen e * trimSig e + trimNum e % trimDen e = trimNum e := by
  rw [trim_sig_nat]; exact Nat.div_add_mod _ _

theorem trim_scale_split (e : ℤ) :
    trimDen e * trimModulus e = trimScale e := by
  rw [trimScale]; ring

/-- One ULP of the value is narrower than one step of the coarse decimal grid:
    `2·num < scale`. This depends on the low bits of the truncated power of ten,
    not just its magnitude, so it is checked separately for each exponent. -/
theorem trim_two_num_lt_scale (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    2 * trimNum e < trimScale e := by
  have hcert := trim_narrow_all e (by simpa [Finset.mem_Icc] using he)
  simp only [trimNarrowHolds, decide_eq_true_eq] at hcert
  rw [← trim_sig_nat] at hcert
  have hstep : trimDen e * (2 * trimSig e + 2) ≤ trimDen e * trimModulus e :=
    Nat.mul_le_mul_left _ hcert
  have hexp : trimDen e * (2 * trimSig e + 2)
      = 2 * (trimDen e * trimSig e) + 2 * trimDen e := by ring
  have hsplit := trim_num_split e
  have hscale := trim_scale_split e
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

/-- The bridge every trim bound crosses: the gap is `den` times the residue plus
    the truncation error `2·f·τ`, and `trim_low_bits` keeps that error inside
    the low bits of `p10` that the packed comparison discards anyway. -/
theorem trim_gap_sandwich (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimResidueScaled f e ≤ trimGap f e ∧
      trimGap f e ≤ trimResidueScaled f e
        + trimSig e % trimUnit e * trimDen e := by
  rw [trim_gap_split]
  have htrunc : 2 * f * (trimNum e % trimDen e)
      ≤ trimSig e % trimUnit e * trimDen e := by
    calc
      2 * f * (trimNum e % trimDen e)
          ≤ 2 ^ 54 * (trimNum e % trimDen e) :=
        Nat.mul_le_mul_right _ (by have := hr.sig_lt; omega)
      _ ≤ trimSig e % trimUnit e * trimDen e := trim_low_bits e hr.range
  omega

/-- What the packed comparisons say about the untruncated values: a packed sum
    of at least `m` window units is worth at least `U·m`. -/
theorem trim_pack (f : ℕ) (e : ℤ) (m : ℕ)
    (hb : m ≤ trimResidue f e / trimUnit e + trimSig e / trimUnit e) :
    trimUnit e * m ≤ trimResidue f e + trimSig e :=
  le_trans (Nat.mul_le_mul_left _ hb) (mul_div_add_div_le _ _ _)

/-- Under the trim-down comparison the gap stays within `den·(p10 + U)`: the low
    bits of `p10` cover the truncation error, and the comparison leaves at most
    one window unit of slack. -/
theorem trim_gap_box (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimResidue f e / trimUnit e ≤ trimSig e / trimUnit e) :
    trimGap f e < trimBnd e := by
  rw [trimBnd, ← trim_sig_nat]
  have hslack := add_mod_lt_of_div_le (trim_unit_pos e) hcmp
  have hscaled : trimResidueScaled f e + trimSig e % trimUnit e * trimDen e
      < trimDen e * (trimSig e + trimUnit e) := by
    rw [trimResidueScaled, mul_comm (trimSig e % trimUnit e), ← mul_add]
    exact mul_lt_mul_of_pos_left hslack (trim_den_pos e)
  exact lt_of_le_of_lt (trim_gap_sandwich f e hr).2 hscaled

/-- The four truncation windows the certificates refute, named by the boundary
    they hug and the side they hug it from. Soundness uses the outward pair,
    completeness the inward pair. -/
structure TrimGapSeparated (f : ℕ) (e : ℤ) : Prop where
  aboveNum : ¬(trimNum e < trimGap f e ∧ trimGap f e < trimBnd e)
  belowNum : ¬(trimNum e < trimGap f e + trimEdge e ∧ trimGap f e < trimNum e)
  belowScale : ¬(trimScale e ≤ trimGap f e + trimBnd e ∧
    trimGap f e + trimNum e < trimScale e)
  aboveScale : ¬(trimScale e < trimGap f e + trimNum e ∧
    trimGap f e + trimNum e < trimScale e + trimEdge e)

/-- The certificates' semantic content: the gap never lands in those windows,
    each of them narrower than one window edge. Below this theorem is modular
    arithmetic of `2·num·f mod scale`; above it the certificates are hidden
    behind these four separation facts. -/
theorem trim_gap_separated (f : ℕ) (e : ℤ) (hr : Regular f e) :
    TrimGapSeparated f e := by
  obtain ⟨q, hcert⟩ := trim_windows_refuted e hr.range
  have hbnd := trim_bnd_le_scale e hr.range
  have hedge := trim_two_edge_lt_num e hr.range
  have hnarrow := trim_two_num_lt_scale e hr.range
  -- The four truncation windows, in the order `trimWindows` lists them.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨hlo, hhi⟩
  · exact trim_no_window_hit f e hr hcert (.head _)
      (by omega) (by omega) (by omega)
  · exact trim_no_window_hit f e hr hcert (.tail _ (.head _))
      (by omega) (by omega) (by omega)
  · exact trim_no_window_hit f e hr hcert (.tail _ (.tail _ (.head _)))
      (by omega) (by omega) (by omega)
  · exact trim_no_window_hit f e hr hcert
      (.tail _ (.tail _ (.tail _ (.head _))))
      (by omega) (by omega) (by omega)

/-- Trim-down soundness: if the packed comparison reads `c ≤ halfUlp`, then the
    exact gap is at most `num`; otherwise it would lie in a forbidden window. -/
theorem trim_gap_le (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimResidue f e / trimUnit e ≤ trimSig e / trimUnit e) :
    trimGap f e ≤ trimNum e := by
  by_contra! hcon
  exact (trim_gap_separated f e hr).aboveNum ⟨hcon, trim_gap_box f e hr hcmp⟩

/-- The strict version needs no certificate: one full window unit of slack
    already exceeds the truncation error of the power of ten. -/
theorem trim_gap_lt (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimResidue f e / trimUnit e < trimSig e / trimUnit e) :
    trimGap f e < trimNum e := by
  -- A whole window unit of slack, scaled by `den`, outweighs the low bits.
  have hscaled : trimResidueScaled f e
      + trimSig e % trimUnit e * trimDen e < trimDen e * trimSig e := by
    have hslack := add_mod_succ_le_of_div_lt (trim_unit_pos e) hcmp
    rw [trimResidueScaled]
    rw [mul_comm (trimSig e % trimUnit e), ← mul_add]
    exact mul_lt_mul_of_pos_left (by omega) (trim_den_pos e)
  have hnum : trimDen e * trimSig e + trimNum e % trimDen e = trimNum e :=
    trim_num_split e
  have hsand := (trim_gap_sandwich f e hr).2
  omega

/-- Trim-down completeness: if the packed comparison reads `halfUlp < c`, then
    the residue lies strictly above `p10`. After clearing the denominator that
    single unit becomes a whole `den`, which exceeds the truncation remainder,
    so `num < gap` without using a certificate. -/
theorem trim_num_lt_gap (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimSig e / trimUnit e < trimResidue f e / trimUnit e) :
    trimNum e < trimGap f e := by
  have hslack := add_mod_succ_le_of_div_lt (trim_unit_pos e) hcmp
  have hscaled : trimDen e * (trimSig e + 1) ≤ trimResidueScaled f e :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp : trimDen e * (trimSig e + 1)
      = trimDen e * trimSig e + trimDen e := by ring
  have hnum := trim_num_split e
  have hmod : trimNum e % trimDen e < trimDen e := Nat.mod_lt _ (trim_den_pos e)
  have hsand := (trim_gap_sandwich f e hr).1
  omega

/-- Trim-down completeness, tie case: if the packed comparison has not read
    `c < halfUlp`, then `num` is less than one window edge above `gap`.
    Therefore a gap below `num` would lie in the forbidden inward window. -/
theorem trim_num_le_gap (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimSig e / trimUnit e ≤ trimResidue f e / trimUnit e) :
    trimNum e ≤ trimGap f e := by
  by_contra! hcon
  have hslack := add_mod_lt_of_div_le (trim_unit_pos e) hcmp
  have hscaled : trimDen e * (trimSig e + trimResidue f e % trimUnit e + 1)
      ≤ trimDen e * (trimResidue f e + trimUnit e) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp1 : trimDen e * (trimSig e + trimResidue f e % trimUnit e + 1)
      = trimDen e * trimSig e + trimDen e * (trimResidue f e % trimUnit e)
        + trimDen e := by ring
  have hexp2 : trimDen e * (trimResidue f e + trimUnit e)
      = trimResidueScaled f e + trimEdge e := by
    rw [trimResidueScaled, trimEdge]; ring
  have hnum := trim_num_split e
  have hmod : trimNum e % trimDen e < trimDen e := Nat.mod_lt _ (trim_den_pos e)
  have hsand := (trim_gap_sandwich f e hr).1
  have hnear : trimNum e < trimGap f e + trimEdge e := by omega
  exact (trim_gap_separated f e hr).belowNum ⟨hnear, hcon⟩

/-- Trim-up soundness: if the packed sum is within one unit of the modulus,
    `gap + num` reaches the modulus after clearing the denominator. -/
theorem trim_scale_le (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimModulus e ≤ trimResidue f e + trimSig e + trimUnit e) :
    trimScale e ≤ trimGap f e + trimNum e := by
  by_contra! hcon
  -- The comparison keeps the gap within the window edge of the modulus.
  have hfar : trimScale e ≤ trimGap f e + trimBnd e := by
    rw [trimBnd, ← trim_sig_nat]
    have hscaled : trimScale e
        ≤ trimResidueScaled f e + trimDen e * (trimSig e + trimUnit e) := by
      rw [trimResidueScaled, ← trim_scale_split e, ← mul_add, ← Nat.add_assoc]
      exact Nat.mul_le_mul_left _ hcmp
    have hsand := (trim_gap_sandwich f e hr).1
    omega
  exact (trim_gap_separated f e hr).belowScale ⟨hfar, hcon⟩

/-- Equality in the packed comparison scales to `gap + num = scale + (2f+1)·τ`:
    the truncation remainder is exactly the slack in the corresponding exact
    bound. -/
theorem trim_tie_gap_eq (f : ℕ) (e : ℤ)
    (htie : trimModulus e = trimResidue f e + trimSig e) :
    trimGap f e + trimNum e
      = trimScale e + (2 * f + 1) * (trimNum e % trimDen e) := by
  let τ := trimNum e % trimDen e
  have hnum : trimNum e = trimDen e * trimSig e + τ := by
    simpa [τ] using (trim_num_split e).symm
  change trimResidueScaled f e + 2 * f * τ + trimNum e =
    trimModulus e * trimDen e + (2 * f + 1) * τ
  rw [trimResidueScaled, hnum, htie]
  ring

/-- An exact power-of-ten approximation admits a tie only at `k = 0`. An exact
    tie leaves the gap at `scale - num`, and that is the residue the fifth
    window refutes wherever the approximation is exact and `k` is not zero. -/
theorem trim_exact_tie_k_zero (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hτ : trimNum e % trimDen e = 0)
    (htie : trimModulus e = trimResidue f e + trimSig e) :
    decimalExponent e = 0 := by
  by_contra hk
  obtain ⟨q, hcert⟩ := trim_windows_refuted e hr.range
  -- With no truncation remainder the packed tie is an exact one.
  have hgap : trimGap f e + trimNum e = trimScale e := by
    rw [trim_tie_gap_eq f e htie, hτ]
    simp
  have hpos : 0 < trimNum e :=
    lt_of_lt_of_le (Nat.mul_pos (by positivity) (trim_den_pos e))
      (trim_num_lower e hr.range)
  -- The fifth window is present exactly under these two hypotheses.
  have hmem : ((trimScale e : ℤ) - trimNum e, (trimScale e : ℤ) - trimNum e)
      ∈ (trimWindows e).windows := by
    refine List.mem_append_right _ ?_
    rw [ite_eq_left ⟨hτ, hk⟩]
    exact List.mem_singleton_self _
  exact trim_no_window_hit f e hr hcert hmem (by omega) (by omega) (by omega)

/-- At `k = 0` the power-of-ten significand is exactly `2^127`, so it has no
    low bits for the truncation to drop. -/
theorem trim_power_of_k_zero (e : ℤ) (hk : decimalExponent e = 0) :
    trimNum e = 2 ^ 127 * trimDen e ∧ trimSig e = 2 ^ 127 := by
  have heq : trimNum e = 2 ^ 127 * trimDen e := by
    rw [trimNum, trimDen, hk]
    decide
  exact ⟨heq, by rw [trim_sig_nat, heq, Nat.mul_div_cancel _ (trim_den_pos e)]⟩

/-- At `k = 0` the packed comparison is exact: both operands are whole window
    units and the power-of-ten truncation error vanishes. Thus the packed tie
    lifts to an exact tie, with `gap + num = scale`. -/
theorem trim_gap_num_eq_scale_of_k_zero (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hk : decimalExponent e = 0)
    (htie : trimResidue f e / trimUnit e + trimSig e / trimUnit e
      = 10 * 2 ^ 60) :
    trimGap f e + trimNum e = trimScale e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e hr.range
  obtain ⟨hnum, hsig⟩ := trim_power_of_k_zero e hk
  have hunit : trimUnit e ∣ trimSig e := by
    rw [hsig, trimUnit]
    exact pow_dvd_pow 2 (by omega)
  have hres : trimUnit e ∣ trimResidue f e := by
    refine (Nat.dvd_mod_iff ?_).mpr (hunit.mul_left _)
    rw [trimModulus, trimUnit]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) 10
  -- Whole units on both sides, so the packed tie is a tie of the operands.
  have hsum : trimResidue f e + trimSig e = trimModulus e := by
    rw [← Nat.mul_div_cancel' hres, ← Nat.mul_div_cancel' hunit, ← Nat.mul_add,
      htie]
    exact (trim_modulus_eq e hsh).symm
  have hgap : trimGap f e = trimResidueScaled f e := by
    rw [trim_gap_split, hnum, Nat.mul_mod_left, Nat.mul_zero, Nat.add_zero]
  have hscaled_sum : trimDen e * (trimResidue f e + trimSig e)
      = trimResidueScaled f e + trimNum e := by
    rw [trimResidueScaled, hnum, hsig]; ring
  rw [hgap, ← trim_scale_split e, ← hsum, hscaled_sum]

/-- Strict trim-up soundness for the final `t0 ≤ t1` test. Packed equality is
    either made strict by power-of-ten truncation or is an exact tie, which
    forces `k = 0` and belongs to the dedicated `k = 0 ∧ t1 = t0` branch. -/
theorem trim_scale_lt (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hb : 10 * 2 ^ 60 ≤ trimResidue f e / trimUnit e + trimSig e / trimUnit e)
    (hne : ¬(decimalExponent e = 0 ∧ trimResidue f e / trimUnit e
      + trimSig e / trimUnit e = 10 * 2 ^ 60)) :
    trimScale e < trimGap f e + trimNum e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e hr.range
  have hu_pos := trim_unit_pos e
  have hmodeq : trimModulus e = trimUnit e * (10 * 2 ^ 60) :=
    trim_modulus_eq e hsh
  have hcmp : trimModulus e ≤ trimResidue f e + trimSig e := by
    rw [hmodeq]; exact trim_pack f e _ hb
  rcases lt_or_eq_of_le hcmp with hlt | heq
  · -- Clearing the denominator preserves the strict inequality.
    have hscaled : trimScale e
        < trimResidueScaled f e + trimDen e * trimSig e := by
      rw [trimResidueScaled, ← trim_scale_split e, ← mul_add]
      exact mul_lt_mul_of_pos_left hlt (trim_den_pos e)
    have hnum : trimDen e * trimSig e + trimNum e % trimDen e = trimNum e :=
      trim_num_split e
    have hsand := (trim_gap_sandwich f e hr).1
    omega
  -- Equality in the packed comparison is a genuine tie only when the
  -- power-of-ten approximation is exact. Otherwise its truncation remainder is
  -- precisely the slack that makes the exact bound strict.
  · by_cases hτ : trimNum e % trimDen e = 0
    · -- A tie in exact arithmetic, which only `k = 0` admits.
      exfalso
      refine hne ⟨trim_exact_tie_k_zero f e hr hτ heq, ?_⟩
      -- An exact tie is seen as one by the packed comparison too.
      have h4 : trimUnit e
          * (trimResidue f e / trimUnit e + trimSig e / trimUnit e)
          ≤ trimUnit e * (10 * 2 ^ 60) := by
        rw [← hmodeq, heq]; exact mul_div_add_div_le _ _ _
      exact Nat.le_antisymm (Nat.le_of_mul_le_mul_left h4 hu_pos) hb
    · rw [trim_tie_gap_eq f e heq]
      exact Nat.lt_add_of_pos_right
        (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hτ))

/-- Each packed unit of room below the modulus becomes one `trimEdge` after
    clearing the denominator. Reconstructing `gap + num` adds `(2f+1)·τ`, where
    `τ` is the power-of-ten truncation remainder; `trim_high_bits` shows that
    this error together with the discarded low bits of `p10` fits within one
    `trimEdge`. -/
theorem trim_packed_room (f : ℕ) (e : ℤ) (hr : Regular f e) (n : ℕ)
    (hcmp : trimResidue f e / trimUnit e + trimSig e / trimUnit e + n
      ≤ 10 * 2 ^ 60) :
    trimGap f e + trimNum e + n * trimEdge e
      ≤ trimScale e + trimResidue f e % trimUnit e * trimDen e
        + trimEdge e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e hr.range
  -- Scaled back up, the packed sum leaves `n` whole window units of room.
  have hroom : trimResidue f e + trimSig e + n * trimUnit e
      ≤ trimModulus e + trimResidue f e % trimUnit e
        + trimSig e % trimUnit e := by
    have hscaled : trimUnit e * (trimResidue f e / trimUnit e
        + trimSig e / trimUnit e + n) ≤ trimUnit e * (10 * 2 ^ 60) :=
      Nat.mul_le_mul_left _ hcmp
    have hexp : trimUnit e * (trimResidue f e / trimUnit e
          + trimSig e / trimUnit e + n)
        = trimUnit e * (trimResidue f e / trimUnit e)
          + trimUnit e * (trimSig e / trimUnit e) + n * trimUnit e := by ring
    have hw := Nat.div_add_mod (trimResidue f e) (trimUnit e)
    have hp := Nat.div_add_mod (trimSig e) (trimUnit e)
    have hmod := trim_modulus_eq e hsh
    omega
  -- Clearing the denominator turns each unit of that room into one `trimEdge`.
  have hscaled : trimResidueScaled f e + trimDen e * trimSig e + n * trimEdge e
      ≤ trimScale e + trimResidue f e % trimUnit e * trimDen e
        + trimSig e % trimUnit e * trimDen e := by
    have hs := Nat.mul_le_mul_left (trimDen e) hroom
    have hexp1 : trimDen e * (trimResidue f e + trimSig e + n * trimUnit e)
        = trimResidueScaled f e + trimDen e * trimSig e
          + n * trimEdge e := by
      rw [trimResidueScaled, trimEdge]; ring
    have hexp2 : trimDen e * (trimModulus e + trimResidue f e % trimUnit e
          + trimSig e % trimUnit e)
        = trimScale e + trimResidue f e % trimUnit e * trimDen e
          + trimSig e % trimUnit e * trimDen e := by
      rw [← trim_scale_split e]; ring
    rwa [hexp1, hexp2] at hs
  -- Reconstructing `gap + num` from those products adds `(2f+1)·τ`.
  have hsum : trimGap f e + trimNum e
      = trimResidueScaled f e + trimDen e * trimSig e
        + (2 * f + 1) * (trimNum e % trimDen e) :=
    calc trimGap f e + trimNum e
        = trimResidueScaled f e + 2 * f * (trimNum e % trimDen e)
            + (trimDen e * trimSig e + trimNum e % trimDen e) := by
          rw [trim_gap_split, trim_num_split e]
      _ = trimResidueScaled f e + trimDen e * trimSig e
            + (2 * f + 1) * (trimNum e % trimDen e) := by ring
  have htau : (2 * f + 1) * (trimNum e % trimDen e)
      ≤ 2 ^ 54 * (trimNum e % trimDen e) :=
    Nat.mul_le_mul_right _ (by have := hr.sig_lt; omega)
  have hhigh : 2 ^ 54 * (trimNum e % trimDen e)
      + trimSig e % trimUnit e * trimDen e ≤ trimEdge e := by
    rw [trimEdge]; exact trim_high_bits e hr.range
  omega

/-- The low bits of the residue are worth less than one window unit. -/
theorem trim_residue_low_lt_edge (f : ℕ) (e : ℤ) :
    trimResidue f e % trimUnit e * trimDen e < trimEdge e := by
  rw [trimEdge]
  exact mul_lt_mul_of_pos_right (Nat.mod_lt _ (trim_unit_pos e))
    (trim_den_pos e)

/-- Trim-up completeness: if the packed sum is two window units short of the
    modulus, one unit absorbs the discarded low bits and one remains, so
    `gap + num` is strictly below `scale`. No certificate is needed. -/
theorem trim_gap_num_lt_scale (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimResidue f e / trimUnit e + trimSig e / trimUnit e + 2
      ≤ 10 * 2 ^ 60) :
    trimGap f e + trimNum e < trimScale e := by
  have hroom := trim_packed_room f e hr 2 hcmp
  have hedge := trim_residue_low_lt_edge f e
  omega

/-- Trim-up completeness, tie case: if the packed sum is one window unit short
    of the modulus, `gap + num` cannot exceed `scale`. The truncated comparison
    only bounds any excess to less than one window edge, and that inward window
    is excluded by the certificate. -/
theorem trim_gap_num_le_scale (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hcmp : trimResidue f e / trimUnit e + trimSig e / trimUnit e + 1
      = 10 * 2 ^ 60) :
    trimGap f e + trimNum e ≤ trimScale e := by
  by_contra! hcon
  have hroom := trim_packed_room f e hr 1 (by omega)
  have hedge := trim_residue_low_lt_edge f e
  exact (trim_gap_separated f e hr).aboveScale ⟨hcon, by omega⟩

/-- The free side of the trim-up bound: the gap can overshoot the coarse step,
    but by less than `num`, since the residue stays below the step and
    `num ≥ 2^127·den` absorbs the truncation error. -/
theorem trim_gap_lt_scale_add (f : ℕ) (e : ℤ) (hr : Regular f e) :
    trimGap f e < trimScale e + trimNum e := by
  have hres : trimResidueScaled f e < trimScale e := by
    rw [trimResidueScaled, trimResidue, stepResidue, trimScale,
      Nat.mul_comm (trimModulus e)]
    exact mul_lt_mul_of_pos_left
      (Nat.mod_lt _ (by rw [trimModulus]; positivity)) (trim_den_pos e)
  have hlow := trim_trunc_lt f e hr
  have htrunc : 2 ^ 54 * trimDen e ≤ trimNum e :=
    le_trans
      (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
      (trim_num_lower e hr.range)
  rw [trim_gap_split]
  omega

/-! ## From integer bounds to half-ULP bounds

In the scale `trimMul` the two multiple-of-ten candidates have scaled errors
`-trimGap` and `trimScale - trimGap`, and half a scaled ULP is exactly
`trimNum`. The power of ten enters only through `trim_mul_eq`, which expresses
`trimMul` as `trimNum` times the inverse scale `s = 2^(1-e)·10^k`. Thus each
candidate bound `|cand - x| ≤ u/2` is a comparison of `trimGap` with `trimNum`.
-/

/-- The unit step, cleared. The coarse step is ten of them. -/
def trimMul (e : ℤ) : ℕ := 2 ^ (128 - decimalShift e) * trimDen e

/-- The candidate scale factor is positive. -/
theorem trim_mul_pos (e : ℤ) : (0 : ℚ) < (trimMul e : ℚ) :=
  Nat.cast_pos.mpr
    (by rw [trimMul]; exact Nat.mul_pos (by positivity) (trim_den_pos e))

theorem trim_scale_eq_ten_mul (e : ℤ) : trimScale e = 10 * trimMul e := by
  simp only [trimScale, trimMul, trimModulus]
  ring

/-- Twice the bound on the power-of-ten truncation error fits inside one grid
    step: `trimMul ≥ 2^125·den`, while the doubled bound is `2^55·den`. -/
theorem trim_two_trunc_le_mul (e : ℤ) (hsh : decimalShift e < 4) :
    2 ^ 55 * trimDen e ≤ trimMul e := by
  rw [trimMul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Half a grid step, cleared: half a unit step times `den`. -/
theorem trim_mul_eq_two_half (e : ℤ) (hsh : decimalShift e < 4) :
    trimMul e = 2 * (trimDen e * 2 ^ (127 - decimalShift e)) := by
  rw [trimMul, show (2 : ℕ) ^ (128 - decimalShift e)
      = 2 * 2 ^ (127 - decimalShift e) from by
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
      = 2 ^ (128 - decimalShift e) := by
    have h10 : (10 : ℚ) ^ (-k) * 10 ^ k = 1 := by
      rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp
    have halign : (decimalShift e : ℤ) + 1 - pe = e := decimal_shift_align e he
    have hsh : decimalShift e < 4 := decimal_shift_lt_four e he
    calc (10 : ℚ) ^ (-k) * 2 ^ (128 - pe) * (2 ^ (1 - e) * 10 ^ k)
        = (10 ^ (-k) * 10 ^ k) * (2 ^ (128 - pe) * 2 ^ (1 - e)) := by
          ring
      _ = (2 : ℚ) ^ ((128 - pe) + (1 - e)) := by
          rw [h10, one_mul, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = 2 ^ (128 - decimalShift e) := by
          rw [show (128 - pe) + (1 - e) = ((128 - decimalShift e : ℕ) : ℤ)
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

/-- Both candidates reach ℚ the same way: in the scale `trimMul`, a candidate
    accounting for the whole product except its gap sits exactly that gap below
    the scaled value. -/
theorem scaled_error_of_nat {cand gap : ℕ} (f : ℕ) (e : ℤ)
    (he : -1074 ≤ e ∧ e ≤ 971)
    (hnat : cand * trimMul e + gap = 2 * f * trimNum e) :
    ((cand : ℚ) - value f e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = -(gap : ℚ) := by
  have hcast : (cand : ℚ) * trimMul e + gap = 2 * f * trimNum e := by
    exact_mod_cast hnat
  -- The same scale sends the scaled value to `2·f·num`.
  have hvalue : value f e * 10 ^ (-decimalExponent e) * (trimMul e : ℚ)
      = 2 * f * (trimNum e : ℚ) := by
    rw [← trim_mul_half_ulp e he, value, ulp]
    ring
  linear_combination hcast - hvalue

/-- The trim-down candidate sits exactly `trimGap` below the scaled value: it is
    the quotient at the coarse step, which is ten unit steps. -/
theorem dec_ten_down_scaled_error (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ((sigTen f e : ℚ)
        - value f e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = -(trimGap f e : ℚ) :=
  scaled_error_of_nat f e he <| by
    calc sigTen f e * trimMul e + trimGap f e
        = 2 * f * trimSig e / trimModulus e * trimScale e + trimGap f e := by
          rw [sig_hi_ten_quotient f e (decimal_shift_lt_four e he),
            trim_scale_eq_ten_mul]
          ring
      _ = 2 * f * trimNum e := step_quotient_add_gap _ f e

/-- The trim-up candidate sits `trimScale - trimGap` above the scaled value,
    since the scale sends a decimal step of `10` to the window modulus. -/
theorem dec_ten_up_scaled_error (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ((sigTen f e : ℚ) + 10
        - value f e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = (trimScale e : ℚ) - (trimGap f e : ℚ) := by
  have hten : (10 : ℚ) * (trimMul e : ℚ) = (trimScale e : ℚ) := by
    exact_mod_cast (trim_scale_eq_ten_mul e).symm
  linear_combination dec_ten_down_scaled_error f e he + hten

/-- Scaling by `trimMul` loses nothing: a candidate with scaled error `dist` is
    within half a ULP exactly when `|dist|` is at most `trimNum`. -/
theorem half_ulp_iff_scaled_error {cand dist : ℚ} (f : ℕ) (e : ℤ)
    (he : -1074 ≤ e ∧ e ≤ 971)
    (hscale : (cand - value f e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = dist) :
    let k := decimalExponent e
    let x := value f e * 10 ^ (-k)
    let u := ulp e * 10 ^ (-k)
    (|cand - x| ≤ u / 2 ↔ |dist| ≤ (trimNum e : ℚ)) ∧
      (|cand - x| < u / 2 ↔ |dist| < (trimNum e : ℚ)) := by
  intro k x u
  have hpos := trim_mul_pos e
  have hdist : |cand - x| * (trimMul e : ℚ) = |dist| := by
    rw [← hscale, abs_mul, abs_of_pos hpos]
  exact ⟨by rw [← mul_le_mul_iff_of_pos_right hpos, hdist,
      trim_mul_half_ulp e he],
    by rw [← mul_lt_mul_iff_of_pos_right hpos, hdist, trim_mul_half_ulp e he]⟩

/-- The same for half a grid step: the scale sends one step of the grid at `k`
    to one `trimMul`, so a candidate with scaled error `dist` is within half a
    step exactly when `2·|dist|` is at most `trimMul`, and sits at a midpoint
    exactly when they are equal. -/
theorem half_step_iff_scaled_error {cand dist : ℚ} (f : ℕ) (e : ℤ)
    (hscale : (cand - value f e * 10 ^ (-decimalExponent e)) * (trimMul e : ℚ)
      = dist) :
    let x := value f e * 10 ^ (-decimalExponent e)
    (|cand - x| ≤ 1 / 2 ↔ 2 * |dist| ≤ (trimMul e : ℚ)) ∧
      (|cand - x| = 1 / 2 ↔ 2 * |dist| = (trimMul e : ℚ)) := by
  intro x
  have hpos := trim_mul_pos e
  have hval : |cand - x| = |dist| / (trimMul e : ℚ) := by
    rw [← hscale, abs_mul, abs_of_pos hpos, mul_div_assoc,
      div_self (ne_of_gt hpos), mul_one]
  rw [hval]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hpos]
    constructor <;> intro hq <;> linarith
  · rw [div_eq_iff (ne_of_gt hpos)]
    constructor <;> intro hq <;> linarith

/-- One ULP spans `[1, 10)` grid steps at yy's exponent. One grid step is
    `2^(128-h)·den` while half a ULP is `num ≥ 2^127·den`, which gives the first
    bound; the second is the narrowness certificate of the packed comparison. -/
theorem ulp_scaled_bounds (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    1 ≤ ulp e * 10 ^ (-decimalExponent e) ∧
      ulp e * 10 ^ (-decimalExponent e) < 10 := by
  have hsh := decimal_shift_lt_four e he
  have hpos := trim_mul_pos e
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

/-! ## The unit-step candidate

`decOne` is `sigHi` rounded to nearest using the discarded word `sigLo`. In
the scale `trimMul = 2^(128-h)·den`, `sigHi` sits `oneGap` below the scaled
value and rounding up adds one whole `trimMul`. The `roundU1` test bounds the
remainder relative to half a unit step, with only the bits below `sigLo` unseen.

`decOne` is never asked to round-trip directly: it is emitted only when nothing
coarser round-trips, and then the exact method's fine case derives the
round-trip from the half-step bound, the grid at `decimalExponent e` being no
coarser than one ULP. So the only obligation here is that bound, which is a
comparison of `2·oneGap` with `trimMul`.
-/

/-- The residue at the unit step: `sigHi·2^(128-h) + oneResidue` is the
    product `2·f·p10`. -/
def oneResidue (f : ℕ) (e : ℤ) : ℕ :=
  stepResidue (2 ^ (128 - decimalShift e)) f e

/-- The gap at the unit step, the distance from `sigHi` to the scaled value once
    the denominator is cleared. -/
def oneGap (f : ℕ) (e : ℤ) : ℕ := stepGap (2 ^ (128 - decimalShift e)) f e

/-- `sigHi` scaled up, plus the gap, is the scaled value `2·f·num`. -/
theorem sig_hi_add_one_gap (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    sigHi f e * trimMul e + oneGap f e = 2 * f * trimNum e := by
  rw [sig_hi_quotient f e hsh]
  exact step_quotient_add_gap _ f e

/-- `sigLo` is the unit-step remainder with its low `64 - h` bits discarded, so
    the packed test sees the remainder only in units of `2^(64-h)`. -/
theorem sig_lo_eq_residue_div (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    sigLo f e = oneResidue f e / 2 ^ (64 - decimalShift e) := by
  rw [sig_lo_eq, oneResidue, stepResidue, pow_shift_split e 128 (by omega),
    Nat.mul_mod_mul_left, pow_shift_split e 64 (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- What `roundU1` says about the remainder: yy compares the discarded word with
    half its range, so the test is on the remainder against half a unit step,
    `2^(127-h)`, blind only to the `2^(64-h)` bits below `sigLo`. -/
theorem one_round_half (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    ((toDecimalCandidates f e).roundU1 = true →
        2 ^ (127 - decimalShift e) ≤ oneResidue f e) ∧
      ((toDecimalCandidates f e).roundU1 = false →
        oneResidue f e
          < 2 ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e)) := by
  have hpos : (0 : ℕ) < 2 ^ (64 - decimalShift e) := by positivity
  have hlo := sig_lo_eq_residue_div f e hsh
  have hpow : (2 : ℕ) ^ 63 * 2 ^ (64 - decimalShift e)
      = 2 ^ (127 - decimalShift e) := by
    rw [← pow_add]
    congr 1
    omega
  have hround : (toDecimalCandidates f e).roundU1
      = if sigLo f e = 2 ^ 63 then decide (sigHi f e % 2 = 1)
        else decide (2 ^ 63 < sigLo f e) := rfl
  constructor
  · intro hu1
    have h63 : 2 ^ 63 ≤ sigLo f e := by
      rw [hround] at hu1
      split at hu1
      · rename_i heq; exact heq.ge
      · exact (of_decide_eq_true hu1).le
    rwa [hlo, Nat.le_div_iff_mul_le hpos, hpow] at h63
  · intro hu1
    have h63 : sigLo f e ≤ 2 ^ 63 := by
      rw [hround] at hu1
      split at hu1
      · rename_i heq; exact heq.le
      · exact not_lt.mp (of_decide_eq_false hu1)
    rw [hlo] at h63
    calc oneResidue f e
        < (2 ^ 63 + 1) * 2 ^ (64 - decimalShift e) :=
          (Nat.div_lt_iff_lt_mul hpos).mp (Nat.lt_succ_of_le h63)
      _ = 2 ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e) := by
          rw [add_mul, one_mul, hpow]

/-- `sigHi` sits exactly `oneGap` below the scaled value. -/
theorem sig_hi_scaled_error (f : ℕ) (e : ℤ) (he : -1074 ≤ e ∧ e ≤ 971) :
    ((sigHi f e : ℚ) - value f e * 10 ^ (-decimalExponent e))
        * (trimMul e : ℚ)
      = -(oneGap f e : ℚ) :=
  scaled_error_of_nat f e he
    (sig_hi_add_one_gap f e (decimal_shift_lt_four e he))

/-! ## Correct rounding at the unit step

On the grid at `decimalExponent e`, one decimal step is one `trimMul`.
`sigHi` lies `oneGap` below the scaled value, so rounding to the nearest grid
point is determined by comparing `2 * oneGap` with `trimMul`; equality is the
exact midpoint case.

Rounding up needs no additional separation: when `roundU1` fires, the packed
remainder has reached half a unit step, hence the exact gap has reached at
least half a step, since power-of-ten truncation only increases it.

Rounding down and exact midpoints are subtler. The packed test sees the
remainder only down to `2^(64-h)`, while the exact gap also contains the
truncation term `2·f·(num % den)`. Thus the packed comparison alone cannot
exclude a gap just past half a step or guarantee that an exact midpoint appears
as a packed midpoint. Those two facts are `OneMidpointSeparated`, and finite
certificates supply them, one window family per exponent.
-/

/-- The unit-step gap is the denominator-cleared remainder plus the
    power-of-ten truncation error. -/
theorem one_gap_split (f : ℕ) (e : ℤ) :
    oneGap f e
      = trimDen e * oneResidue f e + 2 * f * (trimNum e % trimDen e) := by
  rw [oneGap, stepGap, ← oneResidue]

/-- The gap exceeds a whole step only by the power-of-ten truncation error. -/
theorem one_gap_lt_mul_add (f : ℕ) (e : ℤ) (hr : Regular f e) :
    oneGap f e < trimMul e + 2 ^ 54 * trimDen e := by
  have hres : trimDen e * oneResidue f e < trimMul e := by
    rw [trimMul, Nat.mul_comm (2 ^ (128 - decimalShift e)) (trimDen e)]
    exact mul_lt_mul_of_pos_left
      (by rw [oneResidue, stepResidue]; exact Nat.mod_lt _ (by positivity))
      (trim_den_pos e)
  have htrunc := trim_trunc_lt f e hr
  rw [one_gap_split]
  omega

/-- Rounding up means the gap is at least half a step: the packed test saw the
    remainder reach half a unit step, and the truncation error only increases
    it. -/
theorem one_half_step_le_gap (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hu1 : (toDecimalCandidates f e).roundU1 = true) :
    trimMul e ≤ 2 * oneGap f e := by
  have hsh := decimal_shift_lt_four e hr.range
  have hres :=
    Nat.mul_le_mul_left (trimDen e) ((one_round_half f e hsh).1 hu1)
  have hhalf := trim_mul_eq_two_half e hsh
  rw [one_gap_split]
  omega

/-- What the packed `roundU1` test cannot settle by itself. Both facts concern
    where `2·f·num mod trimMul` lies relative to the midpoint `trimMul / 2`.
    Power-of-ten truncation and discarded low bits leave a narrow undecided
    window there, refuted below just as `trimWindows` are. -/
structure OneMidpointSeparated (f : ℕ) (e : ℤ) : Prop where
  -- If `roundU1` does not fire, the exact gap is at most half a step.
  belowHalf :
    (toDecimalCandidates f e).roundU1 = false →
      2 * oneGap f e ≤ trimMul e

  -- An exact midpoint is visible as a packed midpoint too.
  packedMidpoint :
    2 * oneGap f e = trimMul e →
      oneResidue f e = 2 ^ (127 - decimalShift e)

/-! ### Refuting the unit-step windows

Two bands of the remainder are left undecided, both at the midpoint
`2^(127-h)` of the unit step. Just below it the truncation error `2·f·τ` can
carry the exact gap past half a step while yy rounds down; at and just above it
yy reads a packed tie and resolves it by the parity of `sigHi`, which the exact
gap knows nothing about.

An odd `sigHi` rounds up, so the tie band is dangerous only for an even one.
That parity is the next bit of the same product, which the doubled modulus
`2^(129-h)` sees: the residue stays below one unit step exactly when `sigHi` is
even. Both bands are windows there, refuted per exponent as `trimWindows` are.

An exact power-of-ten approximation has no truncation error, so the band below
the midpoint is harmless and the midpoint is a genuine tie, resolved to even.
Those exponents refute the band above the midpoint only.
-/

/-- The residue in the doubled modulus, one bit wider than the unit step. -/
def oneParityResidue (f : ℕ) (e : ℤ) : ℕ :=
  stepResidue (2 ^ (129 - decimalShift e)) f e

/-- That bit, split off: the doubled residue carries one whole unit step above
    the remainder exactly when `sigHi` is odd. -/
theorem one_parity_residue_split (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4) :
    oneParityResidue f e
      = 2 ^ (128 - decimalShift e) * (sigHi f e % 2) + oneResidue f e := by
  have hw : (2 : ℕ) ^ (129 - decimalShift e)
      = 2 ^ (128 - decimalShift e) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hhi : oneParityResidue f e / 2 ^ (128 - decimalShift e)
      = sigHi f e % 2 := by
    rw [oneParityResidue, stepResidue, hw, Nat.mod_mul_right_div_self,
      ← sig_hi_quotient f e hsh]
  have hlo : oneParityResidue f e % 2 ^ (128 - decimalShift e)
      = oneResidue f e := by
    rw [oneParityResidue, stepResidue, Nat.mod_mod_of_dvd _ ⟨2, hw⟩, oneResidue,
      stepResidue]
  conv_lhs => rw [← Nat.div_add_mod (oneParityResidue f e)
    (2 ^ (128 - decimalShift e))]
  rw [hhi, hlo]

/-- Once the remainder has reached half a unit step, `roundU1` can be false
    only through yy's tie branch, which declines exactly for an even `sigHi`. -/
theorem one_even_of_not_round_up (f : ℕ) (e : ℤ) (hsh : decimalShift e < 4)
    (hu1 : (toDecimalCandidates f e).roundU1 = false)
    (hres : 2 ^ (127 - decimalShift e) ≤ oneResidue f e) :
    sigHi f e % 2 = 0 := by
  have hpow : (2 : ℕ) ^ 63 * 2 ^ (64 - decimalShift e)
      = 2 ^ (127 - decimalShift e) := by
    rw [← pow_add]; congr 1; omega
  have hunit : (0 : ℕ) < 2 ^ (64 - decimalShift e) := by positivity
  have h63 : 2 ^ 63 ≤ sigLo f e := by
    rw [sig_lo_eq_residue_div f e hsh, Nat.le_div_iff_mul_le hunit, hpow]
    exact hres
  have hround : (toDecimalCandidates f e).roundU1
      = if sigLo f e = 2 ^ 63 then decide (sigHi f e % 2 = 1)
        else decide (2 ^ 63 < sigLo f e) := rfl
  rw [hround] at hu1
  -- The tie branch declines for an even `sigHi`; the other branch cannot
  -- decline at all, the remainder having passed half a unit step.
  split at hu1 <;> (have := of_decide_eq_false hu1; omega)

/-- The undecided bands as windows on the doubled residue. The truncation error
    is below `2^54·den`, so `2^54` bounds its reach in remainder units. -/
private def oneWindows (e : ℤ) : ModWindows where
  g := 2 * trimSig e
  modulus := 2 ^ (129 - decimalShift e)
  f0 := 1
  f1 := 2 ^ 53 - 1
  windows :=
    let half : ℤ := 2 ^ (127 - decimalShift e)
    let band : ℤ := 2 ^ (64 - decimalShift e)
    let w : ℤ := 2 ^ (128 - decimalShift e)
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
    ((2 : ℤ) ^ (127 - decimalShift e) - 2 ^ 54,
        (2 : ℤ) ^ (127 - decimalShift e)) ∈ (oneWindows e).windows ∧
      ((2 : ℤ) ^ (128 - decimalShift e) + 2 ^ (127 - decimalShift e) - 2 ^ 54,
          (2 : ℤ) ^ (128 - decimalShift e) + 2 ^ (127 - decimalShift e) - 1)
        ∈ (oneWindows e).windows := by
  simp only [oneWindows, ite_eq_right hτ]
  exact ⟨.tail _ (.head _), .tail _ (.tail _ (.head _))⟩

/-- Below the midpoint the truncation error cannot reach it: a remainder short
    of half a unit step is short of it by more than `2^54`. -/
theorem one_residue_below_half (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hτ : trimNum e % trimDen e ≠ 0)
    (hres : oneResidue f e < 2 ^ (127 - decimalShift e)) :
    oneResidue f e + 2 ^ 54 < 2 ^ (127 - decimalShift e) := by
  by_contra hcon
  have hsh := decimal_shift_lt_four e hr.range
  obtain ⟨q, hcert⟩ := one_windows_refuted e hr.range
  obtain ⟨hbelow, habove⟩ := one_windows_truncated e hτ
  -- The remainder is in the last `2^54` below the midpoint; the parity of
  -- `sigHi` decides which of the two windows holds it.
  have hlo : (2 : ℤ) ^ (127 - decimalShift e)
      ≤ (oneResidue f e : ℤ) + 2 ^ 54 := by
    exact_mod_cast
      (show 2 ^ (127 - decimalShift e) ≤ oneResidue f e + 2 ^ 54 from by omega)
  have hhi : (oneResidue f e : ℤ) + 1
      ≤ (2 : ℤ) ^ (127 - decimalShift e) := by
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
        = (2 : ℤ) ^ (128 - decimalShift e) + (oneResidue f e : ℤ) := by
      rw [hsplit, hpar]; push_cast; ring
    exact one_no_window_hit f e hr hcert habove (by rw [hp]; linarith)
      (by rw [hp]; linarith)

/-- In the packed tie band an even `sigHi` occurs only at a genuine midpoint:
    the remainder is exactly half a unit step and the power-of-ten
    approximation is exact, so the exact value is a tie too, and yy resolves it
    to even. -/
theorem one_tie_band_even (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hpar : sigHi f e % 2 = 0)
    (hlo : 2 ^ (127 - decimalShift e) ≤ oneResidue f e)
    (hhi : oneResidue f e
      < 2 ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e)) :
    oneResidue f e = 2 ^ (127 - decimalShift e)
      ∧ trimNum e % trimDen e = 0 := by
  have hsh := decimal_shift_lt_four e hr.range
  obtain ⟨q, hcert⟩ := one_windows_refuted e hr.range
  have hp : (oneParityResidue f e : ℤ) = (oneResidue f e : ℤ) := by
    rw [one_parity_residue_split f e hsh, hpar]; push_cast; ring
  -- The two ends of the band above the midpoint, which both window shapes
  -- share.
  have hup : (oneParityResidue f e : ℤ)
      ≤ (2 : ℤ) ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e) - 1 := by
    rw [hp]
    have hz : (oneResidue f e : ℤ) + 1
        ≤ (2 : ℤ) ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e) := by
      exact_mod_cast (show oneResidue f e + 1
        ≤ 2 ^ (127 - decimalShift e) + 2 ^ (64 - decimalShift e) from hhi)
    linarith
  have hdown (hgt : 2 ^ (127 - decimalShift e) < oneResidue f e) :
      (2 : ℤ) ^ (127 - decimalShift e) + 1 ≤ (oneParityResidue f e : ℤ) := by
    rw [hp]
    exact_mod_cast
      (show 2 ^ (127 - decimalShift e) + 1 ≤ oneResidue f e from hgt)
  -- The band above the midpoint is refuted at every exponent, leaving the
  -- midpoint itself.
  have hband (hgt : 2 ^ (127 - decimalShift e) < oneResidue f e) : False :=
    one_no_window_hit f e hr hcert (.head _) (hdown hgt) hup
  have hmid : oneResidue f e = 2 ^ (127 - decimalShift e) := by
    rcases Nat.eq_or_lt_of_le hlo with heq | hgt
    · exact heq.symm
    · exact (hband hgt).elim
  -- A truncated power-of-ten approximation refutes the midpoint too, so it is
  -- exact here.
  refine ⟨hmid, ?_⟩
  by_contra hτ
  obtain ⟨hwin, -⟩ := one_windows_truncated e hτ
  have hz : (oneParityResidue f e : ℤ) = (2 : ℤ) ^ (127 - decimalShift e) := by
    rw [hp, hmid]; push_cast; ring
  exact one_no_window_hit f e hr hcert hwin
    (by rw [hz]; exact sub_le_self _ (by positivity)) (by rw [hz])

/-- The certificates' semantic content at the unit step: the remainder never
    lands where the packed test could round the wrong way. Below this theorem is
    modular arithmetic of `2·f·p10`; above it the rounding argument sees only
    these two implications. -/
theorem one_midpoint_separated (f : ℕ) (e : ℤ) (hr : Regular f e) :
    OneMidpointSeparated f e := by
  have hsh := decimal_shift_lt_four e hr.range
  have hden := trim_den_pos e
  have htrunc := trim_trunc_lt f e hr
  have hstep := trim_mul_eq_two_half e hsh
  have hgap := one_gap_split f e
  -- Below the midpoint the gap stays strictly inside half a step: the
  -- remainder is a whole `den` short, or `2^54·den` short with the truncation
  -- error to spend.
  have hbelow (hlt : oneResidue f e < 2 ^ (127 - decimalShift e)) :
      2 * oneGap f e < trimMul e := by
    by_cases hτ : trimNum e % trimDen e = 0
    · have hmono : trimDen e * (oneResidue f e + 1)
          ≤ trimDen e * 2 ^ (127 - decimalShift e) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : trimDen e * (oneResidue f e + 1)
          = trimDen e * oneResidue f e + trimDen e := by ring
      rw [hτ] at hgap
      omega
    · have hroom := one_residue_below_half f e hr hτ hlt
      have hmono : trimDen e * (oneResidue f e + 2 ^ 54)
          ≤ trimDen e * 2 ^ (127 - decimalShift e) :=
        Nat.mul_le_mul_left _ (by omega)
      have hexp : trimDen e * (oneResidue f e + 2 ^ 54)
          = trimDen e * oneResidue f e + 2 ^ 54 * trimDen e := by ring
      omega
  refine ⟨?_, ?_⟩
  · intro hu1
    rcases Nat.lt_or_ge (oneResidue f e) (2 ^ (127 - decimalShift e)) with
      hlt | hge
    · exact (hbelow hlt).le
    -- At the midpoint yy declined only for an even `sigHi`, and then the
    -- power-of-ten approximation is exact, so the gap is exactly half a step.
    · obtain ⟨hres, hτ⟩ := one_tie_band_even f e hr
        (one_even_of_not_round_up f e hsh hu1 hge) hge
        ((one_round_half f e hsh).2 hu1)
      rw [hgap, hres, hτ]
      omega
  · intro hmid
    rcases Nat.lt_or_ge (oneResidue f e) (2 ^ (127 - decimalShift e)) with
      hlt | hge
    · exact absurd hmid (by have := hbelow hlt; omega)
    · rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · exact heq.symm
      -- Above the midpoint the gap has already passed half a step.
      · exfalso
        have hmono : trimDen e * (2 ^ (127 - decimalShift e) + 1)
            ≤ trimDen e * oneResidue f e := Nat.mul_le_mul_left _ (by omega)
        have hexp : trimDen e * (2 ^ (127 - decimalShift e) + 1)
            = trimDen e * 2 ^ (127 - decimalShift e) + trimDen e := by ring
        omega

/-! ### Nearest at the unit step -/

/-- At a packed midpoint the remainder is exactly half a unit step, so yy takes
    its tie branch and rounds the significand to even. -/
theorem dec_one_even_of_packed_midpoint (f : ℕ) (e : ℤ)
    (hsh : decimalShift e < 4)
    (hres : oneResidue f e = 2 ^ (127 - decimalShift e)) :
    (toDecimalCandidates f e).decOne % 2 = 0 := by
  set c := toDecimalCandidates f e
  have hlo : sigLo f e = 2 ^ 63 := by
    rw [sig_lo_eq_residue_div f e hsh, hres,
      Nat.pow_div (by omega) (by norm_num),
      show 127 - decimalShift e - (64 - decimalShift e) = 63 from by omega]
  have hround : c.roundU1 = decide (sigHi f e % 2 = 1) := by
    show (if sigLo f e = 2 ^ 63 then decide (sigHi f e % 2 = 1)
      else decide (2 ^ 63 < sigLo f e)) = _
    simp [hlo]
  -- Odd increments, even stays put, and both land on an even significand.
  show (sigHi f e + if c.roundU1 then 1 else 0) % 2 = 0
  by_cases hpar : sigHi f e % 2 = 1 <;> simp [hround, hpar] <;> omega

/-- `decOne` is a nearest value on the grid at `decimalExponent e`, ties to
    even: it lies within half a step, and at an exact midpoint it is even. These
    are the two facts the exact method asks of a fine candidate. -/
theorem dec_one_nearest (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let x := value f e * 10 ^ (-decimalExponent e)
    |((toDecimalCandidates f e).decOne : ℚ) - x| ≤ 1 / 2 ∧
      (|((toDecimalCandidates f e).decOne : ℚ) - x| = 1 / 2 →
        (toDecimalCandidates f e).decOne % 2 = 0) := by
  have hsh := decimal_shift_lt_four e hr.range
  have hsep := one_midpoint_separated f e hr
  set c := toDecimalCandidates f e
  by_cases hu1 : c.roundU1 = true
  -- Rounding up: the candidate is `trimMul - oneGap` above the value, and the
  -- packed test has already carried the gap past half a step.
  · have hdec : (c.decOne : ℚ) = (sigHi f e : ℚ) + 1 := by
      show ((sigHi f e + if c.roundU1 then 1 else 0 : ℕ) : ℚ) = _
      simp [hu1]
    obtain ⟨hle, heq⟩ := half_step_iff_scaled_error f e
      (cand := (sigHi f e : ℚ) + 1)
      (dist := (trimMul e : ℚ) - (oneGap f e : ℚ))
      (by linear_combination sig_hi_scaled_error f e hr.range)
    have hlow : (trimMul e : ℚ) ≤ 2 * (oneGap f e : ℚ) := by
      exact_mod_cast one_half_step_le_gap f e hr hu1
    -- The gap can pass the step, but only by a truncation error, so it stays
    -- clear of a step and a half.
    have hroom : (oneGap f e : ℚ) < 3 / 2 * (trimMul e : ℚ) := by
      have hbig : (2 : ℚ) ^ 55 * (trimDen e : ℚ) ≤ (trimMul e : ℚ) := by
        exact_mod_cast trim_two_trunc_le_mul e hsh
      have hhigh :
          (oneGap f e : ℚ) < (trimMul e : ℚ) + 2 ^ 54 * (trimDen e : ℚ) := by
        exact_mod_cast one_gap_lt_mul_add f e hr
      linarith
    refine ⟨?_, ?_⟩
    · rw [hdec]
      refine hle.mpr ?_
      have habs :
          |(trimMul e : ℚ) - (oneGap f e : ℚ)| ≤ (trimMul e : ℚ) / 2 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    · intro hmid
      rw [hdec] at hmid
      have hq := heq.mp hmid
      -- Equal distance allows `oneGap = trimMul / 2` or `3 * trimMul / 2`.
      -- The room below a step and a half excludes the latter.
      have hnat : 2 * oneGap f e = trimMul e := by
        by_cases hcase : oneGap f e ≤ trimMul e
        · have hcast : (oneGap f e : ℚ) ≤ (trimMul e : ℚ) := by
            exact_mod_cast hcase
          rw [abs_of_nonneg (by linarith)] at hq
          have hgap : (2 : ℚ) * (oneGap f e : ℚ) = (trimMul e : ℚ) := by
            linarith
          exact_mod_cast hgap
        · exfalso
          have hcast : (trimMul e : ℚ) < (oneGap f e : ℚ) := by
            exact_mod_cast Nat.not_le.mp hcase
          rw [abs_of_nonpos (by linarith)] at hq
          linarith
      exact dec_one_even_of_packed_midpoint f e hsh (hsep.packedMidpoint hnat)
  -- Rounding down: the candidate is `oneGap` below the value, and only the
  -- separation says the gap has not passed half a step.
  · rw [Bool.not_eq_true] at hu1
    have hdec : (c.decOne : ℚ) = (sigHi f e : ℚ) := by
      show ((sigHi f e + if c.roundU1 then 1 else 0 : ℕ) : ℚ) = _
      simp [hu1]
    obtain ⟨hle, heq⟩ := half_step_iff_scaled_error f e
      (cand := (sigHi f e : ℚ))
      (dist := -(oneGap f e : ℚ))
      (sig_hi_scaled_error f e hr.range)
    have habs : |(-(oneGap f e : ℚ))| = (oneGap f e : ℚ) := by
      rw [abs_neg, Nat.abs_cast]
    refine ⟨?_, ?_⟩
    · rw [hdec]
      refine hle.mpr ?_
      rw [habs]
      exact_mod_cast hsep.belowHalf hu1
    · intro hmid
      rw [hdec] at hmid
      have hq := heq.mp hmid
      rw [habs] at hq
      have hnat : 2 * oneGap f e = trimMul e := by exact_mod_cast hq
      exact dec_one_even_of_packed_midpoint f e hsh (hsep.packedMidpoint hnat)

/-! ## The multiple-of-ten candidates

`roundD0` and `roundU0` are read once each, as exact comparisons of the gap with
half a scaled ULP. Both the soundness of a fired flag and the completeness of an
unfired one are then directions of the same equivalence, and neither has to look
at a packed comparison again.
-/

/-- What `roundD0` decides: the trim-down gap is within half a ULP, with the
    boundary itself allowed only for even `f`. -/
theorem round_d0_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then trimGap f e ≤ trimNum e
        else trimGap f e < trimNum e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e hr.range
  set c := trimResidue f e / trimUnit e with hc
  set p := trimSig e / trimUnit e with hp
  -- yy's test, in the window quantities it actually compares.
  have hflag : (toDecimalCandidates f e).roundD0
      = if p = c then decide (f % 2 = 0) else decide (c < p) := by
    rw [hc, hp, ← trim_c_eq f e hsh, ← trim_half_ulp_eq e hsh]
    rfl
  rw [hflag]
  constructor
  · intro hd0
    split_ifs at hd0 with htie
    -- The apparent tie `halfUlp = c`, which yy takes only for even `f`.
    · simp only [show f % 2 = 0 from by simpa using hd0, reduceIte]
      exact trim_gap_le f e hr htie.symm.le
    -- The strict comparison `c < halfUlp`, which needs no certificate.
    · have hgap := trim_gap_lt f e hr (by simpa using hd0)
      split_ifs
      · exact hgap.le
      · exact hgap
  · intro hgap
    split_ifs at hgap with heven
    -- Even `f`: the gap is within `num`, so `c` cannot have passed `halfUlp`,
    -- which would put the gap a whole unit beyond `num`.
    · have hcmp : c ≤ p := by
        by_contra hcon
        exact absurd (trim_num_lt_gap f e hr (by omega)) (by omega)
      split_ifs
      · simpa using heven
      · simp only [decide_eq_true_eq]; omega
    -- Odd `f`: the gap is strictly within `num`, which excludes the tie.
    · have hcmp : c < p := by
        by_contra hcon
        exact absurd (trim_num_le_gap f e hr (by omega)) (by omega)
      split_ifs
      · omega
      · simpa using hcmp

/-- The trim-down candidate is in range whenever `roundD0` fires. -/
theorem dec_ten_down (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hd0 : (toDecimalCandidates f e).roundD0 = true) :
    let k := decimalExponent e
    let x := value f e * 10 ^ (-k)
    let u := ulp e * 10 ^ (-k)
    if f % 2 = 0 then
      |(sigTen f e : ℚ) - x| ≤ u / 2
    else
      |(sigTen f e : ℚ) - x| < u / 2 := by
  intro k x u
  obtain ⟨hle, hlt⟩ :=
    half_ulp_iff_scaled_error f e hr.range
      (dec_ten_down_scaled_error f e hr.range)
  have habs : |(-(trimGap f e : ℚ))| = (trimGap f e : ℚ) := by
    rw [abs_neg]; exact abs_of_nonneg (Nat.cast_nonneg _)
  have hgap := (round_d0_iff_gap f e hr).mp hd0
  split_ifs at hgap ⊢
  · exact hle.mpr (by rw [habs]; exact_mod_cast hgap)
  · exact hlt.mpr (by rw [habs]; exact_mod_cast hgap)

/-- What `roundU0` decides: the trim-up gap is within half a ULP, with the
    boundary itself allowed only for even `f`. All three yy branches leave the
    packed sum within one window unit of the modulus; only the final `t0 ≤ t1`
    branch can fire for odd `f`, and there the bound is strict. -/
theorem round_u0_iff_gap (f : ℕ) (e : ℤ) (hr : Regular f e) :
    (toDecimalCandidates f e).roundU0 = true
      ↔ if f % 2 = 0 then trimScale e ≤ trimGap f e + trimNum e
        else trimScale e < trimGap f e + trimNum e := by
  have hsh : decimalShift e < 4 := decimal_shift_lt_four e hr.range
  set c := trimResidue f e / trimUnit e with hc
  set p := trimSig e / trimUnit e with hp
  -- Lift a packed sum reaching the modulus to the untruncated bound.
  have hpack (hb : 10 * 2 ^ 60 ≤ c + p + 1) :
      trimModulus e ≤ trimResidue f e + trimSig e + trimUnit e := by
    rw [trim_modulus_eq e hsh]
    calc trimUnit e * (10 * 2 ^ 60)
        ≤ trimUnit e * (c + p) + trimUnit e := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hb
      _ ≤ trimResidue f e + trimSig e + trimUnit e :=
          Nat.add_le_add_right (trim_pack f e (c + p) le_rfl) _
  -- yy's three tests, in the window quantities they actually compare.
  have hflag : (toDecimalCandidates f e).roundU0
      = (if c + p + 1 = 10 * 2 ^ 60 then decide (f % 2 = 0)
        else if decimalExponent e = 0 ∧ c + p = 10 * 2 ^ 60 then
          decide (f % 2 = 0)
        else decide (10 * 2 ^ 60 ≤ c + p)) := by
    rw [hc, hp, ← trim_c_eq f e hsh, ← trim_half_ulp_eq e hsh]
    rfl
  rw [hflag]
  constructor
  · intro hu0
    split_ifs at hu0 with htie1 htie0
    -- The one-LSB-offset tie `t1 + 1 = t0`, for even `f` only.
    · simp only [show f % 2 = 0 from by simpa using hu0, reduceIte]
      exact trim_scale_le f e hr (hpack htie1.ge)
    -- The exact tie `t1 = t0`, accepted only when `k = 0`, even `f` only.
    · simp only [show f % 2 = 0 from by simpa using hu0, reduceIte]
      exact trim_scale_le f e hr (hpack (Nat.le_succ_of_le htie0.2.ge))
    -- The final `t0 ≤ t1` branch, the only one that can fire for odd `f`.
    · have hplain : 10 * 2 ^ 60 ≤ c + p := by simpa using hu0
      split_ifs
      · exact trim_scale_le f e hr (hpack (Nat.le_succ_of_le hplain))
      · exact trim_scale_lt f e hr hplain htie0
  · intro hbound
    split_ifs at hbound with heven
    -- Even `f`: the packed sum cannot fall two units short of the modulus.
    · split_ifs
      · simpa using heven
      · simpa using heven
      · simp only [decide_eq_true_eq]
        by_contra hcon
        exact absurd (trim_gap_num_lt_scale f e hr (by omega)) (by omega)
    -- Odd `f`: a strict bound excludes both tie branches.
    · split_ifs with htie1 htie0
      · exact absurd (trim_gap_num_le_scale f e hr htie1) (by omega)
      · exact absurd (trim_gap_num_eq_scale_of_k_zero f e hr htie0.1 htie0.2)
          (by omega)
      · simp only [decide_eq_true_eq]
        by_contra hcon
        exact absurd (trim_gap_num_lt_scale f e hr (by omega)) (by omega)

/-- The trim-up candidate is in range whenever `roundU0` fires. -/
theorem dec_ten_up (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hu0 : (toDecimalCandidates f e).roundU0 = true) :
    let k := decimalExponent e
    let x := value f e * 10 ^ (-k)
    let u := ulp e * 10 ^ (-k)
    if f % 2 = 0 then
      |(sigTen f e : ℚ) + 10 - x| ≤ u / 2
    else
      |(sigTen f e : ℚ) + 10 - x| < u / 2 := by
  intro k x u
  obtain ⟨hle, hlt⟩ :=
    half_ulp_iff_scaled_error f e hr.range
      (dec_ten_up_scaled_error f e hr.range)
  -- The free side, shared by both parities.
  have hfree : -(trimNum e : ℚ) < (trimScale e : ℚ) - (trimGap f e : ℚ) := by
    have hz : (trimGap f e : ℚ) < (trimScale e : ℚ) + (trimNum e : ℚ) := by
      exact_mod_cast trim_gap_lt_scale_add f e hr
    linarith
  have hbound := (round_u0_iff_gap f e hr).mp hu0
  split_ifs at hbound ⊢
  · refine hle.mpr (abs_le.mpr ⟨hfree.le, ?_⟩)
    have hz : (trimScale e : ℚ) ≤ (trimGap f e : ℚ) + (trimNum e : ℚ) := by
      exact_mod_cast hbound
    linarith
  · refine hlt.mpr (abs_lt.mpr ⟨hfree, ?_⟩)
    have hz : (trimScale e : ℚ) < (trimGap f e : ℚ) + (trimNum e : ℚ) := by
      exact_mod_cast hbound
    linarith

/-! ## yy's coarse and fine outputs

On the coarse path, yy emits a multiple of ten, and `dec_ten_down` and
`dec_ten_up` bound its distance. On the fine path, it emits `decOne`, whose
half-step bound already implies that it round-trips because the grid step at
`decimalExponent e` is at most one ULP.
-/

/-- On the coarse path, yy emits a multiple of ten that round-trips. Which of
    the two multiple-of-ten candidates `decTen` denotes is decided by `roundU0`;
    whether both trim flags fire is irrelevant. -/
theorem coarse_output_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true →
    (toDecimal f e).1 % 10 = 0 ∧
      Roundtrips f e (((toDecimal f e).1 : ℚ) * 10 ^ decimalExponent e) := by
  intro c htrim
  have hy : (toDecimal f e).1 = c.decTen := by
    show (if c.roundD0 || c.roundU0 then c.decTen else c.decOne) = _
    rw [htrim]
    rfl
  have hten : c.decTen = sigTen f e + (if c.roundU0 then 10 else 0) := rfl
  rw [hy]
  have h10 := sig_ten_mod_ten f e
  refine ⟨by rw [hten]; cases c.roundU0 <;> simp <;> omega, ?_⟩
  refine (roundtrips_iff_scaled f e (decimalExponent e) _).mpr ?_
  cases hu0 : c.roundU0
  · -- Only `roundD0` fired, so `decTen` is the trim-down candidate.
    have hd0 : c.roundD0 = true := by
      rw [hu0, Bool.or_false] at htrim; exact htrim
    rw [hten, hu0]
    simpa using dec_ten_down f e hr hd0
  · rw [hten, hu0]
    simpa using dec_ten_up f e hr hu0

/-- On the fine path, yy emits `decOne`, a nearest value on its own grid. -/
theorem fine_output_nearest (f : ℕ) (e : ℤ) (hr : Regular f e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = false →
    let x := value f e * 10 ^ (-decimalExponent e)
    |((toDecimal f e).1 : ℚ) - x| ≤ 1 / 2 ∧
      (|((toDecimal f e).1 : ℚ) - x| = 1 / 2 → (toDecimal f e).1 % 2 = 0) := by
  intro c htrim
  rw [show (toDecimal f e).1 = c.decOne from by
    show (if c.roundD0 || c.roundU0 then _ else _) = _
    rw [htrim]
    rfl]
  exact dec_one_nearest f e hr

/-! ## Completeness of the trim decision

The exact method takes the coarse case exactly when the rounding interval
contains a multiple of ten, that is, when a digit can be dropped. yy makes the
same choice through `roundD0` and `roundU0`: it trims when either of its two
coarse candidates round-trips. `dec_ten_down` and `dec_ten_up` show that a trim
flag implies such a candidate round-trips; the converses below show that a
round-tripping coarse candidate fires a flag.

The rounding interval is narrower than one coarse step, so yy's two coarse
candidates are the only multiples of ten it can contain. It is therefore enough
to recognize those two. When neither round-trips, yy keeps `decOne`, which lies
on the grid one decimal digit finer.

Because yy compares quantities truncated to window units, a packed tie can hide
which side of the exact rounding boundary the candidate lies on. For even `f`,
ties are accepted, so a rejection implies at least one full window unit of
separation, enough to dominate the power-of-ten truncation error. For odd `f`,
ties are rejected, so the ambiguous packed-tie cases fall in the inward windows
that `trim_gap_separated` excludes. The exceptional `roundU0` tie at `k = 0`
lies one unit farther out, where the power-of-ten approximation is exact, and
`trim_gap_num_eq_scale_of_k_zero` settles it directly.
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
  have hmul := trim_mul_pos e
  have hdown := dec_ten_down_scaled_error f e hr.range
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

/-- Completeness: if the trim-down candidate round-trips, `roundD0` fires. -/
theorem round_d0_of_ten_down_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hround : Roundtrips f e (sigTen f e * 10 ^ decimalExponent e)) :
    (toDecimalCandidates f e).roundD0 = true := by
  obtain ⟨hle, hlt⟩ :=
    half_ulp_iff_scaled_error f e hr.range
      (dec_ten_down_scaled_error f e hr.range)
  have hs := (roundtrips_iff_scaled f e (decimalExponent e) _).mp hround
  refine (round_d0_iff_gap f e hr).mpr ?_
  -- Split on parity: both bounds allow ties iff `f` is even.
  split_ifs at hs ⊢
  · have hq := hle.mp hs
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at hq
    exact_mod_cast hq
  · have hq := hlt.mp hs
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at hq
    exact_mod_cast hq

/-- Completeness: if the trim-up candidate round-trips, `roundU0` fires. -/
theorem round_u0_of_ten_up_roundtrips (f : ℕ) (e : ℤ) (hr : Regular f e)
    (hround :
      Roundtrips f e ((sigTen f e + 10 : ℕ) * 10 ^ decimalExponent e)) :
    (toDecimalCandidates f e).roundU0 = true := by
  obtain ⟨hle, hlt⟩ :=
    half_ulp_iff_scaled_error f e hr.range
      (dec_ten_up_scaled_error f e hr.range)
  have hs := (roundtrips_iff_scaled f e (decimalExponent e) _).mp hround
  push_cast at hs
  refine (round_u0_iff_gap f e hr).mpr ?_
  -- Split on parity: both bounds allow ties iff `f` is even.
  split_ifs at hs ⊢
  · have hq := (abs_le.mp (hle.mp hs)).2
    exact_mod_cast (by linarith :
      (trimScale e : ℚ) ≤ (trimGap f e : ℚ) + (trimNum e : ℚ))
  · have hq := (abs_lt.mp (hlt.mp hs)).2
    exact_mod_cast (by linarith :
      (trimScale e : ℚ) < (trimGap f e : ℚ) + (trimNum e : ℚ))

/-- If the rounding interval contains a multiple of ten, yy trims. -/
theorem trim_of_coarse_roundtrip (f : ℕ) (e : ℤ) (hr : Regular f e) (d : ℕ)
    (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ decimalExponent e)) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true := by
  intro c
  rw [Bool.or_eq_true]
  rcases coarse_candidate_cases f e hr d h10 hround with rfl | rfl
  · exact Or.inl (round_d0_of_ten_down_roundtrips f e hr hround)
  · exact Or.inr (round_u0_of_ten_up_roundtrips f e hr hround)

/-! ## yy refines the exact method

Nothing above is needed beyond `ulp_scaled_bounds` and the three semantic
obligations `coarse_output_roundtrips`, `fine_output_nearest`, and
`trim_of_coarse_roundtrip`. In particular no claim is made that yy's packed
decisions agree with the exact ones: a packed midpoint need not be an exact
midpoint, and the trim flags are matched to the existence of an exact coarse
candidate, not to any exact comparison.
-/

/-- yy implements the exact method: it trims exactly when an exact coarse
    candidate exists. One direction is completeness, `trim_of_coarse_roundtrip`;
    the other holds because trimmed output is itself a multiple of ten that
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
