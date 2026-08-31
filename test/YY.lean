-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import Core
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! # Correctness of yy

`Core.lean` proves that an exact, Schubfach-like selection rule produces a
shortest, correctly rounded decimal whenever the decimal grid step is at most
one ULP and strictly greater than a tenth of one. This file proves that yy
implements that rule. What yy shares with any other algorithm—the format's
spacing, the decimal exponent, the power-of-ten table—is defined there too.

The whole argument is that each of yy's three packed Boolean decisions is an
exact arithmetic predicate. yy computes them from a truncated power of ten and
from a product whose low bits it has already dropped, so a decision could in
principle differ from the exact one; the narrow regions where that could happen
are discharged by finite modular certificates. Once the three characterizations
are in hand, the rest is a short assembly into `ExactCandidate`. No claim is
made that yy's packed comparisons agree with the exact ones case by case—a
packed midpoint need not be an exact midpoint—only that the output is right.

Throughout this file:
* `fmt`: the binary format, supplying the precision, exponent range and width;
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
`oneGap`—and keeps the rest below them: the packed quantities, the exact
identities behind them, the truncation error, bounds on that error, and the
`ModWindows` certificates closing the regions the bounds leave open.

The coarse pair carries a second equivalence, on the other side:

    round_d0_iff_roundtrips :  roundD0 ↔ sigTen round-trips
    round_u0_iff_roundtrips :  roundU0 ↔ sigTen + 10 round-trips

The two boundaries mean different things and stay separate. `*_iff_gap` says the
finite-precision implementation reaches the correct exact decision;
`*_iff_roundtrips` connects the integer scale that decision is made in to the
semantic specification. Consumers read one direction or the other:
`coarse_output_roundtrips` uses `→`, `trim_of_coarse_roundtrip` uses `←`.

## What is a parameter and what is checked

Everything here is polymorphic in the format, and the split is deliberate:
*algebraic identities are parameterized, numerical approximation properties are
checked*. The identities hold for any format, and are proved once against `fmt`.
The properties that depend on how close a fixed-point logarithm is to its exact
value, or on where a truncated power of ten falls against a window edge, do not
follow from any inequality between the parameters, so they are collected as
per-format obligations in `Layout` and `Checks` and discharged by finite search.

That boundary is what makes another format cheap in proof and expensive only in
compute. `correct_of` is the generic theorem; `correct` below is binary64's
instance of it, `YY128.correct` is binary128's, and `YY80.correct` the x87
80-bit format's.

## Dependencies

    correct_of
      ← ulp_scaled_bounds
      ← exact_candidate
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

namespace YY

/-- An exponent of `fmt`. No lemma below varies the exponent at a fixed format,
    so the two travel as one value; indexing by the format rather than carrying
    it as a field keeps `fmt` inferable, hence implicit. -/
structure FPExp (fmt : Format) where
  val : ℤ

variable {fmt : Format}

/-- Argument and comparison positions take the exponent as an integer without
    ceremony. Where nothing fixes the type — under a `^`, or in an equation
    with no typed side — the sites say `.val` instead. -/
instance : CoeHead (FPExp fmt) ℤ := ⟨FPExp.val⟩

/-! ## yy's arithmetic model

Everything from here to `## The coarse decisions` is machinery for the three
flag equivalences: the algorithm as yy computes it, the packed quantities its
comparisons are made of, the exact identities those quantities satisfy, bounds
on how far truncation can move them, and the certificates that close what the
bounds leave open. The subsections are stages of one proof, not interfaces.
`ulp_scaled_bounds`, at the end, is the exception: it is an obligation in its
own right and is proved here because it is the same arithmetic.
-/

/-! ### The layout yy packs into

The side conditions on the format that the packing needs. They are inequalities
between the parameters, so they are hypotheses rather than checks.
-/

/-- A format wide enough for yy's packing. The digit slot is four bits and the
    window unit is `2^(width+4)`, so the width has to hold both and still leave
    the unit negligible against a normalized power of ten; and the significand
    bound `2·f < 2^(prec+1)` has to fit under `2^(2·width-1)`. binary64 and the
    two extended formats satisfy both with room to spare. -/
structure Layout (fmt : Format) : Prop where
  width_ge : 7 ≤ fmt.width
  prec_le : fmt.prec + 5 ≤ 2 * fmt.width

/-- Bundled because the arithmetic below keeps needing both. The first is
    definitional, but `Format.p10Width` is an `abbrev` that `omega` will not
    unfold, so it treats `fmt.p10Width` and `fmt.width` as unrelated atoms
    unless handed the identity. -/
theorem Layout.width_facts {fmt : Format} (hl : Layout fmt) :
    fmt.p10Width = 2 * fmt.width ∧ 7 ≤ fmt.width := ⟨rfl, hl.width_ge⟩

/-- How many of the four digit-slot bits the trim-down comparison leaves packed
    into `c`. yy compares the packed value as it stands, so all four; zmij runs
    this algorithm only at the extended formats, and there re-reads the four
    before deciding a tie.

    Not a `Format` field, and spelled without dot notation to keep that visible:
    it is what an implementation does with the table, not what the format is. -/
def packedBits (fmt : Format) : ℕ := if 64 < fmt.width then 0 else 4

theorem packed_bits_le_four (fmt : Format) : packedBits fmt ≤ 4 := by
  rw [packedBits]
  split <;> omega

/-! ### yy's conversion

The quantities yy computes from the shared power-of-ten table, and the shift
that aligns that table's exponent with the binary one. `toDecimalCandidates` is
the algorithm itself: the three packed Booleans and the two candidates they
choose between, which is what the whole file is about. The alignment lemmas come
last because `exponent_shift_align` is stated against `power10Exponent`.
-/

/-- The shift before clamping. Kept separate so that the check ruling out a
    clamp can be stated about it. -/
def shiftRaw (e : FPExp fmt) : ℤ :=
  e + (-fmt.decimalExponent e * fmt.log2Ten.1) / 2 ^ fmt.log2Ten.2

/-- Shift chosen to align the binary exponent with the power of ten. -/
def exponentShift (e : FPExp fmt) : ℕ := (shiftRaw e).toNat

/-- The decimal significand ⌊f·2^(h+1)·⌊10^(-k)·2^(2w)⌋ / 2^w⌋. -/
def scaledSignificand (f : ℕ) (e : FPExp fmt) : ℕ :=
  let k := fmt.decimalExponent e
  let h := exponentShift e
  let p10 := fmt.power10Significand (-k)
  f * 2 ^ (h + 1) * p10 / 2 ^ fmt.width

/-- High half of the decimal significand. -/
def sigHi (f : ℕ) (e : FPExp fmt) : ℕ := scaledSignificand f e / 2 ^ fmt.width

/-- Low half of the decimal significand. -/
def sigLo (f : ℕ) (e : FPExp fmt) : ℕ := scaledSignificand f e % 2 ^ fmt.width

/-- yy's `ten`: `sigHi` with its last decimal digit cleared. -/
def sigTen (f : ℕ) (e : FPExp fmt) : ℕ := sigHi f e - sigHi f e % 10

theorem sig_ten_mod_ten (f : ℕ) (e : FPExp fmt) : sigTen f e % 10 = 0 := by
  rw [sigTen]; omega

structure DecimalCandidates where
  k : ℤ
  decOne : ℕ
  roundU1 : Bool
  decTen : ℕ
  roundD0 : Bool
  roundU0 : Bool

def toDecimalCandidates (f : ℕ) (e : FPExp fmt) : DecimalCandidates :=
  let k := fmt.decimalExponent e
  let h := exponentShift e

  let p10 := fmt.power10Significand (-k)
  let p10Hi := p10 / 2 ^ fmt.width

  let sig := scaledSignificand f e
  let sigHi := sig / 2 ^ fmt.width
  let sigLo := sig % 2 ^ fmt.width

  let one := sigHi % 10
  let ten := sigHi - one
  let c := one * 2 ^ (fmt.width - 4) + sigLo / 2 ^ 4
  let halfUlp := p10Hi / 2 ^ (4 - h)
  let cDown := one * 2 ^ (fmt.width - packedBits fmt)
    + sigLo / 2 ^ packedBits fmt
  let halfUlpDown := p10 / 2 ^ (fmt.width + packedBits fmt - h)
  let t0 := 10 * 2 ^ (fmt.width - 4)
  let t1 := c + halfUlp

  let roundU1 : Bool :=
    if sigLo = 2 ^ (fmt.width - 1) then
      sigHi % 2 = 1
    else
      2 ^ (fmt.width - 1) < sigLo

  let roundD0 : Bool :=
    if halfUlpDown = cDown then
      f % 2 = 0
    else
      cDown < halfUlpDown

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
    significand and exponent using yy's full path.

    yy is a binary64 algorithm, so this is yy at binary64 and zmij's extension
    of it at the wider formats, which is where zmij runs this path. The
    extension is `packedBits` and nothing else: it makes the trim-down
    comparison four bits finer. -/
def toDecimal (f : ℕ) (e : FPExp fmt) : ℕ × ℤ :=
  let c := toDecimalCandidates f e
  (if c.roundD0 || c.roundU0 then c.decTen else c.decOne, c.k)

/-- The shift undoes the power-of-ten exponent: `h + 1 - pe = e`. Both sides
    scale the same fixed-point quotient, so once the shift is known not to have
    been clamped this is arithmetic, whatever the decimal exponent is — and
    whatever the constants are. -/
theorem exponent_shift_align (e : FPExp fmt) (hnn : 0 ≤ shiftRaw e) :
    (exponentShift e : ℤ) + 1
        - fmt.power10Exponent (-fmt.decimalExponent e) = e := by
  unfold exponentShift shiftRaw Format.power10Exponent at *
  omega

/-! ### The trim layer

yy's `roundD0` and `roundU0` compare the packed value `c` (the last decimal
digit of the integral part, followed by the top `width-4` bits of `sigLo`) with
`halfUlp`. Both sides are truncated at the same window unit `U`. With

    h = exponentShift e,      p10 = trimSig e,
    N = 10·2^(p10Width-h),    U = 2^(width+4-h),
    W = 2·f·p10 % N

one has `c = W / U`, `halfUlp = p10 / U`, `10·2^(width-4) = N / U`, and
`ten·2^(p10Width-h) + W = 2·f·p10`. Thus the two tests use only the pair
`(W, p10)` measured in units of `U`, and the boundary analysis becomes exact
integer arithmetic rather than an error estimate.

The quantities below clear the table's denominator, so that the same reasoning
holds of the exact power of ten rather than of its truncation, and the
difference between the two is one named error term `trimEdgeU`.
-/

/-- Numerator of the exact power of ten for the decimal exponent at `e`. -/
def trimNum (e : FPExp fmt) : ℕ := fmt.power10Num (-fmt.decimalExponent e)

/-- Denominator of that power of ten. -/
def trimDen (e : FPExp fmt) : ℕ := fmt.power10Den (-fmt.decimalExponent e)

/-- Its truncation to the table width, the `p10` of the comparisons. -/
def trimSig (e : FPExp fmt) : ℕ :=
  fmt.power10Significand (-fmt.decimalExponent e)

theorem trim_den_pos (e : FPExp fmt) : 0 < trimDen e := fmt.power10_den_pos _

theorem trim_sig_nat (e : FPExp fmt) : trimSig e = trimNum e / trimDen e :=
  fmt.power10_significand_nat _

/-- The table entry yy reads at `e` is normalized: a per-format check, since
    which indices the fixed-point exponent normalizes is a numerical fact about
    the format's constants. -/
def TableNormalized (e : FPExp fmt) : Prop :=
  2 ^ (fmt.p10Width - 1) * trimDen e ≤ trimNum e ∧
    trimNum e < 2 ^ fmt.p10Width * trimDen e

/-- Modulus of the packed comparison: the window wraps every 10·2^(2w-h). -/
def trimModulus (e : FPExp fmt) : ℕ := 10 * 2 ^ (fmt.p10Width - exponentShift e)

/-- One unit in the last place of the trim-up comparison, which reads the
    packed `c`. -/
def trimUnitU (e : FPExp fmt) : ℕ := 2 ^ (fmt.width + 4 - exponentShift e)

/-- One unit in the last place of the trim-down comparison: the trim-up unit
    shrunk by whatever bits the format leaves unpacked. -/
def trimUnit (e : FPExp fmt) : ℕ :=
  2 ^ (fmt.width + packedBits fmt - exponentShift e)

/-- The exact remainder above the candidate at step `m`. -/
def stepResidue (m f : ℕ) (e : FPExp fmt) : ℕ := 2 * f * trimSig e % m

/-- The remainder above the multiple-of-ten candidate. -/
def trimResidue (f : ℕ) (e : FPExp fmt) : ℕ := stepResidue (trimModulus e) f e

/-- `scaledSignificand` is the shifted product with its low `width` bits
    dropped. -/
theorem scaled_significand_eq (f : ℕ) (e : FPExp fmt) :
    scaledSignificand f e =
      2 ^ exponentShift e * (2 * f * trimSig e) / 2 ^ fmt.width := by
  show f * 2 ^ (exponentShift e + 1) * trimSig e / 2 ^ fmt.width = _
  congr 1
  rw [pow_succ]
  ring

/-- `sigHi` is the same product with `p10Width` bits dropped. -/
theorem sig_hi_eq (f : ℕ) (e : FPExp fmt) :
    sigHi f e
      = 2 ^ exponentShift e * (2 * f * trimSig e) / 2 ^ fmt.p10Width := by
  show scaledSignificand f e / 2 ^ fmt.width = _
  rw [scaled_significand_eq, Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  show fmt.width + fmt.width = 2 * fmt.width
  ring

/-- `sigLo` is the `width` bits between the two. -/
theorem sig_lo_eq (f : ℕ) (e : FPExp fmt) :
    sigLo f e
      = 2 ^ exponentShift e * (2 * f * trimSig e) % 2 ^ fmt.p10Width
          / 2 ^ fmt.width := by
  show scaledSignificand f e % 2 ^ fmt.width = _
  rw [scaled_significand_eq, ← Nat.mod_mul_right_div_self, ← pow_add]
  congr 3
  show fmt.width + fmt.width = 2 * fmt.width
  ring

/-- A power of two splits into the shift and what is left of the window. -/
theorem pow_shift_split (e : FPExp fmt) (n : ℕ) (hn : exponentShift e ≤ n) :
    (2 : ℕ) ^ n = 2 ^ exponentShift e * 2 ^ (n - exponentShift e) := by
  rw [← pow_add]
  congr 1
  omega

/-- Splitting a value at the table width and then discarding the low
    `width + j` bits is the same as discarding them directly; this is what packs
    the last digit into `c`, for whichever `j` bits stay packed. -/
theorem div_window (hl : Layout fmt) (j r : ℕ) (hj : j ≤ 4) :
    r / 2 ^ fmt.p10Width * 2 ^ (fmt.width - j) + r % 2 ^ fmt.p10Width
        / 2 ^ (fmt.width + j)
      = r / 2 ^ (fmt.width + j) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hsplit : (2 : ℕ) ^ fmt.p10Width
      = 2 ^ (fmt.width + j) * 2 ^ (fmt.width - j) := by
    rw [← pow_add]
    congr 1
    omega
  conv_rhs => rw [← Nat.div_add_mod r (2 ^ fmt.p10Width)]
  rw [hsplit, mul_assoc, Nat.mul_add_div (by positivity)]
  ring

/-- `halfUlp` is the power-of-ten significand truncated to the window unit. -/
theorem trim_half_ulp_eq (e : FPExp fmt) (hsh : exponentShift e < 4) :
    trimSig e / 2 ^ fmt.width / 2 ^ (4 - exponentShift e)
      = trimSig e / trimUnitU e := by
  rw [Nat.div_div_eq_div_mul, ← pow_add, trimUnitU,
    show fmt.width + (4 - exponentShift e)
      = fmt.width + 4 - exponentShift e from by omega]

/-- `c` is the window residue truncated to the unit of whichever comparison
    reads it, named by the `j` bits that comparison leaves packed. -/
theorem trim_c_at (hl : Layout fmt) (f : ℕ) (e : FPExp fmt) (j : ℕ)
    (hsh : exponentShift e < 4) (hj : j ≤ 4) :
    sigHi f e % 10 * 2 ^ (fmt.width - j) + sigLo f e / 2 ^ j
      = trimResidue f e / 2 ^ (fmt.width + j - exponentShift e) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  set h := exponentShift e with hh
  set z := 2 * f * trimSig e
  set r := 2 ^ h * z % (2 ^ fmt.p10Width * 10) with hr
  have hpos : 0 < (2 : ℕ) ^ h := by positivity
  have hunit : (2 : ℕ) ^ (fmt.width + j) = 2 ^ h * 2 ^ (fmt.width + j - h) := by
    rw [← pow_add]
    congr 1
    omega
  have hmodulus : (2 : ℕ) ^ fmt.p10Width * 10 = 2 ^ h * trimModulus e := by
    rw [trimModulus, ← hh, pow_shift_split e fmt.p10Width (by omega)]
    ring
  have hresidue : r = 2 ^ h * trimResidue f e := by
    rw [hr, hmodulus, Nat.mul_mod_mul_left]
    rfl
  have hscaled : trimResidue f e / 2 ^ (fmt.width + j - h)
      = r / 2 ^ (fmt.width + j) := by
    rw [hresidue, hunit, Nat.mul_div_mul_left _ _ hpos]
  have hhi : sigHi f e % 10 = r / 2 ^ fmt.p10Width := by
    rw [sig_hi_eq, hr, Nat.mod_mul_right_div_self]
  have hlo : sigLo f e / 2 ^ j
      = r % 2 ^ fmt.p10Width / 2 ^ (fmt.width + j) := by
    have hmod : 2 ^ h * z % 2 ^ fmt.p10Width = r % 2 ^ fmt.p10Width := by
      rw [hr, Nat.mod_mod_of_dvd _ ⟨10, rfl⟩]
    rw [sig_lo_eq, hmod, Nat.div_div_eq_div_mul, ← pow_add]
  rw [hhi, hlo, hscaled, div_window hl j _ hj]

/-- The trim-up comparison's instance, at the full digit slot. -/
theorem trim_c_eq (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    sigHi f e % 10 * 2 ^ (fmt.width - 4) + sigLo f e / 2 ^ 4
      = trimResidue f e / trimUnitU e :=
  trim_c_at hl f e 4 hsh (by omega)

/-- The trim-down comparison's, at whatever the format leaves packed. -/
theorem trim_c_down_eq (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    sigHi f e % 10 * 2 ^ (fmt.width - packedBits fmt)
        + sigLo f e / 2 ^ packedBits fmt
      = trimResidue f e / trimUnit e :=
  trim_c_at hl f e (packedBits fmt) hsh (packed_bits_le_four fmt)

/-- `sigHi` is the quotient at the unit step. -/
theorem sig_hi_quotient (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    sigHi f e
      = 2 * f * trimSig e / 2 ^ (fmt.p10Width - exponentShift e) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  rw [sig_hi_eq, pow_shift_split e fmt.p10Width (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

theorem sig_ten_quotient (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    sigTen f e = 10 * (2 * f * trimSig e / trimModulus e) := by
  rw [sigTen]
  have hdiv : sigHi f e / 10 = 2 * f * trimSig e / trimModulus e := by
    rw [sig_hi_quotient hl f e hsh, Nat.div_div_eq_div_mul,
      show 2 ^ (fmt.p10Width - exponentShift e) * 10 = trimModulus e from by
        rw [trimModulus]; ring]
  have hmod := Nat.div_add_mod (sigHi f e) 10
  rw [← hdiv]
  omega

/-! ### The gap and the checks

The two multiple-of-ten candidates are within half a ULP exactly when

    trim down:  W + (2f-1)·p10Exact ≤ 2·f·p10,
    trim up:    N + 2·f·p10 ≤ W + (2f+1)·p10Exact,

writing `p10Exact` for the exact power of ten `10^(-k)·2^(p10Width-pe)`, which
satisfies `p10 ≤ p10Exact < p10 + 1`. Substituting the window identity
`ten·2^(p10Width-h) + W = 2·f·p10` and `p10Exact·s = 2^(p10Width-h)`, and
writing `ten = 10·M`, both read as comparisons of the exact binary rounding
boundary with the decimal grid the trim targets:

    trim down:  2^(e-1)·(2f-1) ≤ M·10^(k+1),
    trim up:    (M+1)·10^(k+1) ≤ 2^(e-1)·(2f+1).

So the quantity to control is `Λ = M·10^(k+1) - 2^(e-1)·(2f∓1)`. Exact ties are
the case `Λ = 0`: since `2f∓1` is odd it carries no twos, so the boundary can
only land on `10^(k+1)·ℤ` when `e - 1 ≥ k + 1` supplies them, and the remaining
power of two is a unit modulo `5^(k+1)`, leaving the single residue class
`2f∓1 ≡ 0 (mod 5^(k+1))`—an arithmetic progression in `f`, not a magnitude
condition. With `2f∓1 < 2^(prec+1)` this needs `5^(k+1) < 2^(prec+1)`, so ties
exist only for small `k` (binary64: `k ≤ 22`); there the two bounds hold with
equality, which is exactly why the parity test turns them into `≤` for even `f`
and `<` for odd `f`. What must be ruled out is a near miss, `Λ ≠ 0` of the wrong
sign.

A magnitude bound cannot do that on its own. For `k ≥ 0` and `e ≥ k + 2`, both
terms of `Λ` are divisible by `2^(k+1)`, so the scaled defect is a multiple of
`2^(p10Width+1-h)/5^k` while the low-bits check only bounds it by `2^(width+5)`;
that forces `Λ = 0` only while the quantum stays above the uncertainty, which
fails not far past the tie threshold (binary64: `k ≤ 26`). Beyond that the
quantum is smaller than the uncertainty and the separation becomes genuinely
arithmetic, so the development below clears denominators instead. Writing
`num/den` for the exact power of ten and `τ = num % den`, the two bounds become

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

/-- The exact distance from a candidate to the scaled value, in the integer
    scale. -/
def stepGap (m f : ℕ) (e : FPExp fmt) : ℕ :=
  trimDen e * stepResidue m f e
    + 2 * f * (trimNum e % trimDen e)

def trimGap (f : ℕ) (e : FPExp fmt) : ℕ := stepGap (trimModulus e) f e

/-- The power-of-ten truncation error carried by the gap, `2·f·τ`. -/
def trimErr (f : ℕ) (e : FPExp fmt) : ℕ := 2 * f * (trimNum e % trimDen e)

theorem trim_gap_eq (f : ℕ) (e : FPExp fmt) :
    trimGap f e
      = trimDen e * trimResidue f e + trimErr f e := rfl

/-- The comparison's modulus in the integer scale. -/
def trimScale (e : FPExp fmt) : ℕ := trimModulus e * trimDen e

/-- One trim-up window unit in the integer scale. -/
def trimEdgeU (e : FPExp fmt) : ℕ := trimUnitU e * trimDen e

/-- The same for the trim-down comparison, at its own unit. -/
def trimEdge (e : FPExp fmt) : ℕ := trimUnit e * trimDen e

/-- Everything about the truncated power of ten that has to be checked per
    exponent, as one predicate so the kernel sweeps the range once.

    On `num`/`den` rather than the `trimSig` of `TrimChecks`: both reduce, but
    the `Nat.floor` over `ℚ` costs the kernel about twice as much. -/
def trimChecksHold (e : FPExp fmt) : Bool :=
  let num := trimNum e
  let den := trimDen e
  let lowD := num / den % trimUnit e
  let lowU := num / den % trimUnitU e
  decide (2 * (num / den) + 2 ≤ trimModulus e
    ∧ 2 ^ (fmt.prec + 1) * (num % den) ≤ lowD * den
    ∧ 2 ^ (fmt.prec + 1) * (num % den) + lowU * den ≤ trimUnitU e * den)

/-- The three checked facts for one exponent, with the truncation read back as
    `trimSig`. The second belongs to the trim-down comparison and the third to
    the trim-up one, so each is stated at its own unit. -/
def TrimChecks (e : FPExp fmt) : Prop :=
  2 * trimSig e + 2 ≤ trimModulus e
    ∧ 2 ^ (fmt.prec + 1) * (trimNum e % trimDen e)
        ≤ trimSig e % trimUnit e * trimDen e
    ∧ 2 ^ (fmt.prec + 1) * (trimNum e % trimDen e)
        + trimSig e % trimUnitU e * trimDen e
      ≤ trimUnitU e * trimDen e

/-- The Boolean sweep discharges the semantic form. -/
theorem trim_checks_of_hold (e : FPExp fmt) (hcert : trimChecksHold e = true) :
    TrimChecks e := by
  simp only [trimChecksHold, decide_eq_true_eq] at hcert
  rw [TrimChecks, trim_sig_nat]
  exact hcert

/-- The resolution of the packed comparison is negligible against the power of
    ten: `U ≤ 2^(w+4)` while `p10Exact ≥ 2^(2w-1)`. -/
theorem trim_two_edge_lt_num (hl : Layout fmt) (e : FPExp fmt)
    (hnorm : TableNormalized e) :
    2 * trimEdgeU e < trimNum e := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hu : trimUnitU e ≤ 2 ^ (fmt.width + 4) := by
    rw [trimUnitU]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hedge : trimEdgeU e ≤ 2 ^ (fmt.width + 4) * trimDen e := by
    rw [trimEdgeU]; exact Nat.mul_le_mul_right _ hu
  have hnum := hnorm.1
  have hden := trim_den_pos e
  -- `2·2^(w+4) = 2^(w+5) < 2^(2w-1)` is where the layout is used.
  have hgrow : 2 * 2 ^ (fmt.width + 4) < 2 ^ (fmt.p10Width - 1) := by
    rw [show 2 * (2 : ℕ) ^ (fmt.width + 4) = 2 ^ (fmt.width + 5) from by ring]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc 2 * trimEdgeU e ≤ 2 * (2 ^ (fmt.width + 4) * trimDen e) := by omega
    _ = 2 * 2 ^ (fmt.width + 4) * trimDen e := by ring
    _ < 2 ^ (fmt.p10Width - 1) * trimDen e :=
        mul_lt_mul_of_pos_right hgrow hden
    _ ≤ trimNum e := hnum

theorem trim_unit_u_pos (e : FPExp fmt) : 0 < trimUnitU e := by
  rw [trimUnitU]; positivity

theorem trim_unit_pos (e : FPExp fmt) : 0 < trimUnit e := by
  rw [trimUnit]; positivity

/-- The trim-down comparison never leaves more packed, so its edge never
    exceeds the trim-up one and a bound stated there covers both. -/
theorem trim_edge_le_edge_u (e : FPExp fmt) : trimEdge e ≤ trimEdgeU e := by
  have hj := packed_bits_le_four fmt
  rw [trimEdge, trimEdgeU]
  exact Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `2·f < 2^(prec+1)` for a regular significand, the bound the truncation error
    is measured against. Its own lemma because `omega` sees `2^prec` and
    `2^(prec+1)` as unrelated atoms; `pow_succ` is what relates them. -/
theorem two_sig_lt {f : ℕ} {e : ℤ} (hr : fmt.Regular f e) :
    2 * f < 2 ^ (fmt.prec + 1) := by
  have := hr.sig_lt
  rw [pow_succ]
  omega

/-- `den·p10 + τ = num`: the truncated power of ten and the bits it dropped. -/
theorem trim_num_split (e : FPExp fmt) :
    trimDen e * trimSig e + trimNum e % trimDen e
      = trimNum e := by
  rw [trim_sig_nat]; exact Nat.div_add_mod _ _

/-- One ULP of the value is narrower than one step of the coarse decimal grid:
    `2·num < scale`. This depends on the low bits of the truncated power of ten,
    not just its magnitude, so it is checked for each exponent. -/
theorem trim_two_num_lt_scale (e : FPExp fmt) (hc : TrimChecks e) :
    2 * trimNum e < trimScale e := by
  have hstep : trimDen e * (2 * trimSig e + 2)
      ≤ trimDen e * trimModulus e := Nat.mul_le_mul_left _ hc.1
  have hexp : trimDen e * (2 * trimSig e + 2)
      = 2 * (trimDen e * trimSig e) + 2 * trimDen e := by ring
  have hsplit := trim_num_split e
  have hscale : trimDen e * trimModulus e = trimScale e := by
    rw [trimScale]; ring
  have hmod : trimNum e % trimDen e < trimDen e :=
    Nat.mod_lt _ (trim_den_pos e)
  omega

/-- Whatever the step, the candidate scaled back up plus the gap is the scaled
    value `2·f·num`. -/
theorem step_quotient_add_gap (m f : ℕ) (e : FPExp fmt) :
    2 * f * trimSig e / m * (m * trimDen e) + stepGap m f e
      = 2 * f * trimNum e := by
  rw [stepGap, stepResidue]
  calc 2 * f * trimSig e / m * (m * trimDen e)
        + (trimDen e * (2 * f * trimSig e % m)
          + 2 * f * (trimNum e % trimDen e))
      = trimDen e * (m * (2 * f * trimSig e / m)
            + 2 * f * trimSig e % m)
          + 2 * f * (trimNum e % trimDen e) := by ring
    _ = 2 * f * (trimDen e * trimSig e
          + trimNum e % trimDen e) := by
        rw [Nat.div_add_mod]; ring
    _ = 2 * f * trimNum e := by rw [trim_num_split]

/-- The truncation error of the power of ten, `2·f·τ` with `τ < den`
    and `2·f < 2^(prec+1)`. -/
theorem trim_trunc_lt (f : ℕ) (e : FPExp fmt) (hr : fmt.Regular f e) :
    2 * f * (trimNum e % trimDen e)
      < 2 ^ (fmt.prec + 1) * trimDen e :=
  lt_of_le_of_lt (Nat.mul_le_mul_right _ (two_sig_lt hr).le)
    (mul_lt_mul_of_pos_left (Nat.mod_lt _ (trim_den_pos e)) (by positivity))

/-- At `k = 0` the power-of-ten significand is exactly `2^(2w-1)`, so it has no
    low bits for the truncation to drop. Concrete `decide` before; symbolically
    the exponent bookkeeping has to be done by hand. -/
theorem trim_power_ten_k_zero (hl : Layout fmt) (e : FPExp fmt)
    (hk : fmt.decimalExponent e = 0) :
    trimNum e = 2 ^ (fmt.p10Width - 1) * trimDen e
      ∧ trimSig e = 2 ^ (fmt.p10Width - 1) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hpe : fmt.power10Exponent 0 = 1 := by simp [Format.power10Exponent]
  have hden : trimDen e = 1 := by
    simp [trimDen, hk, Format.power10Den, hpe]
    omega
  have hnum : trimNum e = 2 ^ (fmt.p10Width - 1) := by
    simp [trimNum, hk, Format.power10Num, hpe]
    omega
  exact ⟨by rw [hnum, hden, mul_one],
    by rw [trim_sig_nat, hnum, hden, Nat.div_one]⟩

/-- The gap can overshoot the coarse step, but by less than `num`: the residue
    stays below the step and `num ≥ 2^(2w-1)·den` absorbs the truncation
    error. -/
theorem trim_gap_lt_scale_add (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (hnorm : TableNormalized e) :
    trimGap f e < trimScale e + trimNum e := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hres : trimDen e * trimResidue f e < trimScale e := by
    rw [trimResidue, stepResidue, trimScale, Nat.mul_comm (trimModulus e)]
    exact mul_lt_mul_of_pos_left
      (Nat.mod_lt _ (by rw [trimModulus]; positivity)) (trim_den_pos e)
  have hlow : trimErr f e < 2 ^ (fmt.prec + 1) * trimDen e :=
    trim_trunc_lt f e hr
  have htrunc : 2 ^ (fmt.prec + 1) * trimDen e ≤ trimNum e :=
    le_trans
      (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) (by have := hl.prec_le; omega)))
      hnorm.1
  rw [trim_gap_eq]
  omega

/-- What the trim-down comparison throws away, in the integer scale. -/
def trimDrop (e : FPExp fmt) : ℕ :=
  trimNum e % trimDen e + trimSig e % trimUnit e * trimDen e

/-- What the trim-up comparison throws away: the same shape at its own coarser
    unit, plus the low bits of the residue, which it truncates as well. -/
def trimDropU (f : ℕ) (e : FPExp fmt) : ℕ :=
  trimNum e % trimDen e + trimSig e % trimUnitU e * trimDen e
    + trimResidue f e % trimUnitU e * trimDen e

/-- Splitting two values at the window unit. -/
private theorem sum_split (den u w p : ℕ) :
    den * w + den * p
      = den * (w % u) + den * (p % u) + u * den * (w / u + p / u) := by
  calc den * w + den * p
      = den * (u * (w / u) + w % u) + den * (u * (p / u) + p % u) := by
        rw [Nat.div_add_mod, Nat.div_add_mod]
    _ = den * (w % u) + den * (p % u) + u * den * (w / u + p / u) := by ring

/-- The packed boundary `n` window units above `p10`, scaled: it differs from
    the exact boundary `num` by exactly the discarded bits. -/
theorem trim_packed_boundary (e : FPExp fmt) (n : ℕ) :
    trimDen e * ((trimSig e / trimUnit e + n) * trimUnit e)
        + trimDrop e
      = trimNum e + n * trimEdge e := by
  have hexp : trimDen e
        * ((trimSig e / trimUnit e + n) * trimUnit e)
      + (trimNum e % trimDen e
          + trimSig e % trimUnit e * trimDen e)
      = trimDen e * (trimUnit e * (trimSig e / trimUnit e)
          + trimSig e % trimUnit e) + trimNum e % trimDen e
        + n * (trimUnit e * trimDen e) := by ring
  rw [trimDrop, trimEdge, hexp, Nat.div_add_mod, trim_num_split]

/-- The trim-down comparison in exact quantities. `n = 0` is yy's strict test
    and `n = 1` its non-strict one, one window edge further out. -/
theorem trim_packed_iff (f : ℕ) (e : FPExp fmt) (n : ℕ) :
    trimResidue f e / trimUnit e < trimSig e / trimUnit e + n
      ↔ trimGap f e + trimDrop e
        < trimNum e + trimErr f e + n * trimEdge e := by
  have hb := trim_packed_boundary e n
  have hg := trim_gap_eq f e
  rw [Nat.div_lt_iff_lt_mul (trim_unit_pos e),
    show trimResidue f e
        < (trimSig e / trimUnit e + n) * trimUnit e
      ↔ trimDen e * trimResidue f e
        < trimDen e
          * ((trimSig e / trimUnit e + n) * trimUnit e) from
      (Nat.mul_lt_mul_left (trim_den_pos e)).symm]
  omega

/-- The trim-up comparison in exact quantities: the packed sum counts window
    edges below `gap + num`, and what it discards is `err + dropU`. -/
theorem trim_packed_sum (f : ℕ) (e : FPExp fmt) :
    trimGap f e + trimNum e
      = trimErr f e + trimDropU f e
        + trimEdgeU e
          * (trimResidue f e / trimUnitU e
            + trimSig e / trimUnitU e) := by
  have hsplit :=
    sum_split (trimDen e) (trimUnitU e) (trimResidue f e)
      (trimSig e)
  have hnum := trim_num_split e
  have hgap := trim_gap_eq f e
  have hw : trimDen e * (trimResidue f e % trimUnitU e)
      = trimResidue f e % trimUnitU e * trimDen e := by ring
  have hp : trimDen e * (trimSig e % trimUnitU e)
      = trimSig e % trimUnitU e * trimDen e := by ring
  rw [trimDropU, trimEdgeU]
  omega

/-- The coarse step is `10·2^(w-4)` window edges, the constant yy compares to:
    the modulus is that many window units. -/
theorem trim_scale_eq_edge (hl : Layout fmt) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    trimScale e = trimEdgeU e * (10 * 2 ^ (fmt.width - 4)) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  rw [trimScale, trimEdgeU, trimModulus, trimUnitU,
    show fmt.p10Width - exponentShift e
      = (fmt.width + 4 - exponentShift e) + (fmt.width - 4) from by omega,
    pow_add]
  ring

/-- The truncation error never exceeds the bits the trim-down comparison
    discards: that is what the low-bits half of `TrimChecks` certifies, per
    exponent. -/
theorem trim_err_le_drop (f : ℕ) (e : FPExp fmt) (hr : fmt.Regular f e)
    (hc : TrimChecks e) : trimErr f e ≤ trimDrop e := by
  have hbig : trimErr f e
      ≤ 2 ^ (fmt.prec + 1) * (trimNum e % trimDen e) :=
    Nat.mul_le_mul_right _ (two_sig_lt hr).le
  have hlow := hc.2.1
  rw [trimDrop]
  omega

/-- One window unit above the truncation error is more than the trim-down
    comparison discards: `τ < den` and the low bits of `p10` are below `U`. -/
theorem trim_drop_lt_err_add_edge (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) :
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
    the high-bits half of `TrimChecks` is needed. -/
theorem trim_err_drop_u_lt (f : ℕ) (e : FPExp fmt) (hr : fmt.Regular f e)
    (hc : TrimChecks e) :
    trimErr f e + trimDropU f e < 2 * trimEdgeU e := by
  have hbig : trimErr f e
      ≤ 2 ^ (fmt.prec + 1) * (trimNum e % trimDen e) :=
    Nat.mul_le_mul_right _ (two_sig_lt hr).le
  have hhigh := hc.2.2
  have hτ : trimNum e % trimDen e < trimDen e :=
    Nat.mod_lt _ (trim_den_pos e)
  have hres : trimResidue f e % trimUnitU e * trimDen e
      + trimDen e ≤ trimUnitU e * trimDen e :=
    calc trimResidue f e % trimUnitU e * trimDen e + trimDen e
        = (trimResidue f e % trimUnitU e + 1) * trimDen e := by ring
      _ ≤ trimUnitU e * trimDen e :=
        Nat.mul_le_mul_right _ (Nat.mod_lt _ (trim_unit_u_pos e))
  rw [trimDropU, trimEdgeU]
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
`den·U`, a relative width of `U/N ≈ 2^-(width-1)`. This is where verify.py
counts solutions with `floor_sum`; here a refutation certificate reaches the
same conclusion with one small check per window.

A Nadezhin-style separation, as used in Schubfach, still bottoms out in a finite
Diophantine check over the significand range, and fits yy less closely than the
modular windows below.

`expWindows` is stated against the format, so the same definition poses the
question at either width. The answer need not be a certificate, though:
`ExpAvoids` below is the per-significand form of it, which is what lets
binary128's one occupied window be handled at all.
-/

/-- Scaling the window residue by `den` and adding back the truncation error
    `2·f·τ` preserves the residue modulo `n·den`, provided the sum has not
    wrapped. -/
theorem mod_shift (p den τ n f : ℕ)
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

theorem trim_gap_mod (f : ℕ) (e : FPExp fmt) (hlt : trimGap f e < trimScale e) :
    2 * trimNum e * f % trimScale e = trimGap f e := by
  rw [trimGap, stepGap, stepResidue, trim_sig_nat, trimScale] at hlt ⊢
  rw [show 2 * trimNum e * f
      = 2 * (trimNum e / trimDen e * trimDen e
        + trimNum e % trimDen e) * f
      from by rw [Nat.div_add_mod']]
  exact mod_shift _ _ _ _ _ hlt

/-- The gaps the error bounds cannot decide: within one window edge of `num` or
    of `scale - num`, the two boundaries themselves excluded, plus the exact tie
    `scale - num` wherever the power of ten is exact and `k` is not zero. Each
    boundary takes the edge of the comparison that owns it, so the `num` bands
    are the narrower ones.

    Public, unlike before: the format's own file is what discharges the
    refutation obligation, so it has to be able to name the problem. -/
def expWindows (e : FPExp fmt) : ModWindows :=
  fmt.regularWindows (2 * trimNum e) (trimScale e) e <|
    let num : ℤ := trimNum e
    let edge : ℤ := trimEdge e
    let edgeU : ℤ := trimEdgeU e
    let scale : ℤ := trimScale e
    [(num - edge, num - 1), (num + 1, num + edge),
      (scale - num - edgeU, scale - num - 1),
      (scale - num + 1, scale - num + edgeU - 1)]
      ++ if trimNum e % trimDen e = 0 ∧ fmt.decimalExponent e ≠ 0 then
        [(scale - num, scale - num)]
      else []

/-- A gap landing in a refuted window is impossible: the gap is the residue of
    `2·num·f` modulo the window modulus, as long as it has not wrapped. -/
theorem exp_no_window_hit {lo hi q : ℤ} (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e)
    (hcert : (expWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (expWindows e).windows)
    (hwrap : trimGap f e < trimScale e)
    (hlo : lo ≤ (trimGap f e : ℤ)) (hhi : (trimGap f e : ℤ) ≤ hi) :
    False :=
  Format.regular_not_hit f hr
    (by rw [trimScale, trimModulus]
        exact Nat.mul_pos (by positivity) (trim_den_pos e))
    hcert hmem (trim_gap_mod f e hwrap).symm hlo hhi

/-- What a refuting multiplier buys at one significand: its gap misses every
    exceptional window. Stated per significand rather than as the certificate
    itself, so that an exponent whose box no single multiplier covers can reach
    the same conclusion another way. -/
def ExpAvoids (f : ℕ) (e : FPExp fmt) : Prop :=
  trimGap f e < trimScale e →
    ∀ lo hi : ℤ, (lo, hi) ∈ (expWindows e).windows →
      (trimGap f e : ℤ) < lo ∨ hi < (trimGap f e : ℤ)

/-- A certificate for the whole box gives it at every significand. -/
theorem exp_avoids_of_cert {q : ℤ} (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (hcert : (expWindows e).refutedBy q = true) :
    ExpAvoids f e := by
  intro hwrap lo hi hmem
  by_contra hcon
  push Not at hcon
  exact exp_no_window_hit f e hr hcert hmem hwrap hcon.1 hcon.2

/-! ### Recentring on an occupant

A multiplier can only refute a window that nothing occupies, and the refutation
is an interval hull, so shrinking the box around an occupant does not help
either: the hull barely moves and goes on trapping the same multiple. What does
work is to stop indexing the progression by the significand and index it by the
distance from the occupant instead. The occupant is then at distance zero,
outside every box, and the windows move with it, becoming signed offsets from
its own residue.

One certificate per side is still too much to ask — the hull spans the whole box
at a width that leaves no room — but the distances split into dyadic blocks, and
each block is a box small enough to refute. There are `prec` of them per side
and they are needed at one exponent, so the cost does not show.
-/

/-- The residue `expWindows` reads at a significand. -/
def expResidue (b : ℕ) (e : FPExp fmt) : ℕ := 2 * trimNum e * b % trimScale e

/-- `expWindows` seen by the significands a distance `2^i ≤ d < 2^(i+1)` above
    `b`, indexed by that distance and with the windows measured from `b`'s own
    residue. The block index comes last, where a certificate search expects to
    find the quantity it varies. -/
def expWindowsAbove (b : ℕ) (e : FPExp fmt) (i : ℕ) : ModWindows :=
  { expWindows e with
    f0 := 2 ^ i
    f1 := 2 ^ (i + 1) - 1
    windows := (expWindows e).windows.map fun p =>
      (p.1 - expResidue b e, p.2 - expResidue b e) }

/-- And by those below, where the distance runs the other way, so the offsets
    are negated. -/
def expWindowsBelow (b : ℕ) (e : FPExp fmt) (i : ℕ) : ModWindows :=
  { expWindows e with
    f0 := 2 ^ i
    f1 := 2 ^ (i + 1) - 1
    windows := (expWindows e).windows.map fun p =>
      (expResidue b e - p.2, expResidue b e - p.1) }

/-- Certificates for every block around `b` do what one for the whole box
    would, at every significand but `b` itself. -/
theorem exp_avoids_of_blocks {b : ℕ} (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (hne : f ≠ b) (hbp : b < 2 ^ fmt.prec)
    (ha : ∀ i < fmt.prec, ∃ q, (expWindowsAbove b e i).refutedBy q = true)
    (hb : ∀ i < fmt.prec, ∃ q, (expWindowsBelow b e i).refutedBy q = true) :
    ExpAvoids f e := by
  intro hwrap lo hi hmem
  by_contra hcon
  push Not at hcon
  obtain ⟨hlo, hhi⟩ := hcon
  have hfp : f < 2 ^ fmt.prec := hr.sig_lt
  have hmod : 0 < trimScale e := by
    rw [trimScale, trimModulus]
    exact Nat.mul_pos (by positivity) (trim_den_pos e)
  -- Both residues as offsets from their own multiple of the modulus, so that
  -- the difference of the two is the residue at the distance between them.
  have hyf : (trimGap f e : ℤ) = 2 * trimNum e * f
      - trimScale e * ((2 * trimNum e * f / trimScale e : ℕ) : ℤ) := by
    rw [← trim_gap_mod f e hwrap, cast_mod_eq_sub]
    push_cast
    ring
  have hyb : (expResidue b e : ℤ) = 2 * trimNum e * b
      - trimScale e * ((2 * trimNum e * b / trimScale e : ℕ) : ℤ) := by
    rw [expResidue, cast_mod_eq_sub]
    push_cast
    ring
  -- The distance and the block it falls in.
  have hblock : ∀ d : ℕ, d ≠ 0 → d < 2 ^ fmt.prec →
      Nat.log 2 d < fmt.prec ∧ 2 ^ Nat.log 2 d ≤ d
        ∧ d ≤ 2 ^ (Nat.log 2 d + 1) - 1 := by
    intro d hd0 hdp
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) d
    exact ⟨Nat.log_lt_of_lt_pow hd0 hdp, Nat.pow_log_le_self 2 hd0, by omega⟩
  rcases lt_trichotomy f b with hfb | hfb | hfb
  · obtain ⟨hip, hd0, hd1⟩ := hblock (b - f) (by omega) (by omega)
    obtain ⟨q, hcert⟩ := hb _ hip
    have hy : (expResidue b e : ℤ) - trimGap f e
        = ((2 * trimNum e : ℕ) : ℤ) * ((b - f : ℕ) : ℤ)
          - ((trimScale e : ℕ) : ℤ)
            * (((2 * trimNum e * b / trimScale e : ℕ) : ℤ)
              - ((2 * trimNum e * f / trimScale e : ℕ) : ℤ)) := by
      rw [show ((b - f : ℕ) : ℤ) = (b : ℤ) - f from by omega, hyf, hyb]
      push_cast
      ring
    exact (expWindowsBelow b e _).not_hit_rep (b - f) hmod hcert
      (lo := (expResidue b e : ℤ) - hi) (hi := (expResidue b e : ℤ) - lo)
      (List.mem_map_of_mem (f := fun p : ℤ × ℤ =>
        ((expResidue b e : ℤ) - p.2, (expResidue b e : ℤ) - p.1)) hmem)
      hd0 hd1 hy (by omega) (by omega)
  · exact hne hfb
  · obtain ⟨hip, hd0, hd1⟩ := hblock (f - b) (by omega) (by omega)
    obtain ⟨q, hcert⟩ := ha _ hip
    have hy : (trimGap f e : ℤ) - expResidue b e
        = ((2 * trimNum e : ℕ) : ℤ) * ((f - b : ℕ) : ℤ)
          - ((trimScale e : ℕ) : ℤ)
            * (((2 * trimNum e * f / trimScale e : ℕ) : ℤ)
              - ((2 * trimNum e * b / trimScale e : ℕ) : ℤ)) := by
      rw [show ((f - b : ℕ) : ℤ) = (f : ℤ) - b from by omega, hyf, hyb]
      push_cast
      ring
    exact (expWindowsAbove b e _).not_hit_rep (f - b) hmod hcert
      (lo := lo - (expResidue b e : ℤ)) (hi := hi - (expResidue b e : ℤ))
      (List.mem_map_of_mem (f := fun p : ℤ × ℤ =>
        (p.1 - (expResidue b e : ℤ), p.2 - (expResidue b e : ℤ))) hmem)
      hd0 hd1 hy (by omega) (by omega)

/-- The undecided bands of the unit step, as windows on the doubled residue.
    The truncation error is below `2^(prec+1)·den`, so `2^(prec+1)` bounds its
    reach in remainder units.

    Defined here, before the unit-step development that motivates it, so that
    `ChecksAt` below can name both refutation obligations at once. -/
def oneWindows (e : FPExp fmt) : ModWindows :=
  fmt.regularWindows (2 * trimSig e)
      (2 ^ (fmt.p10Width + 1 - exponentShift e)) e <|
    let half : ℤ := 2 ^ (fmt.p10Width - 1 - exponentShift e)
    let band : ℤ := 2 ^ (fmt.width - exponentShift e)
    let w : ℤ := 2 ^ (fmt.p10Width - exponentShift e)
    -- The packed tie band above the midpoint, for an even `sigHi`.
    (half + 1, half + band - 1) ::
      if trimNum e % trimDen e = 0 then []
      else
        -- The midpoint, which only an even `sigHi` reaches wrongly, and the
        -- truncation error's reach below it, which either parity reaches.
        [(half - 2 ^ (fmt.prec + 1), half),
          (w + half - 2 ^ (fmt.prec + 1), w + half - 1)]

/-- What the exceptional windows exist to establish: at `f`, both trim
    comparisons decide what the exact ones do. A significand no certificate
    excludes has to supply this directly, which at a concrete exponent and
    significand is a closed computation. -/
def TrimsAgree (f : ℕ) (e : FPExp fmt) : Prop :=
  ((toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then trimGap f e ≤ trimNum e
        else trimGap f e < trimNum e)
    ∧ ((toDecimalCandidates f e).roundU0 = true
      ↔ if f % 2 = 0 then trimScale e ≤ trimGap f e + trimNum e
        else trimScale e < trimGap f e + trimNum e)

/-- Everything that has to hold of a format at one exponent for yy to be
    correct there. Every field is a numerical fact about the format's constants
    at that exponent, so a format discharges them by sweeping its range; none of
    them is algebra, and none can be derived from the layout.

    The two `_refuted` fields are the expensive ones: one modular certificate
    each, and there is one of these records per exponent. -/
structure ChecksAt (e : FPExp fmt) : Prop where
  /-- `Int.toNat` does not clamp the shift. -/
  shift_nonneg : 0 ≤ shiftRaw e
  /-- The shift leaves the four-bit digit slot intact. -/
  shift_lt_four : exponentShift e < 4
  /-- The table entry read at `e` is normalized. -/
  table : TableNormalized e
  /-- The truncated power of ten is narrow, and its error fits the bits the
      packed comparison discards, from either end of the window unit. -/
  trim : TrimChecks e
  /-- Every significand either misses the coarse windows either side of both
      boundaries, or is one no certificate excludes and decides correctly
      anyway. -/
  exp_refuted : ∀ f, fmt.Regular f e → ExpAvoids f e ∨ TrimsAgree f e
  /-- The unit-step bands around the midpoint are empty. -/
  one_refuted : ∃ q, (oneWindows e).refutedBy q = true

/-- The per-format obligation: `ChecksAt` at every exponent of the format's
    range. The domain is the format's own, so a format cannot discharge this
    over an interval smaller than the one `Regular` admits. -/
def Checks (fmt : Format) : Prop :=
  ∀ e : FPExp fmt, fmt.emin ≤ e → e ≤ fmt.emax → ChecksAt e

/-- Either the gap sits exactly on a boundary, a genuine exact tie, or it is
    outside the windows either side of it, where the packed comparison cannot be
    wrong. -/
private theorem gap_tie_or_far {b hi edge : ℤ} (f : ℕ) (e : FPExp fmt)
    (havoid : ExpAvoids f e)
    (hcap : hi < (trimScale e : ℤ))
    (hbelow : (b - edge, b - 1) ∈ (expWindows e).windows)
    (habove : (b + 1, hi) ∈ (expWindows e).windows) :
    (trimGap f e : ℤ) = b ∨ hi < (trimGap f e : ℤ)
      ∨ (trimGap f e : ℤ) + edge < b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hhi, hlo⟩ := hcon
  have hwrap : trimGap f e < trimScale e := by omega
  rcases lt_or_ge (trimGap f e : ℤ) b with h | h
  · rcases havoid hwrap _ _ hbelow with hx | hx <;> omega
  · rcases havoid hwrap _ _ habove with hx | hx <;> omega

/-- The trim-down dichotomy, about the boundary `num`. -/
theorem d0_gap_tie_or_far (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hnorm : TableNormalized e) (hc : TrimChecks e)
    (havoid : ExpAvoids f e) :
    trimGap f e = trimNum e
      ∨ trimNum e + trimEdge e < trimGap f e
      ∨ trimGap f e + trimEdge e < trimNum e := by
  have hedge := trim_two_edge_lt_num hl e hnorm
  have hle := trim_edge_le_edge_u e
  have hnarrow := trim_two_num_lt_scale e hc
  have := gap_tie_or_far (b := (trimNum e : ℤ)) (edge := (trimEdge e : ℤ))
    (hi := (trimNum e : ℤ) + trimEdge e) f e havoid (by omega)
    (by simp [expWindows, Format.regularWindows])
    (by simp [expWindows, Format.regularWindows])
  omega

/-- The trim-up dichotomy, the same statement about the boundary
    `scale - num`. -/
theorem u0_sum_tie_or_far (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hnorm : TableNormalized e) (hc : TrimChecks e)
    (havoid : ExpAvoids f e) :
    trimGap f e + trimNum e = trimScale e
      ∨ trimScale e + trimEdgeU e ≤ trimGap f e + trimNum e
      ∨ trimGap f e + trimNum e + trimEdgeU e < trimScale e := by
  have hedge := trim_two_edge_lt_num hl e hnorm
  have hnarrow := trim_two_num_lt_scale e hc
  have := gap_tie_or_far (b := (trimScale e : ℤ) - trimNum e)
    (edge := (trimEdgeU e : ℤ))
    (hi := (trimScale e : ℤ) - trimNum e + trimEdgeU e - 1) f e
    havoid (by omega)
    (by simp [expWindows, Format.regularWindows])
    (by simp [expWindows, Format.regularWindows])
  omega

/-- An exact tie in the trim-up comparison needs `k = 0` when the power of ten
    is exact: that is the residue the fifth window refutes elsewhere. -/
theorem u0_exact_tie_k_zero (f : ℕ) (e : FPExp fmt)
    (hnorm : TableNormalized e) (havoid : ExpAvoids f e)
    (hτ : trimNum e % trimDen e = 0)
    (htie : trimGap f e + trimNum e = trimScale e) :
    fmt.decimalExponent e = 0 := by
  by_contra hk
  have hnum : 0 < trimNum e :=
    lt_of_lt_of_le (Nat.mul_pos (by positivity) (trim_den_pos e)) hnorm.1
  -- The fifth window is present exactly under these two hypotheses.
  have hmem : ((trimScale e : ℤ) - trimNum e,
      (trimScale e : ℤ) - trimNum e) ∈ (expWindows e).windows := by
    refine List.mem_append_right _ ?_
    rw [ite_eq_left ⟨hτ, hk⟩]
    exact List.mem_singleton_self _
  rcases havoid (by omega) _ _ hmem with hx | hx <;> omega

/-- At `k = 0` the power of ten is exactly `2^(2w-1)`, a whole number of window
    units, so the trim-up comparison discards nothing and its ties are exact. -/
theorem u0_err_drop_u_k_zero (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) (hk : fmt.decimalExponent e = 0) :
    trimErr f e + trimDropU f e = 0 := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  obtain ⟨hnum, hsig⟩ := trim_power_ten_k_zero hl e hk
  have hunit : trimUnitU e ∣ trimSig e := by
    rw [hsig, trimUnitU]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨cp, hcp⟩ := hunit
  obtain ⟨cw, hcw⟩ : trimUnitU e ∣ trimResidue f e := by
    refine (Nat.dvd_mod_iff ?_).mpr (Dvd.dvd.mul_left ⟨cp, hcp⟩ _)
    rw [trimModulus, trimUnitU]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) 10
  have hτ : trimNum e % trimDen e = 0 := by rw [hnum, Nat.mul_mod_left]
  rw [trimErr, trimDropU, hτ, hcp, hcw]
  simp

/-- The trim-up comparison sees an exact tie only where the power of ten is
    exact, and that needs `k = 0`. -/
theorem u0_tie_k_zero (f : ℕ) (e : FPExp fmt) (hr : fmt.Regular f e)
    (hnorm : TableNormalized e) (havoid : ExpAvoids f e)
    (hzero : trimErr f e + trimDropU f e = 0)
    (htie : trimGap f e + trimNum e = trimScale e) :
    fmt.decimalExponent e = 0 := by
  have herr : 2 * f * (trimNum e % trimDen e) = 0 := by
    rw [trimErr] at hzero; omega
  rcases Nat.mul_eq_zero.mp herr with h | h
  · have := hr.pos; omega
  · exact u0_exact_tie_k_zero f e hnorm havoid h htie

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

/-- The unit step, in integers. The coarse step is ten of them. -/
def trimMul (e : FPExp fmt) : ℕ :=
  2 ^ (fmt.p10Width - exponentShift e) * trimDen e

theorem trim_mul_pos (e : FPExp fmt) : 0 < trimMul e := by
  rw [trimMul]
  exact Nat.mul_pos (by positivity) (trim_den_pos e)

theorem trim_scale_eq_ten_mul (e : FPExp fmt) :
    trimScale e = 10 * trimMul e := by
  simp only [trimScale, trimMul, trimModulus]
  ring

/-- Twice the bound on the power-of-ten truncation error fits inside one grid
    step: `trimMul ≥ 2^(2w-3)·den`, while the doubled bound is
    `2^(prec+2)·den`. -/
theorem trim_two_trunc_le_mul (hl : Layout fmt) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    2 ^ (fmt.prec + 2) * trimDen e ≤ trimMul e := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have := hl.prec_le
  rw [trimMul]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Half a grid step, in integers: half a unit step times `den`. -/
theorem trim_mul_eq_two_half (hl : Layout fmt) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    trimMul e
      = 2 * (trimDen e * 2 ^ (fmt.p10Width - 1 - exponentShift e)) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  rw [trimMul, show (2 : ℕ) ^ (fmt.p10Width - exponentShift e)
      = 2 * 2 ^ (fmt.p10Width - 1 - exponentShift e) from by
    rw [← pow_succ']; congr 1; omega]
  ring

/-- `trimMul` clears the denominator in `power10_exact_ratio`, leaving `trimNum`
    times the binary-decimal scaling factor. -/
theorem trim_mul_eq (hl : Layout fmt) (e : FPExp fmt) (hnn : 0 ≤ shiftRaw e)
    (hsh : exponentShift e < 4) :
    (trimMul e : ℚ)
      = (trimNum e : ℚ)
        * (2 ^ (1 - e.val) * 10 ^ fmt.decimalExponent e) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  set k := fmt.decimalExponent e
  set pe := fmt.power10Exponent (-k)
  have hd : (0 : ℚ) < (trimDen e : ℚ) := by
    exact_mod_cast trim_den_pos e
  have hnum : (10 : ℚ) ^ (-k) * 2 ^ ((fmt.p10Width : ℤ) - pe) * trimDen e
      = trimNum e := by
    rw [fmt.power10_exact_ratio, ← trimNum, ← trimDen,
      div_mul_cancel₀ _ (ne_of_gt hd)]
  -- The inverse scale `s = 2^(1-e)·10^k` turns the power-of-ten factor into
  -- `2^(2w-h)`, which is where the shift alignment is spent.
  have hscale : (10 : ℚ) ^ (-k) * 2 ^ ((fmt.p10Width : ℤ) - pe)
        * (2 ^ (1 - e.val) * 10 ^ k)
      = 2 ^ (fmt.p10Width - exponentShift e) := by
    have h10 : (10 : ℚ) ^ (-k) * 10 ^ k = 1 := by
      rw [← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]; simp
    have halign : (exponentShift e : ℤ) + 1 - pe = e :=
      exponent_shift_align e hnn
    calc (10 : ℚ) ^ (-k) * 2 ^ ((fmt.p10Width : ℤ) - pe)
          * (2 ^ (1 - e.val) * 10 ^ k)
        = (10 ^ (-k) * 10 ^ k)
            * (2 ^ ((fmt.p10Width : ℤ) - pe) * 2 ^ (1 - e.val)) := by ring
      _ = (2 : ℚ) ^ (((fmt.p10Width : ℤ) - pe) + (1 - e)) := by
          rw [h10, one_mul, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
      _ = 2 ^ (fmt.p10Width - exponentShift e) := by
          rw [show ((fmt.p10Width : ℤ) - pe) + (1 - e)
                = ((fmt.p10Width - exponentShift e : ℕ) : ℤ) from by omega,
            zpow_natCast]
  rw [trimMul]
  push_cast
  rw [← hscale, ← hnum]
  ring

/-- The scale sends half a scaled ULP to `trimNum`. -/
theorem trim_mul_half_ulp (hl : Layout fmt) (e : FPExp fmt)
    (hnn : 0 ≤ shiftRaw e) (hsh : exponentShift e < 4) :
    let k := fmt.decimalExponent e
    ulp e * 10 ^ (-k) / 2 * (trimMul e : ℚ) = (trimNum e : ℚ) := by
  intro k
  calc ulp e * 10 ^ (-k) / 2 * (trimMul e : ℚ)
      = (trimNum e : ℚ) * (2 ^ e.val * 2 ^ (1 - e.val) / 2)
          * (10 ^ (-k) * 10 ^ k) := by
        rw [ulp, trim_mul_eq hl e hnn hsh]; ring
    _ = (trimNum e : ℚ) := by
        rw [← zpow_add₀ (two_ne_zero' ℚ) e (1 - e),
          show e.val + (1 - e.val) = 1 from by ring, zpow_one,
          ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0) (-k) k,
          show -k + k = 0 from by ring, zpow_zero]
        ring

/-- The one yy-specific fact the generic bridge needs: `trimMul` sends the
    scaled value to the integer `2·f·num`. -/
theorem trim_value_scaled (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hnn : 0 ≤ shiftRaw e) (hsh : exponentShift e < 4) :
    value f e * 10 ^ (-fmt.decimalExponent e) * (trimMul e : ℚ)
      = ((2 * f * trimNum e : ℤ) : ℚ) := by
  push_cast
  rw [← trim_mul_half_ulp hl e hnn hsh, value, ulp]
  ring

/-- Half a ULP is worth `trimNum` in one copy of the scale. -/
theorem trim_half_ulp_scaled (hl : Layout fmt) (e : FPExp fmt)
    (hnn : 0 ≤ shiftRaw e) (hsh : exponentShift e < 4) :
    ulp e * 10 ^ (-fmt.decimalExponent e) / 2
        * ((1 : ℕ) * (trimMul e : ℚ))
      = ((trimNum e : ℕ) : ℚ) := by
  rw [Nat.cast_one, one_mul]
  exact trim_mul_half_ulp hl e hnn hsh

/-- A candidate round-trips exactly when its signed distance stays within
    `trimNum`, strictly so for odd `f`. -/
theorem roundtrips_iff_dist (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hnn : 0 ≤ shiftRaw e) (hsh : exponentShift e < 4) {c : ℕ}
    {dist : ℤ}
    (hc : (c : ℤ) * trimMul e + dist = 2 * f * trimNum e) :
    Roundtrips f e (c * 10 ^ fmt.decimalExponent e)
      ↔ if f % 2 = 0 then
          -(trimNum e : ℤ) ≤ dist ∧ dist ≤ trimNum e
        else -(trimNum e : ℤ) < dist ∧ dist < trimNum e := by
  obtain ⟨hle, hlt, -⟩ := scaled_cmp_of_int_eq (trim_mul_pos e) one_pos
    (trim_value_scaled hl f e hnn hsh)
    (trim_half_ulp_scaled hl e hnn hsh) hc
  refine (roundtrips_iff_scaled f e (fmt.decimalExponent e) c).trans ?_
  split_ifs
  · exact hle.trans (by omega)
  · exact hlt.trans (by omega)

/-- The trim-down candidate sits `trimGap` below the scaled value. -/
theorem dec_ten_down_scaled (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    (sigTen f e : ℤ) * trimMul e + trimGap f e
      = 2 * f * trimNum e := by
  have h : sigTen f e * trimMul e + trimGap f e
      = 2 * f * trimNum e :=
    calc sigTen f e * trimMul e + trimGap f e
        = 2 * f * trimSig e / trimModulus e * trimScale e
            + trimGap f e := by
          rw [sig_ten_quotient hl f e hsh, trim_scale_eq_ten_mul]
          ring
      _ = 2 * f * trimNum e := step_quotient_add_gap _ f e
  exact_mod_cast h

/-- The trim-up candidate sits `trimScale - trimGap` above it. -/
theorem dec_ten_up_scaled (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    ((sigTen f e + 10 : ℕ) : ℤ) * trimMul e
        + ((trimGap f e : ℤ) - trimScale e)
      = 2 * f * trimNum e := by
  have hten : (trimScale e : ℤ) = 10 * trimMul e := by
    exact_mod_cast trim_scale_eq_ten_mul e
  push_cast
  linear_combination dec_ten_down_scaled hl f e hsh - hten

/-- One ULP spans `[1, 10)` grid steps at yy's exponent. -/
theorem ulp_scaled_bounds (hl : Layout fmt) (e : FPExp fmt) (ha : ChecksAt e) :
    1 ≤ ulp e * 10 ^ (-fmt.decimalExponent e) ∧
      ulp e * 10 ^ (-fmt.decimalExponent e) < 10 := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hlow : trimMul e ≤ 2 * trimNum e := by
    have h1 : trimMul e ≤ 2 ^ fmt.p10Width * trimDen e := by
      rw [trimMul]
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 := ha.table.1
    -- `omega` cannot multiply a power identity through by `den`, so it is
    -- stated already multiplied.
    have h3 : (2 : ℕ) ^ fmt.p10Width * trimDen e
        = 2 * (2 ^ (fmt.p10Width - 1) * trimDen e) := by
      rw [show (2 : ℕ) ^ fmt.p10Width = 2 * 2 ^ (fmt.p10Width - 1) from by
        rw [← pow_succ']; congr 1; omega]
      ring
    omega
  have hhigh := trim_two_num_lt_scale e ha.trim
  rw [trim_scale_eq_ten_mul] at hhigh
  exact ulp_steps_of_int_eq (t := 2 * trimNum e) (trim_mul_pos e)
    (by push_cast
        linear_combination
          2 * trim_mul_half_ulp hl e ha.shift_nonneg ha.shift_lt_four)
    hlow hhigh

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
theorem round_d0_iff_gap (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    (toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then trimGap f e ≤ trimNum e
        else trimGap f e < trimNum e := by
  have hsh := ha.shift_lt_four
  rcases ha.exp_refuted f hr with havoid | hagree
  swap
  · exact hagree.1
  -- yy's test is `c ≤ p` for even `f` and `c < p` for odd `f`, that is
  -- `c < p + 1` and `c < p + 0`.
  have hflag : (toDecimalCandidates f e).roundD0
      = if trimSig e / trimUnit e = trimResidue f e / trimUnit e
        then decide (f % 2 = 0)
        else decide (trimResidue f e / trimUnit e
          < trimSig e / trimUnit e) := by
    rw [← trim_c_down_eq hl f e hsh]
    rfl
  have hpacked : (toDecimalCandidates f e).roundD0 = true
      ↔ if f % 2 = 0 then
          trimResidue f e / trimUnit e
            < trimSig e / trimUnit e + 1
        else trimResidue f e / trimUnit e
          < trimSig e / trimUnit e + 0 := by
    rw [hflag]
    split_ifs <;> simp only [decide_eq_true_eq] <;> omega
  rw [hpacked, trim_packed_iff, trim_packed_iff]
  have herr := trim_err_le_drop f e hr ha.trim
  have hdrop := trim_drop_lt_err_add_edge f e hr
  rcases d0_gap_tie_or_far hl f e ha.table ha.trim havoid with
    htie | hfar
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
      exact (comparison_stable_of_far (l := trimDrop e)
        (r := trimErr f e) (w := trimEdge e)
        (by omega) (by omega) hfar).2

/-- `roundD0` fires exactly when the trim-down candidate round-trips. -/
theorem round_d0_iff_roundtrips (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    (toDecimalCandidates f e).roundD0 = true
      ↔ Roundtrips f e (sigTen f e * 10 ^ fmt.decimalExponent e) := by
  rw [round_d0_iff_gap hl f e hr ha,
    roundtrips_iff_dist hl f e ha.shift_nonneg ha.shift_lt_four
      (dec_ten_down_scaled hl f e ha.shift_lt_four)]
  split_ifs <;> omega

/-! ### The trim-up decision -/

/-- What `roundU0` decides. The packed sum `s` counts window edges below
    `gap + num`, and the coarse step is `10·2^(w-4)` of them. -/
theorem round_u0_iff_gap (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    (toDecimalCandidates f e).roundU0 = true
      ↔ if f % 2 = 0 then trimScale e ≤ trimGap f e + trimNum e
        else trimScale e < trimGap f e + trimNum e := by
  have hsh := ha.shift_lt_four
  rcases ha.exp_refuted f hr with havoid | hagree
  swap
  · exact hagree.2
  have hflag : (toDecimalCandidates f e).roundU0
      = (if trimResidue f e / trimUnitU e
              + trimSig e / trimUnitU e + 1
            = 10 * 2 ^ (fmt.width - 4) then decide (f % 2 = 0)
        else if fmt.decimalExponent e = 0
            ∧ trimResidue f e / trimUnitU e
              + trimSig e / trimUnitU e
              = 10 * 2 ^ (fmt.width - 4) then decide (f % 2 = 0)
        else decide (10 * 2 ^ (fmt.width - 4)
          ≤ trimResidue f e / trimUnitU e
            + trimSig e / trimUnitU e)) := by
    rw [← trim_c_eq hl f e hsh, ← trim_half_ulp_eq e hsh]
    rfl
  have hid := trim_packed_sum f e
  have hD := trim_err_drop_u_lt f e hr ha.trim
  have hscale := trim_scale_eq_edge hl e hsh
  have hE : 0 < trimEdgeU e :=
    Nat.mul_pos (trim_unit_u_pos e) (trim_den_pos e)
  rw [hflag]
  set s := trimResidue f e / trimUnitU e
    + trimSig e / trimUnitU e with hs
  rcases u0_sum_tie_or_far hl f e ha.table ha.trim havoid with
    htie | hhi | hlo
  -- An exact tie: the packed sum is either one edge short of the step or
  -- exactly on it with nothing discarded, both branches yy takes for even `f`.
  · have hle : s ≤ 10 * 2 ^ (fmt.width - 4) :=
      Nat.le_of_mul_le_mul_left (by omega) hE
    have hnear : 10 * 2 ^ (fmt.width - 4) < s + 2 := by
      have hexp : trimEdgeU e * (s + 2)
          = trimEdgeU e * s + 2 * trimEdgeU e := by ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdgeU e) (by omega)
    rcases Nat.lt_or_ge s (10 * 2 ^ (fmt.width - 4)) with hlt | hge
    · rw [ite_eq_left (by omega)]
      split_ifs with hpar <;> simp only [decide_eq_true_eq] <;> omega
    · have heq : s = 10 * 2 ^ (fmt.width - 4) := by omega
      rw [heq] at hid
      rw [ite_eq_right (by omega), ite_eq_left
        ⟨u0_tie_k_zero f e hr ha.table havoid (by omega) htie, heq⟩]
      split_ifs with hpar <;> simp only [decide_eq_true_eq] <;> omega
  -- More than one edge above the boundary, so the plain test fires.
  · have hge : 10 * 2 ^ (fmt.width - 4) < s + 1 := by
      have hexp : trimEdgeU e * (s + 1)
          = trimEdgeU e * s + trimEdgeU e := by ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdgeU e) (by omega)
    have hnot : ¬(fmt.decimalExponent e = 0
        ∧ s = 10 * 2 ^ (fmt.width - 4)) := by
      rintro ⟨hk, heq⟩
      have hzero := u0_err_drop_u_k_zero hl f e hsh hk
      rw [heq] at hid
      omega
    rw [ite_eq_right (by omega), ite_eq_right hnot]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  -- More than one edge below it, so even `s + 1` falls short.
  · have hlt : s + 1 < 10 * 2 ^ (fmt.width - 4) := by
      have hexp : trimEdgeU e * (s + 1)
          = trimEdgeU e * s + trimEdgeU e := by ring
      exact Nat.lt_of_mul_lt_mul_left (a := trimEdgeU e) (by omega)
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega

/-- `roundU0` fires exactly when the trim-up candidate round-trips. -/
theorem round_u0_iff_roundtrips (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    (toDecimalCandidates f e).roundU0 = true
      ↔ Roundtrips f e
        ((sigTen f e + 10 : ℕ) * 10 ^ fmt.decimalExponent e) := by
  have hroom := trim_gap_lt_scale_add hl f e hr ha.table
  rw [round_u0_iff_gap hl f e hr ha,
    roundtrips_iff_dist hl f e ha.shift_nonneg ha.shift_lt_four
      (dec_ten_up_scaled hl f e ha.shift_lt_four)]
  split_ifs <;> omega

/-! ## The unit-step decision

`decOne` is `sigHi` rounded to nearest using the discarded `sigLo`. In
the scale `trimMul = 2^(p10Width-h)·den`, `sigHi` sits `oneGap` below the scaled
value and rounding up adds one whole `trimMul`. The `roundU1` test bounds the
remainder relative to half a unit step, with only the bits below `sigLo` unseen.

`decOne` is never asked to round-trip directly: it is emitted only when nothing
coarser round-trips, and then the exact method's fine case derives the
round-trip from the half-step bound, the grid at `decimalExponent e` being no
coarser than one ULP. So the only obligation here is that bound, a comparison
of `2·oneGap` with `trimMul` in which a midpoint goes up only from an odd
`sigHi`. That is one bound per parity, which is what `round_u1_iff_gap` states.
-/

/-- The residue at the unit step. -/
def oneResidue (f : ℕ) (e : FPExp fmt) : ℕ :=
  stepResidue (2 ^ (fmt.p10Width - exponentShift e)) f e

/-- The gap at the unit step, the distance from `sigHi` to the scaled value in
    the integer scale. -/
def oneGap (f : ℕ) (e : FPExp fmt) : ℕ :=
  stepGap (2 ^ (fmt.p10Width - exponentShift e)) f e

/-- `sigLo` is the unit-step remainder with its low `w - h` bits discarded. -/
theorem sig_lo_eq_residue_div (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    sigLo f e
      = oneResidue f e / 2 ^ (fmt.width - exponentShift e) := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  rw [sig_lo_eq, oneResidue, stepResidue,
    pow_shift_split e fmt.p10Width (by omega),
    Nat.mul_mod_mul_left, pow_shift_split e fmt.width (by omega),
    Nat.mul_div_mul_left _ _ (by positivity)]

/-- What `roundU1` decides about the remainder. Half a step divides down to
    exactly `2^(w-1)`, so the whole band `[half, half + 2^(w-h))` reads as a
    packed tie, which yy resolves by the parity of `sigHi`. -/
theorem round_u1_iff_residue (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    (toDecimalCandidates f e).roundU1 = true
      ↔ if sigHi f e % 2 = 0
        then 2 ^ (fmt.p10Width - 1 - exponentShift e)
            + 2 ^ (fmt.width - exponentShift e)
          ≤ oneResidue f e
        else 2 ^ (fmt.p10Width - 1 - exponentShift e)
          ≤ oneResidue f e := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hpos : (0 : ℕ) < 2 ^ (fmt.width - exponentShift e) := by positivity
  have hlo := sig_lo_eq_residue_div hl f e hsh
  have hpow : (2 : ℕ) ^ (fmt.width - 1) * 2 ^ (fmt.width - exponentShift e)
      = 2 ^ (fmt.p10Width - 1 - exponentShift e) := by
    rw [← pow_add]
    congr 1
    omega
  have hround : (toDecimalCandidates f e).roundU1
      = if sigLo f e = 2 ^ (fmt.width - 1) then
          decide (sigHi f e % 2 = 1)
        else decide (2 ^ (fmt.width - 1) < sigLo f e) := rfl
  -- Reaching half a step is `sigLo ≥ 2^(w-1)`, and leaving the tie band is
  -- `sigLo > 2^(w-1)`; both are the same division.
  have hhalf : 2 ^ (fmt.p10Width - 1 - exponentShift e) ≤ oneResidue f e
      ↔ 2 ^ (fmt.width - 1) ≤ sigLo f e := by
    rw [hlo, Nat.le_div_iff_mul_le hpos, hpow]
  have hpast : 2 ^ (fmt.p10Width - 1 - exponentShift e)
        + 2 ^ (fmt.width - exponentShift e) ≤ oneResidue f e
      ↔ 2 ^ (fmt.width - 1) < sigLo f e := by
    rw [Nat.lt_iff_add_one_le, hlo, Nat.le_div_iff_mul_le hpos, add_mul, one_mul,
      hpow]
  rw [hround, hhalf, hpast]
  rcases lt_trichotomy (sigLo f e) (2 ^ (fmt.width - 1)) with hs | hs | hs
  · rw [ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · rw [ite_eq_left hs]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  · rw [ite_eq_right (by omega)]
    simp only [decide_eq_true_eq]
    split_ifs <;> omega

/-- `sigHi` sits exactly `oneGap` below the scaled value. -/
theorem sig_hi_scaled (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    (sigHi f e : ℤ) * trimMul e + oneGap f e
      = 2 * f * trimNum e := by
  have h : sigHi f e * trimMul e + oneGap f e
      = 2 * f * trimNum e := by
    rw [sig_hi_quotient hl f e hsh]; exact step_quotient_add_gap _ f e
  exact_mod_cast h

/-- The unit-step gap is the remainder in integers plus the power-of-ten
    truncation error. -/
theorem one_gap_split (f : ℕ) (e : FPExp fmt) :
    oneGap f e
      = trimDen e * oneResidue f e
        + 2 * f * (trimNum e % trimDen e) := by
  rw [oneGap, stepGap, ← oneResidue]

/-- The gap exceeds a whole step only by the power-of-ten truncation error,
    which is under half a step. -/
theorem one_gap_lt_step_and_half (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (hsh : exponentShift e < 4) :
    2 * oneGap f e < 3 * trimMul e := by
  have hres : trimDen e * oneResidue f e < trimMul e := by
    rw [trimMul,
      Nat.mul_comm (2 ^ (fmt.p10Width - exponentShift e)) (trimDen e)]
    exact mul_lt_mul_of_pos_left
      (by rw [oneResidue, stepResidue]; exact Nat.mod_lt _ (by positivity))
      (trim_den_pos e)
  have htrunc := trim_trunc_lt f e hr
  have hhalf := trim_two_trunc_le_mul hl e hsh
  -- Already multiplied by `den`: `omega` holds the two products as atoms and
  -- cannot scale a bare power identity by one of them.
  have hpow : (2 : ℕ) ^ (fmt.prec + 2) * trimDen e
      = 2 * (2 ^ (fmt.prec + 1) * trimDen e) := by
    rw [show (2 : ℕ) ^ (fmt.prec + 2) = 2 * 2 ^ (fmt.prec + 1) from by
      rw [← pow_succ']]
    ring
  rw [one_gap_split]
  omega

/-! ### Refuting the unit-step windows

Two bands of the remainder are left undecided, both at the midpoint
`2^(p10Width-1-h)` of the unit step. Just below it the truncation error `2·f·τ`
can carry the exact gap past half a step while yy rounds down; at and just
above it yy reads a packed tie and resolves it by the parity of `sigHi`, which
the exact gap knows nothing about.

An odd `sigHi` rounds up, so the tie band is dangerous only for an even one.
That parity is the next bit of the same product, which the doubled modulus
`2^(p10Width+1-h)` sees: the residue stays below one unit step exactly when
`sigHi` is even. Both bands are windows there, refuted per exponent the way
`expWindows` refutes the coarse ones.

An exact power-of-ten approximation has no truncation error, so the band below
the midpoint is harmless and the midpoint is a genuine tie, resolved to even.
Those exponents refute the band above the midpoint only.
-/

/-- The residue in the doubled modulus, one bit wider than the unit step. -/
def oneParityResidue (f : ℕ) (e : FPExp fmt) : ℕ :=
  stepResidue (2 ^ (fmt.p10Width + 1 - exponentShift e)) f e

/-- That bit, split off: the doubled residue carries one whole unit step above
    the remainder exactly when `sigHi` is odd. -/
theorem one_parity_residue_split (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    oneParityResidue f e
      = 2 ^ (fmt.p10Width - exponentShift e) * (sigHi f e % 2)
        + oneResidue f e := by
  obtain ⟨hp10Width, hw⟩ := hl.width_facts
  have hw2 : (2 : ℕ) ^ (fmt.p10Width + 1 - exponentShift e)
      = 2 ^ (fmt.p10Width - exponentShift e) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hhi : oneParityResidue f e / 2 ^ (fmt.p10Width - exponentShift e)
      = sigHi f e % 2 := by
    rw [oneParityResidue, stepResidue, hw2, Nat.mod_mul_right_div_self,
      ← sig_hi_quotient hl f e hsh]
  have hlo : oneParityResidue f e % 2 ^ (fmt.p10Width - exponentShift e)
      = oneResidue f e := by
    rw [oneParityResidue, stepResidue, Nat.mod_mod_of_dvd _ ⟨2, hw2⟩, oneResidue,
      stepResidue]
  conv_lhs => rw [← Nat.div_add_mod (oneParityResidue f e)
    (2 ^ (fmt.p10Width - exponentShift e))]
  rw [hhi, hlo]

/-- A doubled residue landing in a refuted window is impossible. -/
private theorem one_no_window_hit {lo hi q : ℤ} (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e)
    (hcert : (oneWindows e).refutedBy q = true)
    (hmem : (lo, hi) ∈ (oneWindows e).windows)
    (hlo : lo ≤ (oneParityResidue f e : ℤ))
    (hhi : (oneParityResidue f e : ℤ) ≤ hi) :
    False :=
  Format.regular_not_hit f hr (by positivity) hcert hmem
    (by rw [oneParityResidue, stepResidue, Nat.mul_right_comm]) hlo hhi

/-- A truncated power-of-ten approximation adds the midpoint and the truncation
    error's reach below it, one for each parity of `sigHi`. -/
private theorem one_windows_truncated (e : FPExp fmt)
    (hτ : trimNum e % trimDen e ≠ 0) :
    ((2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e) - 2 ^ (fmt.prec + 1),
        (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e))
      ∈ (oneWindows e).windows ∧
      ((2 : ℤ) ^ (fmt.p10Width - exponentShift e)
            + 2 ^ (fmt.p10Width - 1 - exponentShift e) - 2 ^ (fmt.prec + 1),
          (2 : ℤ) ^ (fmt.p10Width - exponentShift e)
            + 2 ^ (fmt.p10Width - 1 - exponentShift e) - 1)
        ∈ (oneWindows e).windows := by
  simp only [oneWindows, Format.regularWindows, ite_eq_right hτ]
  exact ⟨.tail _ (.head _), .tail _ (.tail _ (.head _))⟩

/-- Below the midpoint the truncation error cannot reach it. -/
theorem one_residue_below_half (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e)
    (hτ : trimNum e % trimDen e ≠ 0)
    (hres : oneResidue f e < 2 ^ (fmt.p10Width - 1 - exponentShift e)) :
    oneResidue f e + 2 ^ (fmt.prec + 1)
      < 2 ^ (fmt.p10Width - 1 - exponentShift e) := by
  by_contra hcon
  have hsh := ha.shift_lt_four
  obtain ⟨q, hcert⟩ := ha.one_refuted
  obtain ⟨hbelow, habove⟩ := one_windows_truncated e hτ
  -- The remainder is in the last `2^(prec+1)` below the midpoint; the parity of
  -- `sigHi` decides which of the two windows holds it.
  have hlo : (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e)
      ≤ (oneResidue f e : ℤ) + 2 ^ (fmt.prec + 1) := by
    exact_mod_cast
      (show 2 ^ (fmt.p10Width - 1 - exponentShift e)
        ≤ oneResidue f e + 2 ^ (fmt.prec + 1) from by omega)
  have hhi : (oneResidue f e : ℤ) + 1
      ≤ (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e) := by
    exact_mod_cast hres
  have hsplit := one_parity_residue_split hl f e hsh
  rcases Nat.mod_two_eq_zero_or_one (sigHi f e) with hpar | hpar
  -- Even `sigHi`: the doubled residue is the remainder itself.
  · have hp : (oneParityResidue f e : ℤ) = (oneResidue f e : ℤ) := by
      rw [hsplit, hpar]; push_cast; ring
    exact one_no_window_hit f e hr hcert hbelow (by rw [hp]; linarith)
      (by rw [hp]; linarith)
  -- Odd `sigHi`: one whole window above it.
  · have hp : (oneParityResidue f e : ℤ)
        = (2 : ℤ) ^ (fmt.p10Width - exponentShift e)
          + (oneResidue f e : ℤ) := by
      rw [hsplit, hpar]; push_cast; ring
    exact one_no_window_hit f e hr hcert habove (by rw [hp]; linarith)
      (by rw [hp]; linarith)

/-- In the packed tie band, an even `sigHi` occurs only at a genuine midpoint,
    which yy resolves to even. -/
theorem one_tie_band_even (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) (hpar : sigHi f e % 2 = 0)
    (hlo : 2 ^ (fmt.p10Width - 1 - exponentShift e) ≤ oneResidue f e)
    (hhi : oneResidue f e
      < 2 ^ (fmt.p10Width - 1 - exponentShift e)
        + 2 ^ (fmt.width - exponentShift e)) :
    oneResidue f e = 2 ^ (fmt.p10Width - 1 - exponentShift e)
      ∧ trimNum e % trimDen e = 0 := by
  have hsh := ha.shift_lt_four
  obtain ⟨q, hcert⟩ := ha.one_refuted
  have hp : (oneParityResidue f e : ℤ) = (oneResidue f e : ℤ) := by
    rw [one_parity_residue_split hl f e hsh, hpar]; push_cast; ring
  -- Bounds for the part of the tie band strictly above the midpoint.
  have hup : (oneParityResidue f e : ℤ)
      ≤ (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e)
        + 2 ^ (fmt.width - exponentShift e) - 1 := by
    rw [hp]
    have hz : (oneResidue f e : ℤ) + 1
        ≤ (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e)
          + 2 ^ (fmt.width - exponentShift e) := by
      exact_mod_cast (show oneResidue f e + 1
        ≤ 2 ^ (fmt.p10Width - 1 - exponentShift e)
          + 2 ^ (fmt.width - exponentShift e) from hhi)
    linarith
  have hdown (hgt : 2 ^ (fmt.p10Width - 1 - exponentShift e)
      < oneResidue f e) :
      (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e) + 1
        ≤ (oneParityResidue f e : ℤ) := by
    rw [hp]
    exact_mod_cast
      (show 2 ^ (fmt.p10Width - 1 - exponentShift e) + 1
        ≤ oneResidue f e from hgt)
  -- The region strictly above the midpoint is refuted, leaving the midpoint.
  have hband (hgt : 2 ^ (fmt.p10Width - 1 - exponentShift e)
      < oneResidue f e) : False :=
    one_no_window_hit f e hr hcert (.head _) (hdown hgt) hup
  have hmid : oneResidue f e
      = 2 ^ (fmt.p10Width - 1 - exponentShift e) := by
    rcases Nat.eq_or_lt_of_le hlo with heq | hgt
    · exact heq.symm
    · exact (hband hgt).elim
  -- A truncated power-of-ten approximation refutes the midpoint too.
  refine ⟨hmid, ?_⟩
  by_contra hτ
  obtain ⟨hwin, -⟩ := one_windows_truncated e hτ
  have hz : (oneParityResidue f e : ℤ)
      = (2 : ℤ) ^ (fmt.p10Width - 1 - exponentShift e) := by
    rw [hp, hmid]; push_cast; ring
  exact one_no_window_hit f e hr hcert hwin
    (by rw [hz]; exact sub_le_self _ (by positivity)) (by rw [hz])

/-! ### What roundU1 decides -/

/-- Strictly below the packed midpoint the exact gap is strictly below half a
    step. -/
theorem one_gap_lt_half_step (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e)
    (hlt : oneResidue f e < 2 ^ (fmt.p10Width - 1 - exponentShift e)) :
    2 * oneGap f e < trimMul e := by
  have hsh := ha.shift_lt_four
  have hden := trim_den_pos e
  have htrunc := trim_trunc_lt f e hr
  have hstep := trim_mul_eq_two_half hl e hsh
  have hgap := one_gap_split f e
  by_cases hτ : trimNum e % trimDen e = 0
  · have hmono : trimDen e * (oneResidue f e + 1)
        ≤ trimDen e * 2 ^ (fmt.p10Width - 1 - exponentShift e) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : trimDen e * (oneResidue f e + 1)
        = trimDen e * oneResidue f e + trimDen e := by ring
    rw [hτ] at hgap
    omega
  · have hroom := one_residue_below_half hl f e hr ha hτ hlt
    have hmono : trimDen e * (oneResidue f e + 2 ^ (fmt.prec + 1))
        ≤ trimDen e * 2 ^ (fmt.p10Width - 1 - exponentShift e) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : trimDen e * (oneResidue f e + 2 ^ (fmt.prec + 1))
        = trimDen e * oneResidue f e
          + 2 ^ (fmt.prec + 1) * trimDen e := by ring
    omega

/-- yy's unit-step decision is the exact one: it rounds up exactly when the gap
    has passed half a step, with an exact midpoint going up only from an odd
    `sigHi`. -/
theorem round_u1_iff_gap (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    (toDecimalCandidates f e).roundU1 = true
      ↔ if sigHi f e % 2 = 0 then trimMul e < 2 * oneGap f e
        else trimMul e ≤ 2 * oneGap f e := by
  have hsh := ha.shift_lt_four
  have hden := trim_den_pos e
  have hgap := one_gap_split f e
  have hstep := trim_mul_eq_two_half hl e hsh
  -- One remainder unit is worth `trimDen` of the gap in integers.
  have hmono (n : ℕ) (h : n ≤ oneResidue f e) :
      trimDen e * n ≤ trimDen e * oneResidue f e :=
    Nat.mul_le_mul_left _ h
  rw [round_u1_iff_residue hl f e hsh]
  split_ifs with hpar
  -- Even `sigHi`: yy waits for the remainder to leave the tie band, and below
  -- the band the certificate leaves only the genuine midpoint.
  · refine ⟨fun hres => ?_, fun hlt => ?_⟩
    · have hb : (0 : ℕ) < 2 ^ (fmt.width - exponentShift e) := by positivity
      have hexp : trimDen e
          * (2 ^ (fmt.p10Width - 1 - exponentShift e)
            + 2 ^ (fmt.width - exponentShift e))
          = trimDen e * 2 ^ (fmt.p10Width - 1 - exponentShift e)
            + trimDen e * 2 ^ (fmt.width - exponentShift e) := by ring
      have := hmono _ hres
      have : 0 < trimDen e * 2 ^ (fmt.width - exponentShift e) := by
        positivity
      omega
    · by_contra hcon
      rcases Nat.lt_or_ge (oneResidue f e)
          (2 ^ (fmt.p10Width - 1 - exponentShift e)) with hlo | hlo
      · have := one_gap_lt_half_step hl f e hr ha hlo
        omega
      · obtain ⟨hres, hτ⟩ :=
          one_tie_band_even hl f e hr ha hpar hlo (by omega)
        rw [hgap, hres, hτ] at hlt
        omega
  -- Odd `sigHi`: yy rounds up from the tie band.
  · refine ⟨fun hres => ?_, fun hle => ?_⟩
    · have := hmono _ hres
      omega
    · by_contra hcon
      have := one_gap_lt_half_step hl f e hr ha (by omega)
      omega

/-- `decOne` sits `oneGap` below the scaled value, less one whole step when it
    rounds up. -/
theorem dec_one_scaled (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hsh : exponentShift e < 4) :
    let c := toDecimalCandidates f e
    (c.decOne : ℤ) * trimMul e
        + ((oneGap f e : ℤ)
          - if c.roundU1 = true then (trimMul e : ℤ) else 0)
      = 2 * f * trimNum e := by
  intro c
  have h := sig_hi_scaled hl f e hsh
  show ((sigHi f e + if c.roundU1 then 1 else 0 : ℕ) : ℤ) * _ + _ = _
  cases c.roundU1 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    push_cast <;> linarith

/-- `decOne` is a nearest value on the grid at `decimalExponent e`, ties to
    even. -/
theorem dec_one_nearest (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    let c := toDecimalCandidates f e
    let x := value f e * 10 ^ (-fmt.decimalExponent e)
    |(c.decOne : ℚ) - x| ≤ 1 / 2 ∧
      (|(c.decOne : ℚ) - x| = 1 / 2 → c.decOne % 2 = 0) := by
  intro c x
  have hsh := ha.shift_lt_four
  have hmul := trim_mul_pos e
  obtain ⟨hle, -, heq⟩ := scaled_cmp_of_int_eq (a := 2) (b := trimMul e)
    (thr := 1 / 2) (trim_mul_pos e) two_pos
    (trim_value_scaled hl f e ha.shift_nonneg hsh)
    (by push_cast; ring) (dec_one_scaled hl f e hsh)
  have hwide := one_gap_lt_step_and_half hl f e hr hsh
  have hflag := round_u1_iff_gap hl f e hr ha
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

/-- On the coarse path, yy emits a multiple of ten that round-trips. -/
theorem coarse_output_roundtrips (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true →
    let d := (toDecimal f e).1
    d % 10 = 0
      ∧ Roundtrips f e ((d : ℚ) * 10 ^ fmt.decimalExponent e) := by
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
    simpa using (round_d0_iff_roundtrips hl f e hr ha).mp hd0
  · rw [hten, hu0]
    simpa using (round_u0_iff_roundtrips hl f e hr ha).mp hu0

/-- On the fine path, yy emits `decOne`, a nearest value on its own grid. -/
theorem fine_output_nearest (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = false →
    let d := (toDecimal f e).1
    let x := value f e * 10 ^ (-fmt.decimalExponent e)
    |(d : ℚ) - x| ≤ 1 / 2 ∧ (|(d : ℚ) - x| = 1 / 2 → d % 2 = 0) := by
  intro c htrim d
  rw [show d = c.decOne from by
    show (if c.roundD0 || c.roundU0 then _ else _) = _
    rw [htrim]
    rfl]
  exact dec_one_nearest hl f e hr ha

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
    `sigTen` or `sigTen + 10`. -/
theorem coarse_candidate_cases (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) (d : ℕ) (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ fmt.decimalExponent e)) :
    d = sigTen f e ∨ d = sigTen f e + 10 := by
  -- The bracket is one-sided each way rather than an absolute value, so this
  -- consumer takes the distance identity and not the interval bridge.
  have hmul : (0 : ℚ) < (trimMul e : ℚ) := by
    exact_mod_cast trim_mul_pos e
  have hdown := scaled_dist_eq
    (trim_value_scaled hl f e ha.shift_nonneg ha.shift_lt_four)
    (dec_ten_down_scaled hl f e ha.shift_lt_four)
  push_cast at hdown
  have hhalf := trim_mul_half_ulp hl e ha.shift_nonneg ha.shift_lt_four
  have hgap0 : (0 : ℚ) ≤ (trimGap f e : ℚ) := by positivity
  have hnum0 : (0 : ℚ) ≤ (trimNum e : ℚ) := by positivity
  have hgap : (trimGap f e : ℚ)
      < (trimScale e : ℚ) + (trimNum e : ℚ) := by
    exact_mod_cast trim_gap_lt_scale_add hl f e hr ha.table
  have hstep : (trimScale e : ℚ) = 10 * (trimMul e : ℚ) := by
    exact_mod_cast trim_scale_eq_ten_mul e
  exact coarse_roundtrip_adjacent f e (fmt.decimalExponent e)
    (ulp_scaled_bounds hl e ha).2 (sig_ten_mod_ten f e) h10
    (le_of_mul_le_mul_right (by linarith) hmul)
    (lt_of_mul_lt_mul_right (by linarith) hmul.le) hround

/-- If the rounding interval contains a multiple of ten, yy trims. -/
theorem trim_of_coarse_roundtrip (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) (d : ℕ) (h10 : d % 10 = 0)
    (hround : Roundtrips f e (d * 10 ^ fmt.decimalExponent e)) :
    let c := toDecimalCandidates f e
    (c.roundD0 || c.roundU0) = true := by
  intro c
  rw [Bool.or_eq_true]
  rcases coarse_candidate_cases hl f e hr ha d h10 hround with rfl | rfl
  · exact Or.inl ((round_d0_iff_roundtrips hl f e hr ha).mpr hround)
  · exact Or.inr ((round_u0_iff_roundtrips hl f e hr ha).mpr hround)

/-! ## yy refines the exact method

Nothing above is needed beyond `ulp_scaled_bounds` and the three semantic
obligations `coarse_output_roundtrips`, `fine_output_nearest`, and
`trim_of_coarse_roundtrip`. In particular no claim is made that yy's packed
decisions agree with the exact ones: a packed midpoint need not be an exact
midpoint, and the trim flags are matched to the existence of an exact coarse
candidate, not to any exact comparison.

`correct_of` is the generic conclusion, in the format and the two records of
per-format obligations. Everything below it is binary64's instance.
-/

/-- yy implements the exact method: it trims exactly when an exact coarse
    candidate exists. -/
theorem exact_candidate (hl : Layout fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (ha : ChecksAt e) :
    let (d, k) := toDecimal f e
    ExactCandidate f e k d := by
  set c := toDecimalCandidates f e
  by_cases htrim : (c.roundD0 || c.roundU0) = true
  · exact Or.inl (coarse_output_roundtrips hl f e hr ha htrim)
  · rw [Bool.not_eq_true] at htrim
    obtain ⟨hle, heven⟩ := fine_output_nearest hl f e hr ha htrim
    refine Or.inr ⟨fun ⟨d, h10, hround⟩ => ?_, hle, heven⟩
    rw [trim_of_coarse_roundtrip hl f e hr ha d h10 hround] at htrim
    exact Bool.noConfusion htrim

/-- yy is correct on the regularly spaced positive values of any format whose
    layout yy's packing fits and whose per-exponent checks hold: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid.

    Everything format-specific is in the two hypotheses. `Layout` is two
    inequalities about the width, discharged by `decide`; `Checks` is the
    per-exponent sweep, and it is the only expensive thing about a new
    format. -/
theorem correct_of (hl : Layout fmt) (hchk : Checks fmt) (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) :
    let (d, k) := toDecimal f e
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  obtain ⟨hlo, hhi⟩ := hr.range
  have ha := hchk e hlo hhi
  obtain ⟨hfine, hcoarse⟩ := ulp_scaled_bounds hl e ha
  exact exact_candidate_correct f e (fmt.decimalExponent e) hr.pos
    hfine hcoarse
    (exact_candidate hl f e hr ha)

/-! ## binary64

The instantiation. `Layout` is arithmetic on the constants; the remaining
obligations are inherited from `Core.lean`, proved from the concrete constants,
or swept over binary64's 2046 exponents. The two modular certificate families
dominate the cost.
-/

/-- binary64's raw shift, with the constants exposed so that `omega` can see
    them. Both sides are the same term; the point is the spelling. -/
private theorem b64_shift_raw_eq (e : ℤ) :
    shiftRaw (⟨e⟩ : FPExp binary64)
      = e + (-(e * 315_653 / 2 ^ 20) * 217_707) / 2 ^ 16 := rfl

theorem binary64_layout : Layout binary64 := ⟨by decide, by decide⟩

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. The two
    fixed-point constants multiply to just over one, by a part in 2^17.4, and
    that is exactly enough for `omega`'s rational relaxation to still admit a
    shift of `-1`. Ruling it out is a Diophantine fact about the constants
    rather than a magnitude bound, so it is checked. -/
private theorem b64_shift_nonneg :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971, 0 ≤ shiftRaw (⟨e⟩ : FPExp binary64) := by
  -- This and the check like it below enumerate 2046 exponents each. `+kernel`
  -- keeps them out of the elaborator, whose recursion and exponentiation
  -- guards they would otherwise trip.
  decide +kernel

/-- The shift used by yy's regular path is less than 4. Unlike the bound above
    this is a magnitude fact, so `omega` gets it from the constants directly. -/
private theorem b64_shift_lt_four (e : ℤ) (hlo : -1074 ≤ e) (hhi : e ≤ 971) :
    exponentShift (⟨e⟩ : FPExp binary64) < 4 := by
  show (shiftRaw (⟨e⟩ : FPExp binary64)).toNat < 4
  rw [b64_shift_raw_eq]
  omega

/-- The table entry is normalized, from binary64's sweep in `core`. -/
private theorem b64_table (e : ℤ) (hlo : -1074 ≤ e) (hhi : e ≤ 971) :
    TableNormalized (⟨e⟩ : FPExp binary64) :=
  binary64.power10_ratio_normalized hlo hhi
    (-binary64.decimalExponent e) (by omega)

private theorem b64_trim_checks :
    ∀ e ∈ Finset.Icc (-1074 : ℤ) 971,
      trimChecksHold (⟨e⟩ : FPExp binary64) = true := by
  decide +kernel

/-- Close `∃ q, (expWindows binary64 e).refutedBy q = true` for a literal
    exponent. -/
elab "exp_cert" : tactic =>
  modCertTactic fun e => (expWindows (⟨e⟩ : FPExp binary64)).search

/-- Close `∃ q, (oneWindows binary64 e).refutedBy q = true` for a literal
    exponent. -/
elab "one_cert" : tactic =>
  modCertTactic fun e => (oneWindows (⟨e⟩ : FPExp binary64)).search

private theorem b64_exp_refuted (e : ℤ) (hlo : -1074 ≤ e) (hhi : e ≤ 971) :
    ∃ q, (expWindows (⟨e⟩ : FPExp binary64)).refutedBy q = true := by
  interval_cases e <;> exp_cert

private theorem b64_one_refuted (e : ℤ) (hlo : -1074 ≤ e) (hhi : e ≤ 971) :
    ∃ q, (oneWindows (⟨e⟩ : FPExp binary64)).refutedBy q = true := by
  interval_cases e <;> one_cert

theorem binary64_checks : Checks binary64 := by
  rintro ⟨e⟩ hlo hhi
  -- Restate the bounds with the literals visible; `omega` treats
  -- `binary64.emin` as an opaque atom otherwise.
  have hlo' : (-1074 : ℤ) ≤ e := hlo
  have hhi' : e ≤ 971 := hhi
  exact
    { shift_nonneg :=
        b64_shift_nonneg e (by simp only [Finset.mem_Icc]; omega)
      shift_lt_four := b64_shift_lt_four e hlo' hhi'
      table := b64_table e hlo' hhi'
      trim := trim_checks_of_hold _
        (b64_trim_checks e (by simp only [Finset.mem_Icc]; omega))
      exp_refuted := fun f hr =>
        Or.inl (exp_avoids_of_cert f _ hr
          (b64_exp_refuted e hlo' hhi').choose_spec)
      one_refuted := b64_one_refuted e hlo' hhi' }

/-- yy is correct on regularly spaced positive binary64 values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid. -/
theorem correct (f : ℕ) (e : ℤ) (hr : binary64.Regular f e) :
    let (d, k) := toDecimal f (⟨e⟩ : FPExp binary64)
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' :=
  correct_of binary64_layout binary64_checks f ⟨e⟩ hr

end YY
