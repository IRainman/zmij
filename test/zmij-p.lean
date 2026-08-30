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

* the table entry is the 128-bit significand of `10^k` rounded *up*, so the
  computed value never falls below the exact one and a value at or above a
  midpoint cannot present itself below one;
* the sticky bit is taken from the product's bits `[64, n-1)`, discarding the
  low word, so the ceiling's excess — under `2^64` denominators, `gap_lt` —
  cannot appear as a set sticky bit and push a value that is exactly on a
  midpoint above it.

One ambiguity survives: a value *near* a midpoint presents the same guard bits
as one exactly on it. `fine_windows_refuted` and `coarse_windows_refuted` rule
that out at the reported grid and at the reround's, over every significand of
every (exponent, precision) pair.

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
      ← normalized_of_input
      ← correctly_rounded_of_normalized
          ← value_normalized
      ← digit_count
      ← rounds_to_nearest
          ← fine_within_half, coarse_within_half
              ← exact_eq, round_even_packed, round_even_demote
              ← dev_eq_zero, dev_eq_zero_coarse  (the certificates)
          ← value_scaled                        (the other use of ℚ)

## Why it is not in the default build

The checks below run for about four minutes. Nothing else depends on this file,
so it is a `lean_lib` of its own, absent from `defaultTargets`: `lake build` is
unaffected and `lake build «zmij-p»` is the explicit request to verify the
fixed-precision path.

## What the four minutes are spent on

|  | count | cost |
|---|---|---|
| `point_shift_bounds` | 37,764 pairs | 12s |
| `table_checks` | 649 indices, to 1.1 kbit | under a second |
| `grid_bounds` | 37,764 pairs | 21s |
| `fine_refuted`, `coarse_refuted` | 37,764 certificates each | ~95s each |

As in `yy128.lean` and `yy80.lean` the multiplier is found by
`ModWindows.search` during elaboration and only the literal reaches the proof
term. The certificates are the bulk of the cost even so, and they spend it on
elaboration rather than in the kernel: 37,764 goals per family, against the 2098
exponents `zmij.lean` splits.
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

/-- The table entry `scale` multiplies by: the 128-bit significand of `10^k`
    rounded up, `num / den` being the truncation `power10Significand` takes.
    zmij bumps the entry when `dec_exp < -55` or `dec_exp > 0`, which over the
    indices reached is exactly when the truncation loses something, and adds the
    bump to the low word, which is where it fits: both are `table_checks`. -/
def tableEntry (k : ℤ) : ℕ :=
  binary64.power10Num k / binary64.power10Den k
    + if binary64.power10Num k % binary64.power10Den k = 0 then 0 else 1

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
def demote (x : ℕ) : ℕ := x / 10 ||| x % 2 ||| (if x % 10 = 0 then 0 else 1)

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
    digit's exponent, which denotes the same value: `reported_eq`. Those 18 also
    bound the precision a caller may ask for, `1 ≤ p ∧ p ≤ 18` standing as a
    hypothesis of its own throughout: it constrains the request, where the two
    structures below constrain the value. -/
def toDecimal (f : ℕ) (e : ℤ) (p : ℕ) : ℕ × ℤ :=
  rounded (f * 2 ^ normShift f) (e - normShift f) p

/-- The value `to_decimal` is called on: a positive finite binary64, a subnormal
    arriving as a significand below `2^52` at `emin`. -/
structure Input (f : ℕ) (e : ℤ) : Prop where
  sig : 0 < f ∧ f < 2 ^ 53
  exp : -1074 ≤ e ∧ e ≤ 971

/-- The value `rounded` is called on, which `normalized_of_input` derives from
    the input. The significand is normalized, which for a subnormal costs
    exponent range: the shift reaches 52 below `emin`. -/
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

/-- What the discarded low word can be worth, cleared: the table's ceiling adds
    under one to a 128-bit entry, which the shifted significand scales by under
    `2^64`. -/
def slack (e : ℤ) (p : ℕ) : ℕ := 2 ^ 64 * den e p

/-- What the ceiling added, cleared and scaled by the significand: the
    difference between the product zmij formed and the exact one. -/
def gap (f : ℕ) (e : ℤ) (p : ℕ) : ℕ := den e p * product f e p - exact f e p

/-- What the guard bits do not report: the product bits below the 1/2 place,
    cleared, less what the ceiling added. It is `dev` being zero that makes an
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

/-- The table over the indices reached: truncation loses something exactly when
    zmij bumps the entry, the bump does not carry out of the low word it is
    added to, and the result is a normalized 128-bit number. -/
theorem table_checks : ∀ k ∈ Finset.Icc (-307 : ℤ) 341,
    (binary64.power10Num k % binary64.power10Den k = 0 ↔ 0 ≤ k ∧ k ≤ 55)
      ∧ binary64.power10Num k / binary64.power10Den k % 2 ^ 64 ≠ 2 ^ 64 - 1
      ∧ 2 ^ 127 ≤ tableEntry k ∧ tableEntry k < 2 ^ 128 := by
  decide +kernel

/-- The scaled value has the digits asked for, to within a step: it is at least
    `10^(p-1)` and below `2·10^p`. Monotonicity in the significand leaves one
    comparison per end of its box. -/
theorem grid_bounds : ∀ p ∈ Finset.Icc 1 18, ∀ e ∈ Finset.Icc (-1126 : ℤ) 971,
    10 ^ (p - 1) * step e p ≤ 2 ^ 52 * 2 ^ 11 * num e p
      ∧ (2 ^ 53 - 1) * 2 ^ 11 * num e p < 2 * 10 ^ p * step e p := by
  decide +kernel

/-- The window problem at a grid `mult` times the reported one: the residues of
    `exact` that sit within `slack` of that grid's midpoint without sitting on
    it. A significand there would present the guard bits of a tie without being
    one, and that is the only way the packed value can mislead. -/
def midWindows (e : ℤ) (p mult : ℕ) : ModWindows where
  g := 2 ^ 11 * num e p
  modulus := mult * step e p
  f0 := 2 ^ 52
  f1 := 2 ^ 53 - 1
  windows :=
    let c : ℤ := mult * halfStep e p
    [(c - slack e p + 1, c - 1), (c + 1, c + slack e p - 1)]

/-! ### Modular certificates

`modCertTactic` reads one integer literal out of the goal and runs the search on
it during elaboration, so the two indices have to arrive as one: `pairIndex`
packs them, eighteen precisions to the exponent, and the two families below
unpack them. A sweep over the packed index is then the same one variable
`interval_cases` splits in `yy128.lean` and `yy80.lean`.

Doing it instead by deciding `refutedBy search` over the grid would put the
Euclidean search itself in the kernel, 37,764 times per family, which is hours
and gigabytes rather than minutes.
-/

/-- The `(exponent, precision)` pair as one index, `0 ≤ c < 37764`. -/
def pairIndex (e : ℤ) (p : ℕ) : ℤ := (e + 1126) * 18 + ((p : ℤ) - 1)

/-- The window problem at the reported grid, at the pair `c` denotes. -/
def fineWindows (c : ℤ) : ModWindows :=
  midWindows (c / 18 - 1126) ((c % 18).toNat + 1) 1

/-- And at the reround's grid, ten times coarser. -/
def coarseWindows (c : ℤ) : ModWindows :=
  midWindows (c / 18 - 1126) ((c % 18).toNat + 1) 10

/-- Close `∃ q, (fineWindows c).refutedBy q = true` for a literal `c`. -/
elab "fine_cert" : tactic => modCertTactic fun c => (fineWindows c).search

/-- Close `∃ q, (coarseWindows c).refutedBy q = true` for a literal `c`. -/
elab "coarse_cert" : tactic => modCertTactic fun c => (coarseWindows c).search

/-- No significand puts the reported grid's guard bits at a tie that is not one.
    The multiplier is searched for during elaboration and checked by the kernel,
    so a bad one would be a failed proof rather than an unsound one. -/
private theorem fine_refuted (c : ℤ) (hlo : 0 ≤ c) (hhi : c ≤ 37763) :
    ∃ q, (fineWindows c).refutedBy q = true := by
  interval_cases c <;> fine_cert

/-- The same at the reround's grid. -/
private theorem coarse_refuted (c : ℤ) (hlo : 0 ≤ c) (hhi : c ≤ 37763) :
    ∃ q, (coarseWindows c).refutedBy q = true := by
  interval_cases c <;> coarse_cert

/-- Unpacking inverts packing: eighteen precisions to the exponent, so the
    precision is what the division leaves. -/
private theorem pair_index_unpack {e : ℤ} {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 18) :
    pairIndex e p / 18 - 1126 = e ∧ (pairIndex e p % 18).toNat + 1 = p := by
  rw [pairIndex]
  omega

/-- The certificate at the reported grid, in the pair's own terms. -/
theorem fine_windows_refuted {e : ℤ} {p : ℕ} (he : -1126 ≤ e ∧ e ≤ 971)
    (hp : 1 ≤ p ∧ p ≤ 18) : ∃ q, (midWindows e p 1).refutedBy q = true := by
  obtain ⟨hdiv, hmod⟩ := pair_index_unpack (e := e) hp
  have h : fineWindows (pairIndex e p) = midWindows e p 1 := by
    simp only [fineWindows, hdiv, hmod]
  rw [← h]
  exact fine_refuted _ (by rw [pairIndex]; omega) (by rw [pairIndex]; omega)

/-- And at the reround's. -/
theorem coarse_windows_refuted {e : ℤ} {p : ℕ} (he : -1126 ≤ e ∧ e ≤ 971)
    (hp : 1 ≤ p ∧ p ≤ 18) : ∃ q, (midWindows e p 10).refutedBy q = true := by
  obtain ⟨hdiv, hmod⟩ := pair_index_unpack (e := e) hp
  have h : coarseWindows (pairIndex e p) = midWindows e p 10 := by
    simp only [coarseWindows, hdiv, hmod]
  rw [← h]
  exact coarse_refuted _ (by rw [pairIndex]; omega) (by rw [pairIndex]; omega)

/-! ## The arithmetic model

The product, split at the two bit positions zmij reads it at, and the exact
value, recovered from that split. `exact_eq` is where the two meet.
-/

theorem den_pos (e : ℤ) (p : ℕ) : 0 < den e p :=
  binary64.power10_den_pos _

theorem step_pos (e : ℤ) (p : ℕ) : 0 < step e p := by
  have := den_pos e p
  rw [step, halfStep]
  positivity

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

/-- The table entry is the exact ratio rounded up: one denominator's worth above
    the numerator at most, and never below it. -/
theorem entry_bounds (k : ℤ) :
    binary64.power10Num k ≤ binary64.power10Den k * tableEntry k
      ∧ binary64.power10Den k * tableEntry k
          < binary64.power10Num k + binary64.power10Den k := by
  have hd := binary64.power10_den_pos k
  have hdm := Nat.div_add_mod (binary64.power10Num k) (binary64.power10Den k)
  have hlt := Nat.mod_lt (binary64.power10Num k) hd
  rw [tableEntry, Nat.mul_add]
  split_ifs <;> omega

/-- What the ceiling added: the product zmij formed, cleared, is the exact value
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
      _ ≤ f * 2 ^ 11 * (num e p + den e p) := Nat.mul_le_mul_left _ hb.2.le
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
    more than `-slack`, the ceiling being all that can put it negative. -/
theorem dev_bounds (f : ℕ) (e : ℤ) (p : ℕ) (hf : f < 2 ^ 53) :
    -(slack e p : ℤ) < dev f e p ∧ dev f e p < halfStep e p := by
  have hgap := gap_lt f e p hf
  have hup : den e p * tail f e p < halfStep e p := by
    rw [halfStep]
    exact Nat.mul_lt_mul_of_le_of_lt le_rfl (tail_lt f e p) (den_pos e p)
  rw [dev]
  omega

/-- The discarded low word is worth far less than half a step: `point_shift`
    leaves 65 bits between the two. -/
theorem slack_lt_half_step (e : ℤ) (p : ℕ) (hs : 3 ≤ pointShift e p) :
    (slack e p : ℤ) < halfStep e p := by
  have hn := shift_bits_ge hs
  have h : slack e p < halfStep e p := by
    rw [slack, halfStep]
    calc 2 ^ 64 * den e p = den e p * 2 ^ 64 := by ring
      _ < den e p * 2 ^ (shiftBits e p - 1) :=
          Nat.mul_lt_mul_of_le_of_lt le_rfl
            (Nat.pow_lt_pow_right one_lt_two (by omega)) (den_pos e p)
  exact_mod_cast h

/-- A set sticky bit puts the exact value strictly above the midpoint the 1/2
    bit reports: the bits it saw are worth more than the ceiling could add. -/
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

/-! ## The rounding decisions

`round_even` reads its decision off the two guard bits, and the reround reads a
coarser one off those two and the digit it drops. Both are arithmetic; what they
decide is correct is the section after this one.
-/

/-- `round_even`, off the two guard bits: it rounds up when they say the value
    is past the midpoint, and at the midpoint when what remains is odd. -/
theorem round_even_eq (i b : ℕ) (hb : b ≤ 3) :
    roundEven (4 * i + b)
      = i + if 2 ≤ b ∧ (b = 3 ∨ i % 2 = 1) then 1 else 0 := by
  rw [roundEven]
  split_ifs <;> omega

/-- `round_even` keeps the integral part unless the 1/2 bit is set and either
    the sticky bit is set or the integral part is odd. -/
theorem round_even_packed (f : ℕ) (e : ℤ) (p : ℕ) :
    roundEven (packed f e p) = integral f e p
      + if half f e p = 1 ∧ (sticky f e p = 1 ∨ integral f e p % 2 = 1)
        then 1 else 0 := by
  obtain ⟨hh, hs⟩ := guard_le_one f e p
  rw [packed, show 4 * integral f e p + 2 * half f e p + sticky f e p
      = 4 * integral f e p + (2 * half f e p + sticky f e p) from by ring,
    round_even_eq _ _ (by omega)]
  split_ifs <;> omega

/-- `demote` sets the sticky bit unless what it drops is zero. -/
theorem demote_eq (x : ℕ) :
    demote x = if x % 10 = 0 then x / 10 else 2 * (x / 10 / 2) + 1 := by
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
  split_ifs with h10
  · rw [show x % 2 = 0 from by omega, Nat.or_zero, Nat.or_zero]
  · rcases show x % 2 = 0 ∨ x % 2 = 1 from by omega with h2 | h2
    · rw [h2, Nat.or_zero, hor]
    · rw [h2, hor, hor,
        show (2 * (x / 10 / 2) + 1) / 2 = x / 10 / 2 from by omega]

/-- `demote` one place coarser, in the same packed form: what remains of the
    integral part above two guard bits of its own, which the digit that leaves
    and the old guard bits together decide. -/
theorem demote_packed (q t b : ℕ) :
    demote (4 * (10 * q + t) + b) = 4 * q
      + (if (4 * t + b) % 10 = 0 then (4 * t + b) / 10
        else 2 * ((4 * t + b) / 10 / 2) + 1) := by
  rw [demote_eq]
  split_ifs <;> omega

/-- `round_even` after `demote`, over the forty cases of the digit that leaves
    against the two guard bits: the digit decides, except at a five, where the
    guard bits do and, failing them, the parity of what remains. -/
theorem round_even_demote_aux (q t b : ℕ) (ht : t < 10) (hb : b ≤ 3) :
    roundEven (demote (4 * (10 * q + t) + b))
      = q + if 6 ≤ t ∨ (t = 5 ∧ (b ≠ 0 ∨ q % 2 = 1)) then 1 else 0 := by
  rw [demote_packed q t b]
  interval_cases t <;> interval_cases b <;> norm_num [roundEven] <;>
    (try split_ifs) <;> omega

/-- The same, off the packed value: the two guard bits are the `b` above. -/
theorem round_even_demote (f : ℕ) (e : ℤ) (p : ℕ) :
    roundEven (demote (packed f e p)) = integral f e p / 10
      + if 6 ≤ integral f e p % 10
          ∨ (integral f e p % 10 = 5 ∧ (half f e p = 1 ∨ sticky f e p = 1
            ∨ integral f e p / 10 % 2 = 1))
        then 1 else 0 := by
  obtain ⟨hh, hs⟩ := guard_le_one f e p
  rw [packed, show 4 * integral f e p + 2 * half f e p + sticky f e p
      = 4 * (10 * (integral f e p / 10) + integral f e p % 10)
        + (2 * half f e p + sticky f e p) from by omega,
    round_even_demote_aux _ _ _ (by omega) (by omega)]
  split_ifs <;> omega

/-! ## An apparent tie is a real one

Everything the guard bits hide is under `slack`: the product bits they do not
see and the ceiling's excess both are. So the packed value can only mislead by
presenting a value near a midpoint as one exactly on it, and the certificates
say no significand does that.
-/

/-- A clear sticky bit leaves the exact value within `slack` of the midpoint the
    1/2 bit reports: the bits it hides are worth less than that, and so is the
    ceiling's excess. -/
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

/-- What the certificates say, at either grid: a residue near the midpoint has
    to be on it. `j` is whatever multiple of the modulus the caller's identity
    leaves, which the certificate never reads. -/
theorem dev_eq_zero_of_cert {f : ℕ} {e : ℤ} {p mult : ℕ}
    (hin : Normalized f e) (hmult : 0 < mult) {q : ℤ}
    (hcert : (midWindows e p mult).refutedBy q = true)
    (hnear : -(slack e p : ℤ) < dev f e p ∧ dev f e p < slack e p) {j : ℤ}
    (hres : (mult : ℤ) * (halfStep e p : ℤ) + dev f e p
      = (midWindows e p mult).g * f - (midWindows e p mult).modulus * j) :
    dev f e p = 0 := by
  have hsig := hin.sig
  have hbox : (midWindows e p mult).f0 ≤ f ∧ f ≤ (midWindows e p mult).f1 := by
    simp only [midWindows]
    omega
  have hmod : 0 < (midWindows e p mult).modulus := by
    have := step_pos e p
    simp only [midWindows]
    positivity
  set c : ℤ := (mult : ℤ) * (halfStep e p : ℤ) with hc
  set w : ℤ := (slack e p : ℤ) with hw
  have hmem₁ : (c - w + 1, c - 1) ∈ (midWindows e p mult).windows := by
    simp [midWindows, hc, hw]
  have hmem₂ : (c + 1, c + w - 1) ∈ (midWindows e p mult).windows := by
    simp [midWindows, hc, hw]
  rcases lt_trichotomy (dev f e p) 0 with hlt | heq | hgt
  · exact absurd hres fun h => (midWindows e p mult).not_hit_rep f hmod hcert
      hmem₁ hbox.1 hbox.2 h (by omega) (by omega)
  · exact heq
  · exact absurd hres fun h => (midWindows e p mult).not_hit_rep f hmod hcert
      hmem₂ hbox.1 hbox.2 h (by omega) (by omega)

/-- At the reported grid: when the 1/2 bit is set and the sticky bit is not, the
    exact value sits exactly on the midpoint. -/
theorem dev_eq_zero (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) (hhalf : half f e p = 1)
    (hsticky : sticky f e p = 0) : dev f e p = 0 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hn := shift_bits_ge hs.1
  refine dev_eq_zero_of_cert (mult := 1) hin (by norm_num)
    (fine_windows_refuted hin.exp hp).choose_spec
    (dev_near_of_sticky_eq_zero f e p hin.sig.2 hsticky)
    (j := integral f e p) ?_
  -- The residue at the midpoint, offset by what the guard bits hide.
  have hex := exact_eq f e p (by omega)
  rw [hhalf, exact] at hex
  simp only [midWindows, step]
  push_cast at hex ⊢
  linarith

/-- At the reround's grid: when the digit that leaves is a five and neither
    guard bit is set, the exact value sits exactly on the coarser midpoint. -/
theorem dev_eq_zero_coarse (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) (hhalf : half f e p = 0)
    (hsticky : sticky f e p = 0) (hfive : integral f e p % 10 = 5) :
    dev f e p = 0 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hn := shift_bits_ge hs.1
  refine dev_eq_zero_of_cert (mult := 10) hin (by norm_num)
    (coarse_windows_refuted hin.exp hp).choose_spec
    (dev_near_of_sticky_eq_zero f e p hin.sig.2 hsticky)
    (j := integral f e p / 10) ?_
  have hex := exact_eq f e p (by omega)
  have hI : (integral f e p : ℤ)
      = 10 * (integral f e p / 10 : ℕ) + 5 := by omega
  rw [hhalf, exact] at hex
  rw [hI] at hex
  simp only [midWindows, step]
  push_cast at hex ⊢
  linarith

/-! ## Half a step

Both candidates are within half a step of the exact value, with a step of
whichever grid they are reported on. The two bounds below are the whole of the
correctness argument; everything above is what they are read off, and the
sections after this one only spend them.

The bounds are stated over abstract integers first. `G` is half a step, `dev`
what the guard bits do not report, and the case analysis is over the guard bits
and the parity that breaks a tie: eight cases at the reported grid, eighty at
the reround's, where the digit that leaves decides first.
-/

/-- The distance to `round_even`'s candidate: within half a step, and exactly
    half a step only where the guard bits report a tie, which `dev = 0` makes a
    real one and the candidate's parity then resolves. -/
private theorem dist_bound {G dev : ℤ} {h s c i : ℕ} (hh : h ≤ 1) (hs : s ≤ 1)
    (hlo : -G < dev) (hhi : dev < G) (hsticky : s = 1 → 0 < dev)
    (htie : h = 1 → s = 0 → dev = 0)
    (hc : c = if h = 1 ∧ (s = 1 ∨ i % 2 = 1) then 1 else 0) :
    -G ≤ G * h + dev - 2 * G * c ∧ G * h + dev - 2 * G * c ≤ G
      ∧ (G * h + dev - 2 * G * c = G → (i + c) % 2 = 0)
      ∧ (G * h + dev - 2 * G * c = -G → (i + c) % 2 = 0) := by
  -- The case split has to reach the goal, where the products with `G` are
  -- otherwise nonlinear, and it has to leave `c` a literal: `omega` reads
  -- implications but not disjunctions, which is why the ties are two
  -- implications above and the parity is a case here rather than a disjunct.
  interval_cases h <;> interval_cases s <;>
    rcases show i % 2 = 0 ∨ i % 2 = 1 from by omega with hi | hi <;>
      rw [hi] at hc <;> norm_num at hc <;> subst hc <;> omega

/-- The same at the reround's grid, ten times coarser: `t` is the digit that
    leaves and `q` what remains, whose parity breaks the coarser tie. -/
private theorem dist_bound_coarse {G dev : ℤ} {h s c t q : ℕ} (hh : h ≤ 1)
    (hs : s ≤ 1) (ht : t < 10) (hlo : -G < dev) (hhi : dev < G)
    (hsticky : s = 1 → 0 < dev) (htie : t = 5 → h = 0 → s = 0 → dev = 0)
    (hc : c = if 6 ≤ t ∨ (t = 5 ∧ (h = 1 ∨ s = 1 ∨ q % 2 = 1)) then 1 else 0) :
    -(10 * G) ≤ 2 * G * t + G * h + dev - 20 * G * c
      ∧ 2 * G * t + G * h + dev - 20 * G * c ≤ 10 * G
      ∧ (2 * G * t + G * h + dev - 20 * G * c = 10 * G → (q + c) % 2 = 0)
      ∧ (2 * G * t + G * h + dev - 20 * G * c = -(10 * G)
        → (q + c) % 2 = 0) := by
  interval_cases t <;> interval_cases h <;> interval_cases s <;>
    rcases show q % 2 = 0 ∨ q % 2 = 1 from by omega with hq | hq <;>
      rw [hq] at hc <;> norm_num at hc <;> subst hc <;> omega

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
  obtain ⟨hh, hst⟩ := guard_le_one f e p
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hex := exact_eq f e p (by have := shift_bits_ge hs.1; omega)
  have hdev := dev_bounds f e p hin.sig.2
  have hslack : (slack e p : ℤ) < halfStep e p := slack_lt_half_step e p hs.1
  set c : ℕ := if half f e p = 1 ∧ (sticky f e p = 1 ∨ integral f e p % 2 = 1)
    then 1 else 0 with hc
  have hround : roundEven (packed f e p) = integral f e p + c :=
    round_even_packed f e p
  have hdist : fineDist f e p = halfStep e p * half f e p + dev f e p
      - 2 * halfStep e p * c := by
    simp only [fineDist]
    rw [hround, hex, step_cast]
    push_cast
    ring
  obtain ⟨hlo, hhi, hup, hdown⟩ := dist_bound (G := (halfStep e p : ℤ))
    (dev := dev f e p) (h := half f e p) (s := sticky f e p) (c := c)
    (i := integral f e p) hh hst (by omega) hdev.2
    (dev_pos_of_sticky f e p hin.sig.2) (dev_eq_zero f e hin p hp) hc
  rw [hdist, hround]
  exact ⟨hlo, hhi, fun htie => htie.elim hup hdown⟩

/-- The same for the reround's candidate, with a step of its own grid. -/
theorem coarse_within_half (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    -(10 * (halfStep e p : ℤ)) ≤ coarseDist f e p
      ∧ coarseDist f e p ≤ 10 * halfStep e p
      ∧ (coarseDist f e p = 10 * halfStep e p
          ∨ coarseDist f e p = -(10 * (halfStep e p : ℤ))
        → roundEven (demote (packed f e p)) % 2 = 0) := by
  obtain ⟨hh, hst⟩ := guard_le_one f e p
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hex := exact_eq f e p (by have := shift_bits_ge hs.1; omega)
  have hdev := dev_bounds f e p hin.sig.2
  have hslack : (slack e p : ℤ) < halfStep e p := slack_lt_half_step e p hs.1
  set c : ℕ := if 6 ≤ integral f e p % 10
      ∨ (integral f e p % 10 = 5 ∧ (half f e p = 1 ∨ sticky f e p = 1
        ∨ integral f e p / 10 % 2 = 1))
    then 1 else 0 with hc
  have hround : roundEven (demote (packed f e p)) = integral f e p / 10 + c :=
    round_even_demote f e p
  have hsplit : (integral f e p : ℤ)
      = 10 * (integral f e p / 10 : ℕ) + (integral f e p % 10 : ℕ) := by omega
  rw [hsplit] at hex
  have hdist : coarseDist f e p = 2 * halfStep e p * (integral f e p % 10)
      + halfStep e p * half f e p + dev f e p - 20 * halfStep e p * c := by
    simp only [coarseDist]
    rw [hround, hex, step_cast]
    push_cast
    ring
  obtain ⟨hlo, hhi, hup, hdown⟩ := dist_bound_coarse (G := (halfStep e p : ℤ))
    (dev := dev f e p) (h := half f e p) (s := sticky f e p) (c := c)
    (t := integral f e p % 10) (q := integral f e p / 10) hh hst (by omega)
    (by omega) hdev.2 (dev_pos_of_sticky f e p hin.sig.2)
    (fun ht hhalf hsticky =>
      dev_eq_zero_coarse f e hin p hp hhalf hsticky ht) hc
  rw [hdist, hround]
  exact ⟨hlo, hhi, fun htie => htie.elim hup hdown⟩

/-! ## Normalization

`to_decimal` picks the scale from the exponent alone, so the significand has to
fill its box before the call. `normalize` shifts it there and the exponent pays
the shift, which leaves the value alone; the value is all the specification
reads of the pair, so what holds of the normalized pair holds of the input.
-/

/-- `normalize` fills the significand's box: the leading bit goes to bit 52, and
    the shift that takes it there is at most 52, so the exponent it spends
    reaches no further than 52 below `emin`. -/
theorem normalized_of_input {f : ℕ} {e : ℤ} (hin : Input f e) :
    Normalized (f * 2 ^ normShift f) (e - normShift f) := by
  obtain ⟨hpos, hlt⟩ := hin.sig
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
  · have := hin.exp
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

/-- The reported significand is correctly rounded on the grid reported with
    it. -/
theorem rounds_to_nearest (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    CorrectlyRounded f e (rounded f e p).1 (rounded f e p).2 := by
  have hs := point_shift_bounds p (by simpa using hp) e
    (by simpa using hin.exp)
  have hstep := step_cast e p
  by_cases hover : roundEven (packed f e p) < 10 ^ p
  · obtain ⟨hlo, hhi, heven⟩ := fine_within_half f e hin p hp
    simp only [fineDist] at hlo hhi heven
    obtain ⟨hd, hk⟩ := to_decimal_fine hover
    rw [hd, hk]
    exact correctly_rounded_of_dist (step_pos e p) (value_scaled f e p hs.1)
      ⟨by omega, by omega⟩
      fun htie => heven (htie.imp (fun h => by omega) fun h => by omega)
  · obtain ⟨hlo, hhi, heven⟩ := coarse_within_half f e hin p hp
    simp only [coarseDist] at hlo hhi heven
    obtain ⟨hd, hk⟩ := to_decimal_coarse hover
    rw [hd, hk]
    exact correctly_rounded_of_dist (m := 10 * step e p)
      (by have := step_pos e p; omega) (value_scaled_coarse f e p hs.1)
      ⟨by push_cast; omega, by push_cast; omega⟩
      fun htie => heven (htie.imp (fun h => by push_cast at h; omega)
        fun h => by push_cast at h; omega)

/-- The reported significand has the digits asked for. The lower bound in the
    reround's branch comes from the branch itself: the significand it rerounds
    had one digit too many. -/
theorem digit_count (f : ℕ) (e : ℤ) (hin : Normalized f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    10 ^ (p - 1) ≤ (rounded f e p).1 ∧ (rounded f e p).1 < 10 ^ p := by
  obtain ⟨hgridlo, hgridhi⟩ := exact_bounds f e hin p hp
  obtain ⟨hflo, hfhi, -⟩ := fine_within_half f e hin p hp
  simp only [fineDist] at hflo hfhi
  have hspos : 0 < step e p := step_pos e p
  have hstep := step_cast e p
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
  by_cases hover : roundEven (packed f e p) < 10 ^ p
  · rw [(to_decimal_fine hover).1]
    refine ⟨?_, hover⟩
    -- Below `10^(p-1)` the candidate would be more than half a step short.
    by_contra hlt
    have h1 : (roundEven (packed f e p) : ℤ) + 1 ≤ (10 : ℤ) ^ (p - 1) := by
      have : roundEven (packed f e p) + 1 ≤ 10 ^ (p - 1) := by omega
      exact_mod_cast this
    have h2 : ((roundEven (packed f e p) : ℤ) + 1) * step e p
        ≤ (10 : ℤ) ^ (p - 1) * step e p :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have : (0 : ℤ) < halfStep e p := by omega
    linarith
  · obtain ⟨hclo, hchi, -⟩ := coarse_within_half f e hin p hp
    simp only [coarseDist] at hclo hchi
    rw [(to_decimal_coarse hover).1]
    -- The rerounded significand is a tenth of one that had `p + 1` digits.
    have hbig : (10 : ℤ) ^ p ≤ (roundEven (packed f e p) : ℤ) := by
      have : 10 ^ p ≤ roundEven (packed f e p) := by omega
      exact_mod_cast this
    have hbig' : (10 : ℤ) ^ p * step e p
        ≤ (roundEven (packed f e p) : ℤ) * step e p :=
      mul_le_mul_of_nonneg_right hbig (by positivity)
    constructor
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

/-- The pair zmij returns denotes the pair above: `dec_sig · 10^(18 - p)`
    against the leading digit's exponent is `d · 10^k`, the padding on one side
    paying for the shift on the other. -/
theorem reported_eq (d : ℕ) (k : ℤ) (p : ℕ) (hp : 1 ≤ p ∧ p ≤ 18) :
    ((d * 10 ^ (18 - p) : ℕ) : ℚ) * 10 ^ (k + (p : ℤ) - 18)
      = (d : ℚ) * 10 ^ k := by
  have hpow : ((10 : ℚ) ^ (18 - p)) = 10 ^ ((18 : ℤ) - (p : ℤ)) := by
    rw [← zpow_natCast]
    congr 1
    omega
  push_cast
  rw [hpow, mul_assoc, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
  congr 2
  omega

/-- zmij converts a positive finite binary64 to a chosen precision correctly:
    the significand it reports has the digits asked for and is correctly rounded
    on the grid reported with it. -/
theorem correct (f : ℕ) (e : ℤ) (hin : Input f e) (p : ℕ)
    (hp : 1 ≤ p ∧ p ≤ 18) :
    let (d, k) := toDecimal f e p
    10 ^ (p - 1) ≤ d ∧ d < 10 ^ p ∧ CorrectlyRounded f e d k :=
  have hn := normalized_of_input hin
  ⟨(digit_count _ _ hn p hp).1, (digit_count _ _ hn p hp).2,
    correctly_rounded_of_normalized (rounds_to_nearest _ _ hn p hp)⟩

end zmij.precision
