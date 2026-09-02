-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import YY
import Mathlib.Tactic.IntervalCases

/-! # Correctness of yy at binary128

`YY.lean` proves `YY.correct_of`, that yy implements `Core.lean`'s exact
selection rule at any format satisfying two records of side conditions. This
file discharges those records at IEEE 754 binary128 and applies the theorem.
Almost every declaration is a finite check or the one-line instantiation at the
end; the exception is the recentring the last section needs, which no other
format has any use for.

The split is the one from `YY.lean`'s header — algebraic identities are
parameterized, numerical approximation properties are checked — and this file is
the checking half at the wider format. `Layout binary128` is two inequalities
between the parameters. `Checks binary128` is six facts at each of binary128's
32,766 exponents, sixteen times the 2,046 binary64 needs. That count is the
whole reason this file exists separately; the numbers involved are also four
times as wide — the exact power of ten at the extremes of the range runs to
about 16,500 bits — but width turns out to cost nothing, for the reason the
section below gives.

## Why it is not in the default build

The checks below run for about four minutes, against 17 seconds for binary64's.
Nothing else depends on this file, so it is a `lean_lib` of its own, absent from
`defaultTargets`: `lake build` is unaffected and `lake build YY128` is the
explicit request to verify binary128.

## What the four minutes are spent on

|  | count | cost |
|---|---|---|
| `shift_nonneg_sweep` | 32,766 exponents | 11s |
| `Power10Normalized` | 9,865 indices | 5s |
| `trim_sweep` | 32,766 exponents | 28s |
| `exp_refuted`, `one_refuted` | 32,766 certificates each | ~3 min |

Three quarters of the four minutes is the kernel reducing closed terms, and what
that costs is the number of arithmetic operations rather than their width: it
spends tens of microseconds unfolding the instance and `Decidable` layers around
an operation, and a fraction of one performing it on GMP integers. A
`trimChecksHold` exponent costs about 0.5ms and a certificate about 2ms at
either end of the range, which is what binary64's certificates cost too, on
numbers a fraction of the width.

The certificates are the point of the exercise and are also where the cost is
least obvious, so it is worth saying where it does *not* go. The multiplier is
found by `ModWindows.search` during elaboration and only the literal reaches the
proof term, so the kernel checks `refutedBy` and never runs the Euclidean
search: letting it search as well costs about 13ms per certificate against the
2ms of checking one. The remainder of a certificate is the machinery around it,
about 0.3ms for `interval_cases` to produce the case and 0.2ms for the search,
so a fifth of the three minutes is elaboration rather than kernel time.

The underlying Diophantine problem is *easier* here, not harder. The window width
relative to the modulus falls from about `2^-63` to about `2^-127` while the
significand box only grows to `2^113`, so certificates are found sooner — within
74 Euclidean steps, against binary64's 44. The cost is entirely that there are
sixteen times as many of them.

## The one exponent that needs more than a certificate

At `e = -2266` a significand's gap lands inside a coarse window, so no
multiplier refutes the box there and `exp_refuted` cannot be a certificate. The
margin is thin by construction: dropping `width + 4 = 132` of the table's 256
bits leaves a window of relative width `2^-127.3` against a significand box of
`2^113`, so the expected number of occupants is `2^-15` per window per exponent.
Over 32,766 exponents that is a handful, and one of them is real. binary64 has
the same structure with a `2^-11.3` margin over 2,046 exponents and no such
case, which is why it needs none of what follows.

yy is right at the `occupant` — the window records that the coarse comparison's
error bound does not *establish* as much. So the exponent is split: the occupant
supplies `TrimsAgree` by evaluation, and `exp_avoids_of_blocks` covers the rest
of the box with 113 certificates per side, over the distances from it rather
than the significands themselves. Both are confined to this one exponent, and
the rest of the range is unaffected.
-/

namespace YY128

open YY

set_option maxHeartbeats 0

-- The kernel folds each sweep over a list of 32,766 exponents, which is sixteen
-- times the default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## Layout -/

/-- The packing conditions, both with room to spare at
    `(prec, width) = (113, 128)`. -/
theorem layout : Layout binary128 := ⟨by decide, by decide⟩

/-! ## Checks

Six facts at every exponent in range. Four are closed computations; the last
two ask for a modular certificate at each exponent, and one exponent needs more
than a certificate.
-/

/-! ### Direct checks -/

/-- Exposes the literals: `binary128` is a structure literal, and `omega` treats
    a projection of one as an opaque atom. -/
private theorem shift_raw_eq (e : ℤ) :
    shiftRaw (⟨e⟩ : FPExp binary128)
      = e + (-(e * 20_201_781 / 2 ^ 26) * 55_732_705) / 2 ^ 24 := rfl

/-- The shift leaves the four-bit digit slot intact. A magnitude fact, so the
    constants give it to `omega` directly. -/
private theorem shift_lt_four (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    exponentShift (⟨e⟩ : FPExp binary128) < 4 := by
  show (shiftRaw (⟨e⟩ : FPExp binary128)).toNat < 4
  rw [shift_raw_eq]
  omega

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. Unlike the bound
    above this is not a magnitude fact: the two constants multiply to just over
    one, by a part in `2^27.5`, which leaves `omega`'s rational relaxation room
    to admit a shift of `-1`. Ruling that out is Diophantine, hence checked. -/
private theorem shift_nonneg_sweep :
    ∀ e ∈ Finset.Icc (-16494 : ℤ) 16271,
      0 ≤ shiftRaw (⟨e⟩ : FPExp binary128) := by
  decide +kernel

/-- The table entry at every index yy can read is a normalized 256-bit number.
    `Core.lean` keeps binary64's sweep because two algorithms share it; this one
    is yy's alone, and wide enough to belong with the rest of the cost. -/
instance : binary128.Power10Normalized where
  ratio := by decide +kernel

/-- Three facts about the truncation: that the packed comparison's modulus is
    not reached, and that the error `num % den` fits the bits the comparison
    discards, measured from either end of the window unit. -/
private theorem trim_sweep :
    ∀ e ∈ Finset.Icc (-16494 : ℤ) 16271,
      trimChecksHold (⟨e⟩ : FPExp binary128) = true := by
  decide +kernel

/-! ### Unit-step windows

One modular question per exponent, refuted everywhere in range. `modCertTactic`
reads the index out of the goal, unwrapping the bundled exponent, so the family
costs one `elab` line.
-/

/-- Close `∃ q, (oneWindows e).refutedBy q = true` for a literal exponent. -/
elab "one_cert128" : tactic =>
  modCertTactic fun e => (oneWindows (⟨e⟩ : FPExp binary128)).search

private theorem one_refuted (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (oneWindows (⟨e⟩ : FPExp binary128)).refutedBy q = true := by
  interval_cases e <;> one_cert128

/-! ### Exponent windows

The same, except at `e = -2266`. These two cover the range on either side of
it; the exponent itself is below.
-/

/-- Close `∃ q, (expWindows e).refutedBy q = true` for a literal exponent. -/
elab "exp_cert128" : tactic =>
  modCertTactic fun e => (expWindows (⟨e⟩ : FPExp binary128)).search

private theorem exp_refuted_below (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ -2267) :
    ∃ q, (expWindows (⟨e⟩ : FPExp binary128)).refutedBy q = true := by
  interval_cases e <;> exp_cert128

private theorem exp_refuted_above (e : ℤ) (hlo : -2265 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (expWindows (⟨e⟩ : FPExp binary128)).refutedBy q = true := by
  interval_cases e <;> exp_cert128

/-! #### The exceptional exponent

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

The recentred problem is posed against a format, like the one it replaces:
nothing in it is binary128's except the occupant it is aimed at.
-/

variable {fmt : Format}

/-- The residue `expWindows` reads at a significand. -/
def expResidue (b : ℕ) (e : FPExp fmt) : ℕ := 2 * trimNum e * b % trimScale e

/-- `expWindows` seen by the significands a distance `2^i ≤ d < 2^(i+1)` above
    `b`, indexed by that distance and with the windows measured from `b`'s own
    residue. The block index comes last, where a certificate search expects to
    find the quantity it varies. -/
def expWindowsAbove (b : ℕ) (e : FPExp fmt) (i : ℕ) : ModWindows :=
  { expWindows e with
    fmin := 2 ^ i
    fmax := 2 ^ (i + 1) - 1
    windows := (expWindows e).windows.map fun p =>
      (p.1 - expResidue b e, p.2 - expResidue b e) }

/-- And by those below, where the distance runs the other way, so the offsets
    are negated. -/
def expWindowsBelow (b : ℕ) (e : FPExp fmt) (i : ℕ) : ModWindows :=
  { expWindows e with
    fmin := 2 ^ i
    fmax := 2 ^ (i + 1) - 1
    windows := (expWindows e).windows.map fun p =>
      (expResidue b e - p.2, expResidue b e - p.1) }

/-- Certificates for every block around `b` do what one for the whole box
    would, at every significand but `b` itself. -/
theorem exp_avoids_of_blocks {b : ℕ} (f : ℕ) (e : FPExp fmt)
    (hr : fmt.Regular f e) (hne : f ≠ b) (hbp : b < 2 ^ fmt.prec)
    (ha : ∀ i < fmt.prec, ∃ q, (expWindowsAbove b e i).refutedBy q = true)
    (hb : ∀ i < fmt.prec, ∃ q, (expWindowsBelow b e i).refutedBy q = true) :
    ExpAvoids f e := by
  intro hwrap rmin rmax hmem
  by_contra hcon
  push Not at hcon
  obtain ⟨hrmin, hrmax⟩ := hcon
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
      (rmin := (expResidue b e : ℤ) - rmax)
      (rmax := (expResidue b e : ℤ) - rmin)
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
      (rmin := rmin - (expResidue b e : ℤ))
      (rmax := rmax - (expResidue b e : ℤ))
      (List.mem_map_of_mem (f := fun p : ℤ × ℤ =>
        (p.1 - (expResidue b e : ℤ), p.2 - (expResidue b e : ℤ))) hmem)
      hd0 hd1 hy (by omega) (by omega)

/-- The significand occupying the trim-up window, the band just above
    `scale - num`. -/
def occupant : ℕ := 6098265699439592702088126713856255

/-- The coarse classifier at the occupant agrees with the exact one. At a fixed
    exponent and significand that is a closed computation, which is the whole
    reason this exponent can be finished at all. -/
private theorem occupant_trims_agree :
    TrimsAgree occupant (⟨-2266⟩ : FPExp binary128) := by
  unfold TrimsAgree
  decide +kernel

/-- Close `∃ q, (expWindowsAbove occupant _ i).refutedBy q = true` for a literal
    block. -/
elab "block_above_cert" : tactic =>
  modCertTactic fun i =>
    (expWindowsAbove occupant (⟨-2266⟩ : FPExp binary128) i.toNat).search

/-- Close `∃ q, (expWindowsBelow occupant _ i).refutedBy q = true` for a literal
    block. -/
elab "block_below_cert" : tactic =>
  modCertTactic fun i =>
    (expWindowsBelow occupant (⟨-2266⟩ : FPExp binary128) i.toNat).search

private theorem above_refuted (i : ℕ) (hi : i < binary128.prec) :
    ∃ q, (expWindowsAbove occupant (⟨-2266⟩ : FPExp binary128) i).refutedBy
      q = true := by
  change i < 113 at hi
  interval_cases i <;> block_above_cert

private theorem below_refuted (i : ℕ) (hi : i < binary128.prec) :
    ∃ q, (expWindowsBelow occupant (⟨-2266⟩ : FPExp binary128) i).refutedBy
      q = true := by
  change i < 113 at hi
  interval_cases i <;> block_below_cert

private theorem exp_refuted (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271)
    (f : ℕ) (hr : binary128.Regular f e) :
    ExpAvoids f (⟨e⟩ : FPExp binary128)
      ∨ TrimsAgree f (⟨e⟩ : FPExp binary128) := by
  rcases lt_trichotomy e (-2266) with h | h | h
  · exact Or.inl (exp_avoids_of_cert f _ hr
      (exp_refuted_below e hlo (by omega)).choose_spec)
  · subst h
    rcases eq_or_ne f occupant with rfl | hne
    · exact Or.inr occupant_trims_agree
    · exact Or.inl (exp_avoids_of_blocks f _ hr hne (by decide +kernel)
        above_refuted below_refuted)
  · exact Or.inl (exp_avoids_of_cert f _ hr
      (exp_refuted_above e (by omega) hhi).choose_spec)

/-! ### The record -/

theorem checks : Checks binary128 := by
  rintro ⟨e⟩ hlo hhi
  change (-16494 : ℤ) ≤ e at hlo
  change e ≤ 16271 at hhi
  have he : e ∈ Finset.Icc (-16494 : ℤ) 16271 := Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  exact
    { shift_nonneg := shift_nonneg_sweep e he
      shift_lt_four := shift_lt_four e hlo hhi
      table :=
        binary128.power10_ratio_normalized hlo hhi
          (-binary128.decimalExponent e) (by omega)
      trim := trim_checks_of_hold _ (trim_sweep e he)
      exp_refuted := exp_refuted e hlo hhi
      one_refuted := one_refuted e hlo hhi }

/-! ## Correctness -/

/-- yy is correct on regularly spaced positive binary128 values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid.

    `YY.correct` is the same sentence at binary64. -/
theorem correct (f : ℕ) (e : ℤ) (hr : binary128.Regular f e) :
    let (d, k) := toDecimal f (⟨e⟩ : FPExp binary128)
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' :=
  correct_of layout checks f ⟨e⟩ hr

end YY128
