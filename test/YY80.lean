-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import YY
import Mathlib.Tactic.IntervalCases

/-! # Correctness of yy at the x87 80-bit format

`YY.lean` proves `YY.correct_of`, that yy implements `Core.lean`'s exact
selection rule at any format satisfying two records of side conditions.
`YY128.lean` discharges those records at binary128; this file does the same at
the x87 80-bit format and applies the theorem. Like that one it contains no
mathematics: every declaration is either a finite check or the one-line
instantiation at the end.

The 80-bit format shares binary128's 15-bit exponent, its `width`, and its two
fixed-point logarithms — zmij runs one code path at both — so the checks come
out the same shape and size: `Layout binary80` is two inequalities between the
parameters, and `Checks binary80` is six facts at each of 32,766 exponents, over
a 256-bit table whose exact powers of ten reach about 16,600 bits. What differs
is the significand box, `2^64` against binary128's `2^113`, and that makes this
the easier of the two but not the cheaper: the numbers the kernel checks are the
same width either way.

## Why it is not in the default build

The checks below run for about four minutes. Nothing else depends on this file,
so it is a `lean_lib` of its own, absent from `defaultTargets`: `lake build` is
unaffected and `lake build YY80` is the explicit request to verify the 80-bit
format.

## What the four minutes are spent on

|  | count | cost |
|---|---|---|
| `shift_nonneg_sweep` | 32,766 | 11s |
| `Power10Normalized` | 9,865 indices, to 16.6 kbit | 4s |
| `trim_sweep` | 32,766, to 16.6 kbit | 25s |
| `exp_refuted`, `one_refuted` | 32,766 certificates each | ~3 min |

As at binary128 the multiplier is found by `ModWindows.search` during
elaboration and only the literal reaches the proof term, so the kernel checks
`refutedBy` and never repeats the Euclidean search. What the narrower
significand buys shows up in the search and not in the check: no problem here
needs more than 58 of the 160 steps the search is given.

## Why a certificate suffices at every exponent

binary128 has one exponent where a significand's gap lands inside a coarse
window, so no multiplier refutes the box there and `YY128.lean` spends a section
on that exponent alone. Nothing of the kind is needed here, and the significand
is why: dropping `width + 4 = 132` of the table's 256 bits leaves a window of
relative width `2^-127.3`, and against a box of `2^64` that is `2^-63` expected
occupants per window per exponent, or about `2^-46` over the whole range.
binary128's `2^-15` per window per exponent is what adds up to a handful over
the same range, one of which is real.
-/

namespace YY80

open YY

set_option maxHeartbeats 0

-- The kernel folds each sweep over a list of 32,766 exponents, which is sixteen
-- times the default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## Finite arithmetic checks

`Layout`, and the four `Checks` fields that a decision procedure closes
outright. The two that need a searched witness are below.
-/

/-- The packing conditions, both with room to spare at
    `(prec, width) = (64, 128)`. -/
theorem layout : Layout binary80 := ⟨by decide, by decide⟩

/-- Exposes the literals: `binary80` is a structure literal, and `omega` treats
    a projection of one as an opaque atom. -/
private theorem shift_raw_eq (e : ℤ) :
    shiftRaw (⟨e⟩ : FPExp binary80)
      = e + (-(e * 20_201_781 / 2 ^ 26) * 55_732_705) / 2 ^ 24 := rfl

/-- The shift leaves the four-bit digit slot intact. A magnitude fact, so the
    constants give it to `omega` directly. -/
private theorem shift_lt_four (e : ℤ) (hlo : -16445 ≤ e) (hhi : e ≤ 16320) :
    exponentShift (⟨e⟩ : FPExp binary80) < 4 := by
  show (shiftRaw (⟨e⟩ : FPExp binary80)).toNat < 4
  rw [shift_raw_eq]
  omega

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. Unlike the bound
    above this is not a magnitude fact: the two constants multiply to just over
    one, by a part in `2^27.5`, which leaves `omega`'s rational relaxation room
    to admit a shift of `-1`. Ruling that out is Diophantine, hence checked. -/
private theorem shift_nonneg_sweep :
    ∀ e ∈ Finset.Icc (-16445 : ℤ) 16320,
      0 ≤ shiftRaw (⟨e⟩ : FPExp binary80) := by
  decide +kernel

/-- The table entry at every index yy can read is a normalized 256-bit number.
    The 80-bit exponents run higher and the index is the negated decimal
    exponent, so these indices sit about fifteen below binary128's and the sweep
    is its own rather than a corollary of that one. -/
instance : binary80.Power10Normalized where
  ratio := by decide +kernel

private theorem table (e : ℤ) (hlo : -16445 ≤ e) (hhi : e ≤ 16320) :
    TableNormalized (⟨e⟩ : FPExp binary80) :=
  binary80.power10_ratio_normalized hlo hhi
    (-binary80.decimalExponent e) (by omega)

/-- Three facts about the truncation: that the packed comparison's modulus is
    not reached, and that the error `num % den` fits the bits the comparison
    discards, measured from either end of the window unit. -/
private theorem trim_sweep :
    ∀ e ∈ Finset.Icc (-16445 : ℤ) 16320,
      trimChecksHold (⟨e⟩ : FPExp binary80) = true := by
  decide +kernel

/-! ## Modular certificates

One modular question per exponent per family. `modCertTactic` reads the index
out of the goal, unwrapping the bundled exponent, so each family still costs
one `elab` line.
-/

/-- Close `∃ q, (expWindows e).refutedBy q = true` for a literal exponent. -/
elab "exp_cert80" : tactic =>
  modCertTactic fun e => (expWindows (⟨e⟩ : FPExp binary80)).search

/-- Close `∃ q, (oneWindows e).refutedBy q = true` for a literal exponent. -/
elab "one_cert80" : tactic =>
  modCertTactic fun e => (oneWindows (⟨e⟩ : FPExp binary80)).search

private theorem exp_refuted (e : ℤ) (hlo : -16445 ≤ e) (hhi : e ≤ 16320) :
    ∃ q, (expWindows (⟨e⟩ : FPExp binary80)).refutedBy q = true := by
  interval_cases e <;> exp_cert80

private theorem one_refuted (e : ℤ) (hlo : -16445 ≤ e) (hhi : e ≤ 16320) :
    ∃ q, (oneWindows (⟨e⟩ : FPExp binary80)).refutedBy q = true := by
  interval_cases e <;> one_cert80

/-! ## Instantiation -/

theorem checks : Checks binary80 := by
  rintro ⟨e⟩ hlo hhi
  have hlo' : (-16445 : ℤ) ≤ e := hlo
  have hhi' : e ≤ 16320 := hhi
  have he : e ∈ Finset.Icc (-16445 : ℤ) 16320 := Finset.mem_Icc.mpr ⟨hlo', hhi'⟩
  exact
    { shift_nonneg := shift_nonneg_sweep e he
      shift_lt_four := shift_lt_four e hlo' hhi'
      table := table e hlo' hhi'
      trim := trim_checks_of_hold _ (trim_sweep e he)
      coarse_resolved := fun f hr =>
        Or.inl (exp_avoids_of_cert f _ hr (exp_refuted e hlo' hhi').choose_spec)
      one_refuted := one_refuted e hlo' hhi' }

/-- yy is correct on regularly spaced positive x87 80-bit values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid.

    `YY.correct` is the same sentence at binary64 and `YY128.correct` at
    binary128. -/
theorem correct (f : ℕ) (e : ℤ) (hr : binary80.Regular f e) :
    let (d, k) := toDecimal f (⟨e⟩ : FPExp binary80)
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' :=
  correct_of layout checks f ⟨e⟩ hr

end YY80
