-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import yy

/-! # Correctness of yy at binary128

`yy.lean` proves `yy.correct_of`, that yy implements `core.lean`'s exact
selection rule at any format satisfying two records of side conditions. This
file discharges those records at IEEE 754 binary128 and applies the theorem,
giving `correct`, binary64's sentence at the wider format. It contains no
mathematics: every declaration is either a finite check or the one-line
instantiation at the end.

The split is the one from `yy.lean`'s header — algebraic identities are
parameterized, numerical approximation properties are checked — and this file is
the checking half at the wider format. `Layout binary128` is two inequalities
between the parameters. `Checks binary128` is six facts at each of binary128's
32,766 exponents, and where binary64 needs 2,046 of each, the numbers involved
are also four times as wide: the exact power of ten at the extremes of the range
runs to about 16,500 bits. That is the whole reason this file exists separately.

## Why it is not in the default build

The checks below run for about four minutes, against 17 seconds for binary64's.
Nothing else depends on this file, so it is a `lean_lib` of its own, absent from
`defaultTargets`: `lake build` is unaffected and `lake build yy128` is the
explicit request to verify binary128.

## What the four minutes are spent on

|  | count | cost |
|---|---|---|
| `shift_nonneg_sweep` | 32,766 | 11s |
| `table_sweep` | 9,865 indices, to 16.5 kbit | 5s |
| `trim_sweep` | 32,766, to 16.5 kbit | 28s |
| `exp_refuted`, `one_refuted` | 32,766 certificates each | ~3 min |

The certificates are the point of the exercise and are also where the cost is
least obvious, so it is worth saying where it does *not* go. The multiplier is
found by `ModWindows.search` during elaboration and only the literal reaches the
proof term, so the kernel checks `refutedBy` and never runs the Euclidean search.
That division matters more at this width than at binary64's: having the kernel
search as well costs about 395ms per certificate against 4ms for checking one,
which would turn three minutes into seven hours.

The underlying Diophantine problem is *easier* here, not harder. The window width
relative to the modulus falls from about `2^-63` to about `2^-127` while the
significand box only grows to `2^113`, so certificates are found sooner — within
74 Euclidean steps, against binary64's 44. The cost is entirely that there are
sixteen times as many of them and each is four times as wide.

## Why the comparisons are finer here

Both of yy's near-boundary comparisons read more of the product at this format
than yy itself does, which is what `packedBits` and `packedBitsU` record. The
trim-down one re-reads all four bits that packing drops, the trim-up one a
single bit, and neither setting is free to move.

The reason is that a window's width is the granularity of the comparison that
owns it, so a coarser comparison is one whose windows are wider, and a window
wide enough to catch a significand is one no multiplier can refute. Dropping
`width + 4 = 132` of the table's 256 bits leaves a window of relative width
`2^-127.3` against a significand box of `2^112`, so an occupant is expected
about once in `2^15` windows. Over 32,766 exponents and four windows each that
is a handful, and with the trim-up comparison left as coarse as yy's, one is
real: at `e = -2266` a significand sits at 0.59 of the band above
`scale - num`. One bit of trim-up refinement halves the band and evicts it,
which is why `packedBitsU` is three and not four.

It cannot be more than one bit either, in the other direction: at two the
truncation error outgrows what `TrimChecks` can bound, at one exponent. So
`(0, 3)` is the only setting at which both halves of the argument hold, and
`(4, 4)` — yy's own — is what binary64 keeps, its `2^-11.3` margin over 2,046
exponents leaving it with no occupant to evict.
-/

namespace yy128

open yy

set_option maxHeartbeats 0

-- The kernel folds each sweep over a list of 32,766 exponents, which is sixteen
-- times the default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## The layout

The packing conditions, both with room to spare at `(prec, width) = (113, 128)`.
-/

theorem layout : Layout binary128 := ⟨by decide, by decide⟩

/-! ## The fixed-point logarithms

Three facts that follow from the constants by integer arithmetic once `omega` can
see them. The `rfl` lemmas exist only to expose the literals: `binary128` is a
structure literal, and `omega` treats a projection of one as an opaque atom.
-/

private theorem dec_exp_eq (e : ℤ) :
    binary128.decimalExponent e = e * 20_201_781 / 2 ^ 26 := rfl

private theorem shift_raw_eq (e : ℤ) :
    shiftRaw (⟨e⟩ : FPExp binary128)
      = e + (-(e * 20_201_781 / 2 ^ 26) * 55_732_705) / 2 ^ 24 := rfl

/-- The decimal exponent's range, which bounds the table indices the sweep below
    has to cover. -/
private theorem dec_exp_range (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    -4966 ≤ binary128.decimalExponent e ∧ binary128.decimalExponent e ≤ 4898 := by
  rw [dec_exp_eq]
  omega

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

/-! ## The table

`core.lean`'s sweep covers binary64's 618 indices and stays there because two
algorithms share it. binary128's is yy's alone, and the numbers are wide enough
that it belongs with the rest of the cost.
-/

/-- The table entry at every index yy can read is a normalized 256-bit number. -/
private theorem table_sweep :
    ∀ k ∈ Finset.Icc (-4898 : ℤ) 4966,
      2 ^ 255 * binary128.power10Den k ≤ binary128.power10Num k ∧
        binary128.power10Num k < 2 ^ 256 * binary128.power10Den k := by
  decide +kernel

private theorem table (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    TableNormalized (⟨e⟩ : FPExp binary128) := by
  obtain ⟨h1, h2⟩ := dec_exp_range e hlo hhi
  exact table_sweep (-binary128.decimalExponent e)
    (by simp only [Finset.mem_Icc]; omega)

/-! ## The truncated power of ten

Three facts about the truncation: that the packed comparison's modulus is not
reached, and that the error `num % den` fits the bits the comparison discards,
measured from either end of the window unit.
-/

private theorem trim_sweep :
    ∀ e ∈ Finset.Icc (-16494 : ℤ) 16271,
      trimChecksHold (⟨e⟩ : FPExp binary128) = true := by
  decide +kernel

/-! ## The certificates

One modular question per exponent per family. `modCertTactic` reads the index
out of the goal, unwrapping the bundled exponent, so each family still costs
one `elab` line.
-/

/-- Close `∃ q, (expWindows e).refutedBy q = true` for a literal exponent. -/
elab "exp_cert128" : tactic =>
  modCertTactic fun e => (expWindows (⟨e⟩ : FPExp binary128)).search

/-- Close `∃ q, (oneWindows e).refutedBy q = true` for a literal exponent. -/
elab "one_cert128" : tactic =>
  modCertTactic fun e => (oneWindows (⟨e⟩ : FPExp binary128)).search

private theorem exp_refuted (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (expWindows (⟨e⟩ : FPExp binary128)).refutedBy q = true := by
  interval_cases e <;> exp_cert128

private theorem one_refuted (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (oneWindows (⟨e⟩ : FPExp binary128)).refutedBy q = true := by
  interval_cases e <;> one_cert128

/-! ## The instantiation -/

theorem checks : Checks binary128 := by
  rintro ⟨e⟩ hlo hhi
  have hlo' : (-16494 : ℤ) ≤ e := hlo
  have hhi' : e ≤ 16271 := hhi
  exact
    { shift_nonneg :=
        shift_nonneg_sweep e (by simp only [Finset.mem_Icc]; omega)
      shift_lt_four := shift_lt_four e hlo' hhi'
      table := table e hlo' hhi'
      trim := trim_checks_of_hold _
        (trim_sweep e (by simp only [Finset.mem_Icc]; omega))
      exp_refuted := exp_refuted e hlo' hhi'
      one_refuted := one_refuted e hlo' hhi' }

/-- yy is correct on regularly spaced positive binary128 values: after removing
    trailing zeros its output is a shortest decimal representation that
    round-trips, and it is correctly rounded on its own decimal grid.

    `yy.correct` is the same sentence at binary64. -/
theorem correct (f : ℕ) (e : ℤ) (hr : binary128.Regular f e) :
    let (d, k) := toDecimal f (⟨e⟩ : FPExp binary128)
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' :=
  correct_of layout checks f ⟨e⟩ hr

end yy128
