-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

import yy

/-! # Correctness of yy at binary128

`yy.lean` proves `yy.correctOf`, that yy implements `core.lean`'s exact selection
rule at any format satisfying two records of side conditions. This file discharges
those records at IEEE 754 binary128 and applies the theorem. It contains no
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

The checks below run for about ten minutes, against 17 seconds for binary64's.
Nothing else depends on this file, so it is a `lean_lib` of its own, absent from
`defaultTargets`: `lake build` is unaffected and `lake build yy128` is the
explicit request to verify binary128.

## What the ten minutes are spent on

|  | count | cost |
|---|---|---|
| `shift_nonneg_sweep` | 32,766 | 11s |
| `table_sweep` | 9,865 indices, to 16.5 kbit | 9s |
| `trim_sweep` | 32,766, to 16.5 kbit | ~4 min |
| `exp_refuted`, `one_refuted` | 32,766 certificates each | ~5 min |

The certificates are the point of the exercise and are also where the cost is
least obvious, so it is worth saying where it does *not* go. The multiplier is
found by `ModWindows.search` during elaboration and only the literal reaches the
proof term, so the kernel checks `refutedBy` and never runs the Euclidean search.
That division matters more at this width than at binary64's: having the kernel
search as well costs about 395ms per certificate against 4ms for checking one,
which would turn five minutes into seven hours.

The underlying Diophantine problem is *easier* here, not harder. The window width
relative to the modulus falls from about `2^-63` to about `2^-127` while the
significand box only grows to `2^113`, so certificates are found sooner — within
74 Euclidean steps, against binary64's 44. The cost is entirely that there are
sixteen times as many of them and each is four times as wide.

## Status: yy is not correct at binary128 with these parameters

This file does not prove binary128's analogue of `yy.correct`, because that
statement is **false**. At

    f = 6098265699439592702088126713856256,   e = -2266

a normal binary128 value, yy emits a 34-digit decimal that is outside the
half-ULP interval by a relative `2^-127`, while the 35-digit candidate it would
have emitted on the fine path is comfortably inside. `bad_output`,
`bad_output_not_nearest` and `fine_candidate_is_nearest` are that computation, and
`checks_unsatisfiable` derives from it that no instantiation of `yy.correctOf` at
binary128 exists. All are `decide +kernel`; nothing here is a `sorry`.

The failure is a hair's breadth: the packed comparison discards `word + 4 = 132`
of the table's 256 bits, leaving a window of relative width `2^-127.3` against a
significand box of `2^113`, so the expected number of undecidable cases is
`2^-15` per window per exponent. Over 32,766 exponents that is a handful, and one
of them decides the wrong way. binary64 has the same structure with a `2^-11.3`
margin over 2,046 exponents and gets away with it — the control experiment finds
zero such cases there, which is consistent with `yy.correct` being a theorem.

So this is a genuine defect in the binary128 configuration, not in the proof
architecture, and the remedy is a wider table or a narrower window unit rather
than a better certificate search. Everything else is verified:
`correct_away_from_bad` is binary64's sentence at binary128 for every exponent
but `-2266`, over the same sweeps. Nothing about binary64 is affected —
`yy.correct` does not depend on this file.
-/

namespace yy128

open yy

set_option maxHeartbeats 0

-- The kernel folds each sweep over a list of 32,766 exponents, which is sixteen
-- times the default recursion limit's reach.
set_option maxRecDepth 100000

/-! ## The layout

The packing conditions, both with room to spare at `(prec, word) = (113, 128)`.
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
    shiftRaw binary128 e
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
    exponentShift binary128 e < 4 := by
  show (shiftRaw binary128 e).toNat < 4
  rw [shift_raw_eq]
  omega

/-- The shift is nonnegative, so `Int.toNat` does not clamp it. Unlike the bound
    above this is not a magnitude fact: the two constants multiply to just over
    one, by a part in `2^27.5`, which leaves `omega`'s rational relaxation room
    to admit a shift of `-1`. Ruling that out is Diophantine, hence checked. -/
private theorem shift_nonneg_sweep :
    ∀ e ∈ Finset.Icc (-16494 : ℤ) 16271, 0 ≤ shiftRaw binary128 e := by
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
    TableNormalized binary128 e := by
  obtain ⟨h1, h2⟩ := dec_exp_range e hlo hhi
  exact table_sweep (-binary128.decimalExponent e)
    (by simp only [Finset.mem_Icc]; omega)

/-! ## The truncated power of ten

Three facts about the truncation: that the packed comparison's modulus is not
reached, and that the error `num % den` fits the bits the comparison discards,
measured from either end of the window unit.
-/

private theorem trim_sweep :
    ∀ e ∈ Finset.Icc (-16494 : ℤ) 16271, trimChecksHold binary128 e = true := by
  decide +kernel

/-! ## The certificates

One modular question per exponent per family. `modCertTactic` reads the last
argument of the applied problem, so the format argument does not disturb it and
each family still costs one `elab` line.
-/

/-- Close `∃ q, (expWindows binary128 e).refutedBy q = true` for a literal
    exponent. -/
elab "exp_cert128" : tactic =>
  modCertTactic fun e => (expWindows binary128 e).search

/-- Close `∃ q, (oneWindows binary128 e).refutedBy q = true` for a literal
    exponent. -/
elab "one_cert128" : tactic =>
  modCertTactic fun e => (oneWindows binary128 e).search

private theorem exp_refuted_below (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ -2267) :
    ∃ q, (expWindows binary128 e).refutedBy q = true := by
  interval_cases e <;> exp_cert128

private theorem exp_refuted_above (e : ℤ) (hlo : -2265 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (expWindows binary128 e).refutedBy q = true := by
  interval_cases e <;> exp_cert128

/-! ## The counterexample at `e = -2266`

The certificate at `e = -2266` cannot be found because there is nothing to find:
two adjacent significands in the box land inside the coarse windows — one in the
band just above `num`, one in the band just above `scale - num` — and at the
first of them yy's decision is wrong. The facts below are what remains of
`exp_refuted` there, and they are checked, not assumed.

The significand is `2^112 < f < 2^113`, a normal binary128 value at an exponent
well inside the range, so `binary128.Regular f (-2266)` holds. yy takes the
coarse path: `roundD0` fires, and it emits the multiple of ten `decTen`. The
exact trim-down test disagrees — `trimGap` exceeds `trimNum` — and the arithmetic
below says which of the two is right.
-/

/-- The significand at which yy fails. -/
def bad : ℕ := 6098265699439592702088126713856256

/-- It is a regularly spaced binary128 value. -/
theorem bad_regular : binary128.Regular bad (-2266) := by
  refine ⟨⟨by decide, by decide, Or.inl (by decide)⟩, by decide, by decide⟩

/-- What yy emits there: the trim-down candidate, a multiple of ten. -/
theorem bad_output : toDecimal binary128 bad (-2266)
    = (44795683542663963852361293387747210, -683) := by
  decide +kernel

/-- That output is **outside** the half-ULP interval, by `2^2142`. Scaled to
    integers: the value is `bad·2^-2266`, the output is `d·10^-683`, and a half
    ULP is `2^-2267`, so round-tripping means
    `2·|d·2^2266 - bad·10^683| ≤ 10^683`. It fails. -/
theorem bad_output_not_nearest :
    10 ^ 683 < (2 * ((44795683542663963852361293387747210 : ℤ) * 2 ^ 2266
      - (bad : ℤ) * 10 ^ 683)).natAbs := by
  decide +kernel

/-- And it fails avoidably: the candidate yy would have emitted on the fine path
    is comfortably inside. So the shortest round-tripping decimal here has 35
    digits, and yy returns 34 of them. -/
theorem fine_candidate_is_nearest :
    (2 * ((44795683542663963852361293387747214 : ℤ) * 2 ^ 2266
      - (bad : ℤ) * 10 ^ 683)).natAbs < 10 ^ 683 := by
  decide +kernel

/-- Hence `Checks binary128` is not satisfiable: `At binary128 (-2266)` would
    give a refuting multiplier for a window the significand above lands in, and
    `ModWindows.not_hit` turns that into `False`. There is therefore no
    instantiation of `correctOf` at binary128 with these parameters, which is
    the honest reading of this file. -/
theorem checks_unsatisfiable (hc : Checks binary128) : False := by
  obtain ⟨q, hcert⟩ := (hc (-2266) (by decide) (by decide)).exp_refuted
  refine (expWindows binary128 (-2266)).not_hit bad (by decide +kernel) hcert
    (lo := (expWindows binary128 (-2266)).windows[1]!.1)
    (hi := (expWindows binary128 (-2266)).windows[1]!.2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel)

private theorem one_refuted (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) :
    ∃ q, (oneWindows binary128 e).refutedBy q = true := by
  interval_cases e <;> one_cert128

/-! ## What is available away from `e = -2266`

`Checks` quantifies over the whole exponent range and so cannot be built. Every
field of it is nevertheless established at every other exponent, which is what
`atOf` records: `correctOf` applies at any exponent for which `At` holds, so this
is exactly the part of binary128 that is verified.
-/

/-- Every obligation of `At binary128 e`, at every exponent but `-2266`. -/
theorem atOf (e : ℤ) (hlo : -16494 ≤ e) (hhi : e ≤ 16271) (hne : e ≠ -2266) :
    At binary128 e := by
  have hlo' : (-16494 : ℤ) ≤ e := hlo
  have hhi' : e ≤ 16271 := hhi
  exact
    { shift_nonneg :=
        shift_nonneg_sweep e (by simp only [Finset.mem_Icc]; omega)
      shift_lt_four := shift_lt_four e hlo' hhi'
      table := table e hlo' hhi'
      trim := trim_checks_of_hold binary128 e
        (trim_sweep e (by simp only [Finset.mem_Icc]; omega))
      exp_refuted := by
        rcases lt_trichotomy e (-2266) with h | h | h
        · exact exp_refuted_below e hlo' (by omega)
        · exact absurd h hne
        · exact exp_refuted_above e (by omega) hhi'
      one_refuted := one_refuted e hlo' hhi' }

/-- yy is correct on regularly spaced positive binary128 values **at every
    exponent but `-2266`**: after removing trailing zeros its output is a
    shortest decimal representation that round-trips, and it is correctly
    rounded on its own decimal grid.

    Compare `yy.correct`, which is this sentence at binary64 with no exponent
    excluded. The exclusion is not a gap in the proof: `bad_output_not_nearest`
    shows the statement is false at `-2266`. -/
theorem correct_away_from_bad (f : ℕ) (e : ℤ) (hr : binary128.Regular f e)
    (hne : e ≠ -2266) :
    let (d, k) := toDecimal binary128 f e
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  obtain ⟨hlo, hhi⟩ := hr.range
  obtain ⟨hfine, hcoarse⟩ := ulp_scaled_bounds binary128 layout e
    (atOf e hlo hhi hne).shift_nonneg (atOf e hlo hhi hne).shift_lt_four
    (atOf e hlo hhi hne).table (atOf e hlo hhi hne).trim
  exact exact_candidate_correct f e (binary128.decimalExponent e) hr.pos hfine
    hcoarse (exact_candidate binary128 layout f e hr (atOf e hlo hhi hne))

end yy128
