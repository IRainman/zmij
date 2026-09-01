-- Lean proofs for https://github.com/vitaut/zmij/.
--
-- Copyright (c) 2025 - present, Victor Zverovich
-- Distributed under the MIT license (see LICENSE).

-- Field.Power carries the `positivity` extension for `10 ^ (k : ℤ)`, which
-- Mathlib.Tactic.Positivity does not pull in.
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Exact decimal conversion and certified comparisons

Algorithm-independent foundations for verifying shortest decimal conversion.

The first part specifies the problem and states the exact Schubfach-like
selection rule: prefer a multiple of ten that round-trips, and settle for a
nearest grid point otherwise. `exact_candidate_correct` proves that the method
produces a shortest, correctly rounded decimal for any positive value, given
only that the decimal grid is no coarser than one ULP and strictly coarser than
a tenth of one.

The second part is the vocabulary the algorithms share: how a format spaces the
values they convert, which decimal exponent they report, and the normalized
power-of-ten table they multiply by. It is the only part that knows formats
exist, but it is not specific to an algorithm, which is the line that decides
what belongs here.

The third part relates an implementation's arithmetic to the rule. It works in
integers, so `scaled_cmp_of_int_eq` turns an integer identity into a comparison
against the exact value; and it observes those quantities through comparisons it
can only afford to make approximately. Away from a decision boundary the loss
cannot change the answer, which is `comparison_stable_of_far`; near one the
observation is ambiguous, and the ambiguity is a Diophantine question about a
modular progression, which `ModWindows` answers by kernel-checked certificate.

The first and third parts are not specific to any implementation. The conversion
results ask only for bounds on the decimal grid, never for a binary format or
for the rule that chose the grid; the certificate machinery knows only modular
arithmetic, and never what a residue means.

Throughout this file:
* `f`, `e`: binary significand and exponent, denoting `f·2^e`;
* `d`, `k`: decimal significand and exponent, denoting `d·10^k`.
-/

/-! ## Decimal conversion specification -/

/-- Exact rational value represented by binary significand `f`
    and exponent `e`. -/
def value (f : ℕ) (e : ℤ) : ℚ := f * 2 ^ e

/-- One ULP for a regularly spaced value with exponent `e`. -/
def ulp (e : ℤ) : ℚ := 2 ^ e

/-- Whether the rational value `r` rounds to the regularly spaced value f·2^e
    under round-to-nearest, ties-to-even. -/
def Roundtrips (f : ℕ) (e : ℤ) (r : ℚ) : Prop :=
  if f % 2 = 0 then
    |r - value f e| ≤ ulp e / 2
  else
    |r - value f e| < ulp e / 2

/-- A decimal representation is shortest if it round-trips and no value on the
    next coarser decimal grid does. The grids are nested, so refuting the next
    one refutes every coarser one. It also forces `d` to have no trailing zero,
    since `d / 10` at `k + 1` would denote the same value. -/
def Shortest (f : ℕ) (e : ℤ) (d : ℕ) (k : ℤ) : Prop :=
  Roundtrips f e (d * 10 ^ k) ∧
    ∀ d' : ℕ, ¬Roundtrips f e (d' * 10 ^ (k + 1))

/-- A decimal representation is correctly rounded on its decimal grid if no
    value on that grid is closer to the exact value, with ties resolved to
    even. -/
def CorrectlyRounded (f : ℕ) (e : ℤ) (d : ℕ) (k : ℤ) : Prop :=
  let r := (d : ℚ) * 10 ^ k
  let v := value f e
  (∀ d' : ℕ, |r - v| ≤ |(d' : ℚ) * 10 ^ k - v|) ∧
   ∀ d' : ℕ, |r - v| = |(d' : ℚ) * 10 ^ k - v| → d' = d ∨ d % 2 = 0

/-! ## The exact reference method

This is the exact selection rule underlying Schubfach, stated at a decimal
exponent `k` and read in the scaled domain: prefer a multiple of ten that
round-trips, and settle for a nearest integer, ties to even, when there is none.
A multiple of ten round-trips exactly when a digit can be dropped,
`coarse_roundtrip_iff_next_grid`, so the first case is where the shortest
representation is coarser than the grid at `k`.

Only two properties of `k` are used. The grid must be fine enough that a
nearest grid point round-trips, `1 ≤ u`, and coarse enough that the round-trip
interval, one ULP wide, cannot hold two multiples of ten, `u < 10`.

`coarse_roundtrip_adjacent` comes last, after the correctness theorem, because
it is not part of it. That second bound also pins down where the one multiple of
ten can be, which is how an implementation gets away with testing two
candidates.
-/

/-! ### The method

The rule above, written down. Everything after this subsection is machinery
for proving `exact_candidate_correct`.
-/

/-- Whether some multiple of ten round-trips on the grid at `k`. -/
def CoarseRoundtrip (f : ℕ) (e k : ℤ) : Prop :=
  ∃ c : ℕ, c % 10 = 0 ∧ Roundtrips f e (c * 10 ^ k)

/-- The exact method: a multiple of ten that round-trips if one exists, and
    otherwise a nearest value on the grid at `k`, ties to even. The second case
    says what the computation establishes, a half-step bound and evenness at an
    exact midpoint, rather than the correct rounding those two imply. -/
def ExactCandidate (f : ℕ) (e k : ℤ) (d : ℕ) : Prop :=
  let x := value f e * 10 ^ (-k)
  (d % 10 = 0 ∧ Roundtrips f e (d * 10 ^ k)) ∨
    (¬CoarseRoundtrip f e k ∧ |(d : ℚ) - x| ≤ 1 / 2 ∧
      (|(d : ℚ) - x| = 1 / 2 → d % 2 = 0))

/-! ### The scaled domain

Scaled by `10^(-k)`, the grid at `k` becomes the integers, the exact value
becomes `x`, and one ULP becomes `u = ulp e · 10^(-k)` grid steps. Both of the
method's cases are distances to `x` there: a round-trip is a bound on `|d - x|`
by `u / 2`, non-strict for even `f` and strict for odd, and correct rounding is
choosing a nearest integer, ties to even. Half a step settles the second,
distinct candidates being at least one step apart, so a candidate within half a
step is nearest and one strictly within is uniquely nearest.
-/

/-- Scaling by the positive factor `10^k` carries a distance in the scaled
    domain to the corresponding distance on the grid at `k`. Every comparison
    below crosses between the two through this one identity. -/
private theorem abs_sub_scaled (f : ℕ) (e k : ℤ) (n : ℕ) :
    |(n : ℚ) - value f e * 10 ^ (-k)| * 10 ^ k
      = |(n : ℚ) * 10 ^ k - value f e| := by
  have h : ((n : ℚ) - value f e * 10 ^ (-k)) * 10 ^ k
      = (n : ℚ) * 10 ^ k - value f e := by
    rw [zpow_neg]; field_simp
  rw [← h, abs_mul, abs_of_pos (show (0 : ℚ) < 10 ^ k by positivity)]

/-- Two grid points are no farther apart than the sum of their distances to any
    value. -/
private theorem abs_sub_le_add (a b x : ℚ) : |a - b| ≤ |a - x| + |b - x| := by
  rw [abs_sub_comm b x]
  exact abs_sub_le a x b

/-- Distinct integer candidates are at least one step apart, so the sum of their
    distances to any value is at least one. -/
private theorem one_le_abs_sub_add_abs_sub {x : ℚ} {d d' : ℕ} (hne : d' ≠ d) :
    1 ≤ |(d' : ℚ) - x| + |(d : ℚ) - x| := by
  have hstep : (1 : ℚ) ≤ |(d' : ℚ) - (d : ℚ)| := by
    exact_mod_cast Int.one_le_abs (show (d' : ℤ) - d ≠ 0 by omega)
  linarith [abs_sub_le_add (d' : ℚ) (d : ℚ) x]

/-- A candidate within half a step is a nearest grid point. -/
private theorem abs_sub_le_of_le_half {x : ℚ} {d : ℕ}
    (hd : |(d : ℚ) - x| ≤ 1 / 2) (d' : ℕ) :
    |(d : ℚ) - x| ≤ |(d' : ℚ) - x| := by
  rcases eq_or_ne d' d with rfl | hne
  · exact le_rfl
  · linarith [one_le_abs_sub_add_abs_sub (x := x) hne]

/-- A candidate strictly within half a step is the unique nearest grid point. -/
private theorem eq_of_abs_sub_eq_of_lt_half {x : ℚ} {d d' : ℕ}
    (hd : |(d : ℚ) - x| < 1 / 2) (heq : |(d : ℚ) - x| = |(d' : ℚ) - x|) :
    d' = d := by
  by_contra hne
  linarith [one_le_abs_sub_add_abs_sub (x := x) hne]

/-- A candidate within half a grid step is correctly rounded if an exact
    midpoint is resolved to an even candidate. The factor `10^k` is positive, so
    it cancels from every comparison, leaving comparisons in the scaled
    domain. An implementation that rounds to a grid the caller chose, rather
    than to a shortest representation, asks for nothing else. -/
theorem correctly_rounded_of_le_half (f : ℕ) (e : ℤ) (d : ℕ) (k : ℤ)
    (hle : |(d : ℚ) - value f e * 10 ^ (-k)| ≤ 1 / 2)
    (heven : |(d : ℚ) - value f e * 10 ^ (-k)| = 1 / 2 → d % 2 = 0) :
    CorrectlyRounded f e d k := by
  have hp : (0 : ℚ) < 10 ^ k := by positivity
  simp only [CorrectlyRounded]
  refine ⟨fun d' => ?_, fun d' hd' => ?_⟩
  · rw [← abs_sub_scaled f e k d, ← abs_sub_scaled f e k d']
    exact mul_le_mul_of_nonneg_right (abs_sub_le_of_le_half hle d') hp.le
  · rw [← abs_sub_scaled f e k d, ← abs_sub_scaled f e k d'] at hd'
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl
        (eq_of_abs_sub_eq_of_lt_half hlt (mul_right_cancel₀ (ne_of_gt hp) hd'))
    · exact Or.inr (heven heq)

/-- Scaling by the positive factor `10^k` preserves the rounding bounds, so a
    round-trip on the grid at `k` is the scaled half-ULP bound. -/
theorem roundtrips_iff_scaled (f : ℕ) (e k : ℤ) (d : ℕ) :
    let x := value f e * 10 ^ (-k)
    let u := ulp e * 10 ^ (-k)
    Roundtrips f e (d * 10 ^ k)
      ↔ (if f % 2 = 0 then |(d : ℚ) - x| ≤ u / 2
          else |(d : ℚ) - x| < u / 2) := by
  intro x u
  have hp : (0 : ℚ) < 10 ^ k := by positivity
  have hne : (10 : ℚ) ^ k ≠ 0 := ne_of_gt hp
  have hdist := abs_sub_scaled f e k d
  have hhalf : u / 2 * 10 ^ k = ulp e / 2 := by
    simp only [u, zpow_neg]; field_simp
  simp only [Roundtrips]
  split_ifs
  · rw [← hdist, ← hhalf]; exact mul_le_mul_iff_of_pos_right hp
  · rw [← hdist, ← hhalf]; exact mul_lt_mul_iff_of_pos_right hp

/-- Either parity of a round-trip bounds the scaled distance by half a ULP. -/
private theorem abs_sub_le_half_ulp (f : ℕ) (e k : ℤ) {d : ℕ}
    (hround : Roundtrips f e (d * 10 ^ k)) :
    |(d : ℚ) - value f e * 10 ^ (-k)| ≤ ulp e * 10 ^ (-k) / 2 := by
  have hs := (roundtrips_iff_scaled f e k d).mp hround
  split_ifs at hs <;> linarith

/-- Whether a value round-trips depends only on its distance to the exact value,
    so anything no farther away than one that round-trips does too. -/
private theorem roundtrips_of_abs_le (f : ℕ) (e : ℤ) {r r' : ℚ}
    (hround : Roundtrips f e r) (hle : |r' - value f e| ≤ |r - value f e|) :
    Roundtrips f e r' := by
  simp only [Roundtrips] at hround ⊢
  split_ifs at hround ⊢ <;> linarith

/-- A positive value is at least a whole ULP away from zero, so the zero
    significand never round-trips. -/
private theorem not_roundtrips_zero (f : ℕ) (e : ℤ) (hf0 : 0 < f) :
    ¬Roundtrips f e 0 := by
  have hf : (1 : ℚ) ≤ (f : ℚ) := by exact_mod_cast hf0
  have hpos : (0 : ℚ) < 2 ^ e := by positivity
  have hval : |(0 : ℚ) - value f e| = (f : ℚ) * 2 ^ e := by
    rw [zero_sub, abs_neg, value, abs_of_pos (mul_pos (by linarith) hpos)]
  have hbig : ulp e / 2 < (f : ℚ) * 2 ^ e := by
    rw [ulp]
    nlinarith
  simp only [Roundtrips, hval]
  split_ifs <;> linarith

/-- On a grid no coarser than one ULP, a value within half a grid step
    round-trips. For odd `f` the round-trip bound is strict; half a step can
    reach half a ULP only when the step is exactly one ULP, and then the scaled
    value is the integer `f`, which lies at no half-integer distance. -/
private theorem roundtrips_of_le_half (f : ℕ) (e k : ℤ) (d : ℕ)
    (hfine : 1 ≤ ulp e * 10 ^ (-k))
    (hd : |(d : ℚ) - value f e * 10 ^ (-k)| ≤ 1 / 2) :
    Roundtrips f e (d * 10 ^ k) := by
  refine (roundtrips_iff_scaled f e k d).mpr ?_
  rcases eq_or_lt_of_le hfine with hone | hgt
  · have hx : value f e * 10 ^ (-k) = (f : ℚ) := by
      rw [show value f e = (f : ℚ) * ulp e from by rw [value, ulp], mul_assoc,
        ← hone, mul_one]
    rw [hx] at hd ⊢
    obtain ⟨hlo, hhi⟩ := abs_le.mp hd
    have hdf : d = f := by
      have h1 : d < f + 1 := by
        exact_mod_cast (show (d : ℚ) < (f : ℚ) + 1 by linarith)
      have h2 : f < d + 1 := by
        exact_mod_cast (show (f : ℚ) < (d : ℚ) + 1 by linarith)
      omega
    rw [hdf, ← hone]
    split_ifs <;> norm_num
  · split_ifs <;> linarith

/-! ### Decimal reduction -/

/-- Removes trailing zeros from a decimal significand, shifting the exponent to
    preserve the represented value. -/
def reduceDecimal (d : ℕ) (k : ℤ) : ℕ × ℤ :=
  if 0 < d ∧ d % 10 = 0 then reduceDecimal (d / 10) (k + 1)
  else (d, k)
termination_by d
decreasing_by omega

private theorem reduce_reduced (d : ℕ) (k : ℤ) :
    (reduceDecimal d k).1 = 0 ∨ (reduceDecimal d k).1 % 10 ≠ 0 := by
  fun_induction reduceDecimal d k with
  | case1 d k _ ih => exact ih
  | case2 d k hstop => omega

/-- Reduction shifts the exponent by the number of zeros stripped and removes
    the corresponding power of ten from the significand. -/
private theorem reduce_shift (d : ℕ) (k : ℤ) :
    ∃ t : ℕ, (reduceDecimal d k).2 = k + t
      ∧ d = (reduceDecimal d k).1 * 10 ^ t := by
  fun_induction reduceDecimal d k with
  | case1 d k _ ih =>
    obtain ⟨t, hk, hd⟩ := ih
    refine ⟨t + 1, by push_cast; omega, ?_⟩
    rw [pow_succ, ← Nat.mul_assoc, ← hd]
    omega
  | case2 d k _ => exact ⟨0, by simp, by simp⟩

/-- Trailing zeros can move between the significand and the exponent. -/
private theorem ten_pow_shift (d t : ℕ) (k : ℤ) :
    ((d * 10 ^ t : ℕ) : ℚ) * 10 ^ k = (d : ℚ) * 10 ^ (k + (t : ℤ)) := by
  push_cast
  rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0), zpow_natCast]
  ring

private theorem reduce_value (d : ℕ) (k : ℤ) :
    let (d', k') := reduceDecimal d k
    (d' : ℚ) * 10 ^ k' = (d : ℚ) * 10 ^ k := by
  obtain ⟨t, hkt, hstrip⟩ := reduce_shift d k
  rcases hred : reduceDecimal d k with ⟨d', k'⟩
  simp only [hred] at hkt hstrip
  rw [hstrip, hkt, ten_pow_shift]

/-- Moving to the next coarser grid multiplies its significand by ten. -/
private theorem ten_pow_succ_shift (d : ℕ) (k : ℤ) :
    ((d * 10 : ℕ) : ℚ) * 10 ^ k = (d : ℚ) * 10 ^ (k + 1) := by
  rw [show d * 10 = d * 10 ^ 1 from by ring, ten_pow_shift d 1]
  norm_num

/-! ### Correctness -/

/-- The multiples of ten on the grid at `k` are exactly the values on the grid
    at `k + 1`, the two descriptions differing only by a factor of ten in the
    significand. So the method's case split is the question `Shortest` asks, and
    the coarse case is precisely where a shorter representation exists. -/
private theorem coarse_roundtrip_iff_next_grid (f : ℕ) (e k : ℤ) :
    CoarseRoundtrip f e k ↔ ∃ d : ℕ, Roundtrips f e (d * 10 ^ (k + 1)) := by
  constructor
  · rintro ⟨c, h10, hc⟩
    refine ⟨c / 10, ?_⟩
    rw [← ten_pow_succ_shift, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h10)]
    exact hc
  · rintro ⟨d, hd⟩
    exact ⟨d * 10, Nat.mul_mod_left d 10, by rw [ten_pow_succ_shift]; exact hd⟩

/-- At most one multiple of ten round-trips: two distinct ones are ten grid
    steps apart, while the round-trip interval is `u < 10` steps wide. -/
private theorem coarse_roundtrip_unique (f : ℕ) (e k : ℤ)
    (hcoarse : ulp e * 10 ^ (-k) < 10) {c₁ c₂ : ℕ}
    (h₁ : c₁ % 10 = 0) (h₂ : c₂ % 10 = 0)
    (hround₁ : Roundtrips f e (c₁ * 10 ^ k))
    (hround₂ : Roundtrips f e (c₂ * 10 ^ k)) :
    c₁ = c₂ := by
  let x := value f e * 10 ^ (-k)
  have hd₁ := abs_sub_le_half_ulp f e k hround₁
  have hd₂ := abs_sub_le_half_ulp f e k hround₂
  have hsum : |(c₁ : ℚ) - (c₂ : ℚ)| < 10 :=
    lt_of_le_of_lt (abs_sub_le_add _ _ x) (by linarith)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hsum
  have hn₁ : c₁ < c₂ + 10 := by
    exact_mod_cast (show (c₁ : ℚ) < (c₂ : ℚ) + 10 by linarith)
  have hn₂ : c₂ < c₁ + 10 := by
    exact_mod_cast (show (c₂ : ℚ) < (c₁ : ℚ) + 10 by linarith)
  omega

/-- A candidate with no trailing zero that is the only value round-tripping on
    its grid is both shortest and correctly rounded. Nothing coarser
    round-trips, since it would be a multiple of ten back on this grid, hence
    the candidate, which has none; and nothing on this grid is closer, since
    anything at least as close round-trips too. That also leaves no tie to
    resolve. -/
private theorem shortest_correct_of_unique (f : ℕ) (e k : ℤ) {d : ℕ}
    (hrt : Roundtrips f e (d * 10 ^ k)) (hne : d % 10 ≠ 0)
    (huniq : ∀ c : ℕ, Roundtrips f e (c * 10 ^ k) → c = d) :
    Shortest f e d k ∧ CorrectlyRounded f e d k := by
  have hclose (c : ℕ)
      (hc : |(c : ℚ) * 10 ^ k - value f e| ≤ |(d : ℚ) * 10 ^ k - value f e|) :
      c = d := huniq c (roundtrips_of_abs_le f e hrt hc)
  refine ⟨⟨hrt, fun c hc => hne ?_⟩,
    fun c => ?_, fun c hc => Or.inl (hclose c hc.ge)⟩
  · obtain ⟨c', h10', hc'⟩ := (coarse_roundtrip_iff_next_grid f e k).mpr ⟨c, hc⟩
    rw [← huniq c' hc']
    exact h10'
  · by_contra hcon
    rw [hclose c (not_le.mp hcon).le] at hcon
    exact hcon le_rfl

/--
Correctness of the exact method. In the coarse case the candidate carries
trailing zeros, and after stripping them every value on the reduced grid is
still a multiple of ten back at `k`, where uniqueness identifies it with the
candidate. In the fine case the candidate has no trailing zero to strip, since
one would itself be a coarse candidate, so reduction leaves it alone, nothing on
any coarser grid round-trips, and correct rounding is the half-step bound read
through `correctly_rounded_of_le_half`.
-/
theorem exact_candidate_correct (f : ℕ) (e k : ℤ) {d : ℕ} (hf0 : 0 < f)
    (hfine : 1 ≤ ulp e * 10 ^ (-k)) (hcoarse : ulp e * 10 ^ (-k) < 10)
    (hd : ExactCandidate f e k d) :
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  rcases hd with ⟨h10, hrt⟩ | ⟨hnone, hle, heven⟩
  · -- The coarse case.
    obtain ⟨t, hkt, hstrip⟩ := reduce_shift d k
    have hstop := reduce_reduced d k
    have hval := reduce_value d k
    rcases hred : reduceDecimal d k with ⟨d', k'⟩
    simp only [hred] at hkt hstrip hstop hval ⊢
    have hrt' : Roundtrips f e ((d' : ℚ) * 10 ^ k') := by rw [hval]; exact hrt
    -- Reduction never reaches zero, which does not round-trip, so it stopped at
    -- a significand with no trailing zero -- and so it stripped at least one.
    have hne : d' % 10 ≠ 0 := by
      rcases hstop with h0 | hstop
      · rw [h0] at hrt'
        exact absurd (by simpa using hrt') (not_roundtrips_zero f e hf0)
      · exact hstop
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp only [pow_zero, Nat.mul_one] at hstrip
        omega
      · exact ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    -- Every value that round-trips on the reduced grid is the candidate itself.
    refine shortest_correct_of_unique f e k' hrt' hne fun c hc => ?_
    have hck : Roundtrips f e (((c * 10 ^ (s + 1) : ℕ) : ℚ) * 10 ^ k) := by
      rw [ten_pow_shift c (s + 1),
        show k + ((s + 1 : ℕ) : ℤ) = k' from by rw [hkt]]
      exact hc
    have hc10 : (c * 10 ^ (s + 1)) % 10 = 0 := by
      rw [pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _
    have heq := coarse_roundtrip_unique f e k hcoarse hc10 h10 hck hrt
    rw [hstrip] at heq
    exact Nat.eq_of_mul_eq_mul_right (by positivity) heq
  · -- The fine case: no trailing zero to strip, so reduction is the identity.
    have hrt : Roundtrips f e (d * 10 ^ k) :=
      roundtrips_of_le_half f e k d hfine hle
    have hd10 : d % 10 ≠ 0 := fun h10 => hnone ⟨d, h10, hrt⟩
    rw [show reduceDecimal d k = (d, k) from by rw [reduceDecimal]; simp [hd10]]
    exact ⟨⟨hrt, fun c hc =>
        hnone ((coarse_roundtrip_iff_next_grid f e k).mpr ⟨c, hc⟩)⟩,
      correctly_rounded_of_le_half f e d k hle heven⟩

/-! ### Locating the coarse candidate -/

/-- Where to look for it. Take a multiple of ten `c` that locates the scaled
    value to within half a ULP of the interval `[c, c + 10)`, with a ULP less
    than one coarse step. Then a multiple of ten that round-trips is `c` or the
    next one up: the round-trip reaches half a ULP either side of the value too,
    which confines it to `(c - 10, c + 20)`, where the only multiples of ten are
    `c` and `c + 10`. The tolerance is the round-trip's own radius, so an
    implementation has two candidates to test from any bracket it locates the
    value to that well. -/
theorem coarse_roundtrip_adjacent (f : ℕ) (e k : ℤ)
    (hcoarse : ulp e * 10 ^ (-k) < 10) {c d : ℕ}
    (hc : c % 10 = 0) (hd : d % 10 = 0)
    (hlo : (c : ℚ) - ulp e * 10 ^ (-k) / 2 ≤ value f e * 10 ^ (-k))
    (hhi : value f e * 10 ^ (-k) < (c : ℚ) + 10 + ulp e * 10 ^ (-k) / 2)
    (hround : Roundtrips f e (d * 10 ^ k)) :
    d = c ∨ d = c + 10 := by
  obtain ⟨hlo', hhi'⟩ := abs_le.mp (abs_sub_le_half_ulp f e k hround)
  have h10 : c < d + 10 := by
    exact_mod_cast (show (c : ℚ) < (d : ℚ) + 10 by linarith)
  have h20 : d < c + 20 := by
    exact_mod_cast (show (d : ℚ) < (c : ℚ) + 20 by linarith)
  omega

/-! ## What the algorithms share

Nothing above this section knows an implementation, and nothing after it knows
decimals. Between them sits what the implementation proofs have in common: how
a format spaces the values they convert, which decimal exponent they report, and
the normalized power-of-ten table they multiply by. No one algorithm owns
any of it, and neither part around it uses any of it.

All of it is stated over a `Format`, so that an implementation proof can be
written once and instantiated per format, and an implementation file names what
it needs through its own format, as `binary64.decimalExponent`.
-/

/-! ### Floating-point formats -/

/-- A binary format, as the layers below need it: precision, exponent range,
    the width of the base integer type an implementation computes in, and
    fixed-point approximations of `log₁₀2` and `log₂10` as a numerator over a
    power of two. Those two approximations are the only fields whose numerical
    accuracy has to be checked rather than used definitionally, and how far they
    can be trusted is what pins down the exponent range of the checks below.
    Only the `log₂10` side is checked through `Power10Normalized`; what has to
    hold of `log₁₀2` is a bound on the shift an implementation derives from it,
    which differs between algorithms, so each checks its own. -/
structure Format where
  prec : ℕ
  emin : ℤ
  emax : ℤ
  width : ℕ
  log10Two : ℕ × ℕ
  log2Ten  : ℕ × ℕ

abbrev Format.p10Width (fmt : Format) : ℕ := 2 * fmt.width

/-! ### Finite and regular values -/

/-- Whether f·2^e is a positive finite value of the format, including
    powers of two. A selection rule has to know the spacing below a binade, so
    it asks for `Regular`; a rounding to a precision the caller names does not,
    and asks only for this. -/
structure Format.Finite (fmt : Format) (f : ℕ) (e : ℤ) : Prop where
  pos : 0 < f
  sig_lt : f < 2 ^ fmt.prec
  range : fmt.emin ≤ e ∧ e ≤ fmt.emax

/-- Whether f·2^e is a regularly spaced positive value of the format: a finite
    value that is a normal other than a power of 2, or anything at the minimum
    exponent, subnormals included, there being no binade below to halve the
    spacing. -/
structure Format.Regular (fmt : Format) (f : ℕ) (e : ℤ) : Prop
    extends Format.Finite fmt f e where
  normal_or_min : 2 ^ (fmt.prec - 1) < f ∨ e = fmt.emin

/-! ### The decimal exponent -/

/-- Approximation of floor(e·log₁₀ 2), the decimal exponent to report for a
    value with binary exponent `e`. -/
def Format.decimalExponent (fmt : Format) (e : ℤ) : ℤ :=
  e * fmt.log10Two.1 / 2 ^ fmt.log10Two.2

/-- The decimal exponent reached at the bottom of the format's range. It and
    `kmax` are computed from `emin`/`emax` rather than supplied, so they cannot
    name an interval the format does not actually reach. -/
def Format.kmin (fmt : Format) : ℤ := fmt.decimalExponent fmt.emin

/-- The decimal exponent reached at the top of the format's range. -/
def Format.kmax (fmt : Format) : ℤ := fmt.decimalExponent fmt.emax

/-- The approximation is monotone whatever the constants are, scaling by a
    nonnegative numerator and flooring by a positive power of two both being
    monotone. -/
theorem Format.decimal_exponent_mono (fmt : Format) {a b : ℤ} (hab : a ≤ b) :
    fmt.decimalExponent a ≤ fmt.decimalExponent b :=
  Int.ediv_le_ediv (by positivity)
    (mul_le_mul_of_nonneg_right hab (Int.natCast_nonneg _))

/-- Hence the exponents it reaches over the format's range, which is what
    confines the indices an implementation reads the table at below.
    Monotonicity makes this a derivation and not a per-format check: what has to
    be checked of a format's constants is what `decimalExponent` computes, never
    where its range lies. -/
theorem Format.decimal_exponent_range (fmt : Format) {e : ℤ}
    (hlo : fmt.emin ≤ e) (hhi : e ≤ fmt.emax) :
    fmt.kmin ≤ fmt.decimalExponent e ∧ fmt.decimalExponent e ≤ fmt.kmax :=
  ⟨fmt.decimal_exponent_mono hlo, fmt.decimal_exponent_mono hhi⟩

/-! ### The power of ten

`10^k` as a truncated `p10Width`-bit significand with a fixed-point exponent.
Which entry gets read varies from caller to caller, so the checks below cover
every index any of them reaches.
-/

/-- Binary exponent of 10^k used to normalize its table significand: the
    fixed-point form of `⌊k·log₂10⌋ + 1`. Taking a logarithm here instead would
    make every exponent-wise check below shift the power of ten down to zero one
    bit at a time. -/
def Format.power10Exponent (fmt : Format) (k : ℤ) : ℤ :=
  k * fmt.log2Ten.1 / 2 ^ fmt.log2Ten.2 + 1

/-- Truncated normalized binary significand of 10^k, at the table width. -/
def Format.power10Significand (fmt : Format) (k : ℤ) : ℕ :=
  ⌊(10 : ℚ) ^ k * 2 ^ ((fmt.p10Width : ℤ) - fmt.power10Exponent k)⌋₊

/-- Numerator of the exact scaled power of ten `10^k·2^(p10Width-pe)`, with
    negative exponents moved to the denominator. Writing the power as a ratio of
    naturals turns the truncation into a single `Nat` division, which is what
    keeps the exponent-wise checks below cheap in the kernel. -/
def Format.power10Num (fmt : Format) (k : ℤ) : ℕ :=
  10 ^ k.toNat * 2 ^ ((fmt.p10Width : ℤ) - fmt.power10Exponent k).toNat

/-- Denominator of that same power of ten, carrying the negative exponents. -/
def Format.power10Den (fmt : Format) (k : ℤ) : ℕ :=
  10 ^ (-k).toNat * 2 ^ (fmt.power10Exponent k - (fmt.p10Width : ℤ)).toNat

theorem Format.power10_den_pos (fmt : Format) (k : ℤ) :
    0 < fmt.power10Den k := by
  rw [Format.power10Den]; positivity

/-- The scaled exact power of ten is exactly the rational `num / den`. Only
    exponent bookkeeping, so it holds at any width. -/
theorem Format.power10_exact_ratio (fmt : Format) (k : ℤ) :
    (10 : ℚ) ^ k * 2 ^ ((fmt.p10Width : ℤ) - fmt.power10Exponent k)
      = (fmt.power10Num k : ℚ) / (fmt.power10Den k : ℚ) := by
  set w : ℤ := (fmt.p10Width : ℤ) with hw
  set pe := fmt.power10Exponent k
  have hden : (fmt.power10Den k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (fmt.power10_den_pos k).ne'
  -- Each pair of exponents in the ratio adds up to the truncated one.
  have hk : k + ((-k).toNat : ℤ) = (k.toNat : ℤ) := by omega
  have hpe : w - pe + ((pe - w).toNat : ℤ) = ((w - pe).toNat : ℤ) := by
    omega
  rw [eq_div_iff hden, Format.power10Num, Format.power10Den, ← hw]
  push_cast
  rw [← zpow_natCast (10 : ℚ) (-k).toNat,
    ← zpow_natCast (2 : ℚ) (pe - w).toNat,
    ← zpow_natCast (10 : ℚ) k.toNat, ← zpow_natCast (2 : ℚ) (w - pe).toNat,
    show (10 : ℚ) ^ k * 2 ^ (w - pe) *
        (10 ^ ((-k).toNat : ℤ) * 2 ^ ((pe - w).toNat : ℤ))
      = (10 ^ k * 10 ^ ((-k).toNat : ℤ)) *
        (2 ^ (w - pe) * 2 ^ ((pe - w).toNat : ℤ)) from by ring,
    ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), hk, hpe]

/-- The truncation is the natural quotient `num / den`, which is what lets the
    normalization check and the layers an implementation builds on it stay in
    `Nat`. -/
theorem Format.power10_significand_nat (fmt : Format) (k : ℤ) :
    fmt.power10Significand k = fmt.power10Num k / fmt.power10Den k := by
  rw [Format.power10Significand, fmt.power10_exact_ratio]
  exact Nat.floor_div_eq_div _ _

/-- The significand is a normalized table-width number — its top bit is set, and
    it still fits the width — given the ratio bounds at that index. Which
    indices satisfy those bounds is a numerical fact about the format's
    constants, so it arrives as a hypothesis: the format that owns the index
    range sweeps it. -/
theorem Format.power10_significand_bounds (fmt : Format) {k : ℤ}
    (hlo : 2 ^ (fmt.p10Width - 1) * fmt.power10Den k ≤ fmt.power10Num k)
    (hhi : fmt.power10Num k < 2 ^ fmt.p10Width * fmt.power10Den k) :
    2 ^ (fmt.p10Width - 1) ≤ fmt.power10Significand k ∧
      fmt.power10Significand k < 2 ^ fmt.p10Width := by
  rw [fmt.power10_significand_nat]
  exact ⟨(Nat.le_div_iff_mul_le (fmt.power10_den_pos k)).mpr hlo,
    (Nat.div_lt_iff_lt_mul (fmt.power10_den_pos k)).mpr hhi⟩

/-- That the fixed-point exponent normalizes `10^k` at every index the format
    reaches: `[-kmax, -kmin]` for the index at a decimal exponent, one lower for
    the index below it. Outside that range the approximation eventually drifts
    from `⌊k·log₂10⌋ + 1`, so this is a fact about the format's `log2Ten` and
    not a consequence of the other fields. Each format supplies it as an
    instance, in whichever file can afford the sweep. -/
class Format.Power10Normalized (fmt : Format) : Prop where
  /-- In ratio form the check is two comparisons of naturals per index. -/
  ratio : ∀ k ∈ Finset.Icc (-fmt.kmax - 1) (-fmt.kmin),
    2 ^ (fmt.p10Width - 1) * fmt.power10Den k ≤ fmt.power10Num k ∧
      fmt.power10Num k < 2 ^ fmt.p10Width * fmt.power10Den k

/-- The bounds at either index a caller reads for a value at `e`: the one for
    its decimal exponent, or the one below. Which indices an exponent range
    reaches is a derivation, so a caller names its exponent, not an interval. -/
theorem Format.power10_ratio_normalized (fmt : Format)
    [h : fmt.Power10Normalized]
    {e : ℤ} (hlo : fmt.emin ≤ e) (hhi : e ≤ fmt.emax) (k : ℤ)
    (hk : -fmt.decimalExponent e - 1 ≤ k ∧ k ≤ -fmt.decimalExponent e) :
    2 ^ (fmt.p10Width - 1) * fmt.power10Den k ≤ fmt.power10Num k ∧
      fmt.power10Num k < 2 ^ fmt.p10Width * fmt.power10Den k := by
  obtain ⟨h1, h2⟩ := fmt.decimal_exponent_range hlo hhi
  exact h.ratio k (Finset.mem_Icc.mpr (by omega))

/-! ### Concrete formats -/

/-- IEEE 754 binary64. -/
def binary64 : Format where
  prec := 53
  emin := -1074
  emax := 971
  width := 64
  log10Two := (315_653, 20)
  log2Ten  := (217_707, 16)

/-- IEEE 754 binary128. -/
def binary128 : Format where
  prec := 113
  emin := -16494
  emax := 16271
  width := 128
  -- The smallest power-of-two denominators exact over this range.
  log10Two := (20_201_781, 26)
  log2Ten  := (55_732_705, 24)

/-- The x87 80-bit extended format, whose leading significand bit is stored
    rather than implicit — it is not an IEEE interchange format. Its 64 bits of
    precision against binary128's 113 put the exponent range 49 higher under the
    same 15-bit exponent field. zmij runs one code path at both extended
    formats, so the width and the two logarithms are binary128's. -/
def binary80 : Format where
  prec := 64
  emin := -16445
  emax := 16320
  width := 128
  log10Two := (20_201_781, 26)
  log2Ten  := (55_732_705, 24)

/-- The table entry at every index either algorithm reads is normalized. -/
instance : binary64.Power10Normalized where
  -- `+kernel` keeps the enumeration out of the elaborator, whose recursion and
  -- exponentiation guards it would otherwise trip.
  ratio := by decide +kernel

/-! ## Certified exact comparisons

An implementation works with integers, but its decisions are about exact
rational quantities. It connects the two by scaling an exact value `x` by an
integer `scale` so that `x·scale = x'` is integral. For a candidate `c`, an
identity such as

    c·scale + dist = x'

then expresses the exact distance from `c` to `x` through the integer `dist`.
`scaled_cmp_of_int_eq` turns identities of this form into exact comparisons.

The implementation's actual comparisons are lossy, so each decision has two
regimes. Away from a decision boundary, the approximation error cannot change
the result; `comparison_stable_of_far` handles all such cases at once. Near a
boundary the result is genuinely ambiguous, and `ModWindows` rules out the
remaining cases with kernel-checked certificates.

None of this knows a particular implementation. An implementation supplies the
integer identities connecting its quantities to the exact ones, bounds the
errors in its approximations, and provides certificates for the boundary cases.
-/

/-! ### Integer comparison identities

These lemmas are the only crossing into `ℚ`. An implementation supplies integer
identities for its candidates and, through the common `scale`, turns them into
exact distance comparisons and bounds on the number of grid steps per ULP.

Below this layer an implementation proof reasons in `ℤ`; above it the scale
disappears. The exact comparisons are deliberately reduced to integer interval
constraints, which `omega` can solve directly.
-/

/-- The scaled distance from the exact value, given by the integer identity. -/
theorem scaled_dist_eq {c scale : ℕ} {x' dist : ℤ} {x : ℚ} (hx : x * scale = x')
    (hnat : (c : ℤ) * scale + dist = x') :
    ((c : ℚ) - x) * scale = -(dist : ℚ) := by
  have hcast : (c : ℚ) * scale + (dist : ℚ) = x' := by exact_mod_cast hnat
  rw [sub_mul, hx]
  linarith

/-- Every comparison of a candidate against the exact value, as an integer
    interval condition on its signed distance. The threshold is scaled to match,
    `thr·(a·scale) = b`, with `a` accounting for fractional thresholds such as
    a half-ULP. -/
theorem scaled_cmp_of_int_eq {c scale a b : ℕ} {x' dist : ℤ} {x thr : ℚ}
    (hscale : 0 < scale) (ha : 0 < a) (hx : x * scale = x')
    (hthr : thr * (a * scale) = b) (hnat : (c : ℤ) * scale + dist = x') :
    (|(c : ℚ) - x| ≤ thr ↔ -(b : ℤ) ≤ a * dist ∧ a * dist ≤ b) ∧
      (|(c : ℚ) - x| < thr ↔ -(b : ℤ) < a * dist ∧ a * dist < b) ∧
      (|(c : ℚ) - x| = thr ↔ a * dist = b ∨ a * dist = -(b : ℤ)) := by
  have hscaleq : (0 : ℚ) < scale := by exact_mod_cast hscale
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hp : (0 : ℚ) < (a : ℚ) * scale := by positivity
  -- The scale comes out of the absolute value, leaving one integer magnitude.
  have habs :
      |(c : ℚ) - x| * ((a : ℚ) * scale) = |(((a : ℤ) * dist : ℤ) : ℚ)| := by
    rw [show ((a : ℚ) * scale) = |(scale : ℚ)| * |(a : ℚ)| from by
        rw [abs_of_pos hscaleq, abs_of_pos haq]; ring,
      ← mul_assoc, ← abs_mul, scaled_dist_eq hx hnat, abs_neg, ← abs_mul]
    push_cast
    rw [mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [← mul_le_mul_iff_of_pos_right hp, hthr, habs, abs_le]
    constructor <;> intro h <;> exact_mod_cast h
  · rw [← mul_lt_mul_iff_of_pos_right hp, hthr, habs, abs_lt]
    constructor <;> intro h <;> exact_mod_cast h
  · rw [← mul_left_inj' (ne_of_gt hp), hthr, habs, abs_eq (by positivity)]
    constructor <;> intro h <;> exact_mod_cast h

/-- The two bounds on the decimal grid that `exact_candidate_correct` asks for,
    from an integer identity. The `scale` sends `u`, one ULP measured in grid
    steps, to the integer `u'`, and `u` then spans between one and ten steps as
    soon as `u'` lies between `scale` and `10·scale`. -/
theorem ulp_steps_of_int_eq {scale u' : ℕ} {u : ℚ} (hscale : 0 < scale)
    (hu : u * scale = u') (hlo : scale ≤ u') (hhi : u' < 10 * scale) :
    1 ≤ u ∧ u < 10 := by
  have hscaleq : (0 : ℚ) < scale := by exact_mod_cast hscale
  refine ⟨(mul_le_mul_iff_of_pos_right hscaleq).mp ?_,
    (mul_lt_mul_iff_of_pos_right hscaleq).mp ?_⟩
  · rw [one_mul, hu]; exact_mod_cast hlo
  · rw [hu]; exact_mod_cast hhi

/-! ### Stability away from a boundary -/

/-- Far from the boundary a bounded approximation error cannot change a
    comparison. `x` is the exact value and `b` the exact boundary; a lossy test
    compares `x + dx` with `b + db`, the two offsets differing by at most `w`.
    Once `x` is more than `w` from `b`, the lossy test agrees with both exact
    tests, which there agree with each other. -/
theorem comparison_stable_of_far {x b dx db w : ℕ} (hdx : dx ≤ db + w)
    (hdb : db ≤ dx + w) (hfar : b + w < x ∨ x + w < b) :
    ((x + dx < b + db) ↔ x ≤ b) ∧ ((x + dx < b + db) ↔ x < b) := by
  omega

/-! ### Modular window certificates

The error bounds leave the comparison undecided within a narrow band either side
of the boundary it tests against. The value tested is a distance to the grid,
periodic across it and linear in the significand until it wraps, so within one
grid period it is the residue `n·f mod m`, and the ambiguous band becomes a
window of residues. In the coarse-window applications, `n` is one ULP in the
implementation's integer scale and `m` is the spacing it tests against, a grid
step or half of one. Refuting a window is a Diophantine question: can the
residue land in `[rmin, rmax]` for some significand `f` in `[fmin, fmax]`?
`ModWindows` poses that question, knowing nothing about what the residue means.

One multiplier `q` answers the question. Write `n·f = m·j + r`, where `j` is the
quotient and `r` the residue, and let `ε = n·q - m·p` be the error of an
approximation `p/q ≈ n/m`. Then

    q·r - f·ε
      = q·(n·f - m·j) - f·(n·q - m·p)
      = m·(p·f - q·j).

The `n·f·q` terms cancel, so `q·r - f·ε` is a multiple of `m`. If its bounds
over the box `f ∈ [fmin, fmax]`, `r ∈ [rmin, rmax]` fall strictly between the
same two consecutive multiples, no `f` can put the residue in the window. Such
a `q` is easy to find when the product of the interval widths is well below `m`.

Everything in this subsection is proof-producing and checked by the kernel. The
multiplier it takes is a witness, not an assumption, so where the witness comes
from is a separate question, answered below.
-/

/-- A modular window problem: the progression `n·f mod m`, the range
    `fmin ≤ f ≤ fmax` it runs over, and the closed windows of residues to
    exclude. -/
structure ModWindows where
  n : ℕ
  m : ℕ
  fmin : ℕ
  fmax : ℕ
  windows : List (ℤ × ℤ)

private def modWindowRefuted (n m fmin fmax rmin rmax q : ℤ) : Bool :=
  let p := (2 * (n * q) + m) / (2 * m)
  let ε := n * q - m * p
  -- `f·ε` runs between the two endpoint values, in whichever order the sign
  -- of `ε` dictates.
  let rmin' := q * rmin - max (fmin * ε) (fmax * ε)
  let rmax' := q * rmax - min (fmin * ε) (fmax * ε)
  decide (0 < q ∧ m * (rmin' / m) < rmin' ∧ rmax' < m * (rmin' / m) + m)

/-- Whether the one multiplier `q` refutes every window of the problem: a
    handful of big-integer operations per window, with the search for `q` left
    outside. -/
def ModWindows.refutedBy (w : ModWindows) (q : ℤ) : Bool :=
  w.windows.all fun window =>
    modWindowRefuted w.n w.m w.fmin w.fmax window.1 window.2 q

/-- An interval strictly between consecutive multiples of `m` cannot contain a
    multiple of `m`. -/
private theorem window_gap_absurd {m lo' hi' v : ℤ} (hm : 0 < m)
    (hlo : lo' ≤ m * v) (hhi : m * v ≤ hi')
    (hgap_lo : m * (lo' / m) < lo') (hgap_hi : hi' < m * (lo' / m) + m) :
    False := by
  have hv_lo : lo' / m < v :=
    lt_of_mul_lt_mul_left (lt_of_lt_of_le hgap_lo hlo) hm.le
  have hv_hi : v < lo' / m + 1 := by
    refine lt_of_mul_lt_mul_left (a := m) ?_ hm.le
    calc
      m * v ≤ hi' := hhi
      _ < m * (lo' / m) + m := hgap_hi
      _ = m * (lo' / m + 1) := by ring
  omega

/-- If a significand in range has its residue in the window, a multiple of `m`
    lies between the resulting bounds. -/
private theorem window_bounds {n m fmin fmax rmin rmax q p ε f j r : ℤ}
    (hq : 0 < q) (hε : ε = n * q - m * p)
    (hfmin : fmin ≤ f) (hfmax : f ≤ fmax)
    (hres : r = n * f - m * j) (hrmin : rmin ≤ r) (hrmax : r ≤ rmax) :
    q * rmin - max (fmin * ε) (fmax * ε) ≤ m * (p * f - q * j) ∧
      m * (p * f - q * j) ≤ q * rmax - min (fmin * ε) (fmax * ε) := by
  have hkey : m * (p * f - q * j) = q * r - f * ε := by
    rw [hres, hε]
    ring
  have hqrmin : q * rmin ≤ q * r := mul_le_mul_of_nonneg_left hrmin hq.le
  have hqrmax : q * r ≤ q * rmax := mul_le_mul_of_nonneg_left hrmax hq.le
  have hfε : min (fmin * ε) (fmax * ε) ≤ f * ε
      ∧ f * ε ≤ max (fmin * ε) (fmax * ε) := by
    rcases le_total 0 ε with hε0 | hε0
    · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hfmin hε0),
        le_trans (mul_le_mul_of_nonneg_right hfmax hε0) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hfmax hε0),
        le_trans (mul_le_mul_of_nonpos_right hfmin hε0) (le_max_left _ _)⟩
  exact ⟨by linarith [hfε.2], by linarith [hfε.1]⟩

/-- The quotient-remainder identity for `a mod m`, cast to `ℤ`. The cast on the
    left anchors a rewrite to the residue named; inlining the `Int.emod_def`
    step would match any remainder in the goal. -/
theorem cast_mod_eq_sub (a m : ℕ) :
    ((a % m : ℕ) : ℤ) = a - m * ((a / m : ℕ) : ℤ) := by
  rw [Int.natCast_emod, Int.emod_def, ← Int.natCast_ediv]

/-- A certificate excludes every listed window from any integer representative
    `r = n·f - m·j` of the residue class, for any significand in range. This
    general form handles recentred windows whose representatives may be
    signed. -/
theorem ModWindows.not_hit_rep (w : ModWindows) (f : ℕ) (hm : 0 < w.m)
    {q : ℤ} (hcert : w.refutedBy q = true)
    {rmin rmax : ℤ} (hmem : (rmin, rmax) ∈ w.windows) {r j : ℤ}
    (hfmin : w.fmin ≤ f) (hfmax : f ≤ w.fmax)
    (hres : r = w.n * f - w.m * j) (hrmin : rmin ≤ r) (hrmax : r ≤ rmax) :
    False := by
  have hwindow := List.all_eq_true.mp hcert _ hmem
  simp only [modWindowRefuted, decide_eq_true_eq] at hwindow
  obtain ⟨hq, hgap0, hgap1⟩ := hwindow
  obtain ⟨hb0, hb1⟩ :=
    window_bounds (fmin := (w.fmin : ℤ)) (fmax := (w.fmax : ℤ))
      (p := (2 * ((w.n : ℤ) * q) + w.m) / (2 * w.m))
      (ε := (w.n : ℤ) * q - w.m * _) hq rfl
      (by exact_mod_cast hfmin) (by exact_mod_cast hfmax) hres hrmin hrmax
  exact window_gap_absurd (by exact_mod_cast hm) hb0 hb1 hgap0 hgap1

/-- A certificate excludes every listed window from the canonical residue
    `n·f mod m`, for any significand in range. This is the form implementations
    normally use; recentred signed representatives are handled by
    `not_hit_rep`. -/
theorem ModWindows.not_hit (w : ModWindows) (f : ℕ) (hm : 0 < w.m)
    {q : ℤ} (hcert : w.refutedBy q = true) {rmin rmax : ℤ}
    (hmem : (rmin, rmax) ∈ w.windows) {r : ℕ}
    (hfmin : w.fmin ≤ f) (hfmax : f ≤ w.fmax)
    (hres : r = w.n * f % w.m)
    (hrmin : rmin ≤ (r : ℤ)) (hrmax : (r : ℤ) ≤ rmax) :
    False := by
  -- The residue identity, with the quotient as the multiple of the modulus.
  have hrz : (r : ℤ) = w.n * f - w.m * ((w.n * f / w.m : ℕ) : ℤ) := by
    rw [hres, cast_mod_eq_sub]
    push_cast
    ring
  exact w.not_hit_rep f hm hcert hmem hfmin hfmax hrz hrmin hrmax

/-! ### Certificate search

Nothing in this subsection is trusted. `ModWindows.search` runs during
elaboration, outside the proof term, and `modCertTactic` quotes what it returns
as a literal for the kernel to check against `ModWindows.refutedBy`. A bad
multiplier is a failed proof rather than an unsound one, so no theorem anywhere
depends on how the search works, or on whether it terminates with a useful
answer at all.
-/

/--
The multiplier is searched for rather than tabulated, by the elaborator rather
than by the kernel. Convergent denominators of `n/m` give the relevant best
rational approximations. The Euclidean remainder `v` that produces `qc` is the
error `|n·qc - m·p|`, and a certificate has to fit `q·(rmax - rmin)` for the
window plus `(fmax - fmin)·v` for the box inside one modulus, so the loop waits
for the box term alone to fit. Waiting reads no window and skips the small
denominators, leaving few window checks per problem. Balancing the two terms
puts the span at about `2·√((fmax-fmin)·(rmax-rmin)/m)` of the modulus, which is
what leaves room between consecutive multiples.
-/
private def modCertSearch (w : ModWindows) : (fuel : ℕ) → (u v qp qc : ℤ) → ℤ
  | 0, _, _, _, qc => qc
  | fuel + 1, u, v, qp, qc =>
    if decide (((w.fmax : ℤ) - w.fmin) * v < w.m) && w.refutedBy qc then
      qc
    else if v = 0 then
      qc
    else
      modCertSearch w fuel v (u % v) qc (u / v * qc + qp)

/-- A multiplier refuting every window, or the best attempt at one. Untrusted:
    what it returns is checked by `refutedBy`. The fuel bounds the Euclidean
    search, whose length grows with the precision: the current binary64
    searches finish within 44 steps and binary128 within 74, so 160 leaves both
    room to spare. The loop exits as soon as the problem is refuted, so unused
    fuel costs nothing. -/
def ModWindows.search (w : ModWindows) : ℤ :=
  modCertSearch w 160 w.m ((w.n : ℤ) % (w.m : ℤ)) 0 1

open Lean Elab Tactic Meta in
/-- Close a goal `∃ q, w.refutedBy q = true`, where `w` is a definition applied
    to one integer literal, by running the given search on that literal during
    elaboration and quoting the multiplier it returns. Only the literal reaches
    the proof term, where the kernel checks the certificate. -/
def modCertTactic (search : ℤ → ℤ) : TacticM Unit := do
  let target ← whnfR (← (← getMainGoal).getType)
  let_expr Exists _ pred := target
    | throwError "mod_cert: expected `∃ q, w.refutedBy q = true`"
  let_expr Eq _ lhs _ := pred.bindingBody!
    | throwError "mod_cert: expected an equation under the existential"
  let_expr ModWindows.refutedBy problem _ := lhs
    | throwError "mod_cert: expected `w.refutedBy q`, got {lhs}"
  let .app _ argument := problem
    | throwError "mod_cert: {problem} is not applied to an index"
  -- The index may arrive wrapped, as when the window family is applied to an
  -- exponent bundled with its format; the literal is then the last argument of
  -- the constructor.
  let some index := argument.int? <|> argument.getAppArgs.back?.bind (·.int?)
    | throwError "mod_cert: the index {argument} is not a literal"
  let q ← Term.exprToSyntax (toExpr (search index))
  evalTactic (← `(tactic| exact ⟨$q, by decide +kernel⟩))

/-! ### Windows over regular values

Nothing above knows which significands a format admits. The implementation
proofs ask their window questions over the same ones, and `Regular` is all any
of them knows about `f`, so the box and the bounds a certificate needs belong
here rather than in each implementation proof.
-/

/-- A window problem over the significands `Regular` admits at `e`. At the
    minimum exponent every positive significand is possible; above it `Regular`
    gives the tighter lower bound `2 ^ (prec - 1) + 1`. -/
def Format.regularWindows (fmt : Format) (n m : ℕ) (e : ℤ)
    (windows : List (ℤ × ℤ)) : ModWindows where
  n := n
  m := m
  fmin := if e = fmt.emin then 1 else 2 ^ (fmt.prec - 1) + 1
  fmax := 2 ^ fmt.prec - 1
  windows := windows

/-- `not_hit` over that box: `Regular` discharges the significand bounds, so a
    caller never mentions `fmin` or `fmax`; it supplies positivity of the
    modulus and identifies its quantity with the residue. -/
theorem Format.regular_not_hit {fmt : Format} {n m : ℕ} {e : ℤ}
    {windows : List (ℤ × ℤ)} {q rmin rmax : ℤ} {r : ℕ} (f : ℕ)
    (hr : fmt.Regular f e) (hm : 0 < m)
    (hcert : (fmt.regularWindows n m e windows).refutedBy q = true)
    (hmem : (rmin, rmax) ∈ windows) (hres : r = n * f % m)
    (hrmin : rmin ≤ (r : ℤ)) (hrmax : (r : ℤ) ≤ rmax) :
    False :=
  (fmt.regularWindows n m e windows).not_hit f hm hcert hmem
    (hfmin := by
      simp only [Format.regularWindows]
      split_ifs with hmin
      · exact hr.pos
      · rcases hr.normal_or_min with h | h
        · omega
        · exact absurd h hmin)
    (hfmax := by simp only [Format.regularWindows]; have := hr.sig_lt; omega)
    hres hrmin hrmax
