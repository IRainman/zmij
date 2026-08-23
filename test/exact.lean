import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-! # Shortest decimal conversion

The specification, and the exact mathematics of the Schubfach-like method:
prefer a multiple of ten that round-trips, and settle for a nearest grid point
otherwise. `exact_candidate_correct` proves that method is shortest and
correctly rounded for any positive value, given only that the decimal grid is no
coarser than one ULP and strictly coarser than one tenth of an ULP. Nothing here
knows a binary format, or how the grid is chosen.

The last section is unrelated to decimal conversion. An implementation of any
such method observes exact quantities through lossy comparisons, and where the
observation is ambiguous the ambiguity is a Diophantine question about a modular
progression. `ModWindows` answers those questions by certificate, knowing
nothing about what the residues mean.

Throughout:

* `f`, `e`: binary significand and exponent, representing `f·2^e`;
* `d`, `k`: decimal significand and exponent, representing `d·10^k`.
-/

/-! ## The specification -/

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

/-! ## Nearest values on a decimal grid

Scaled by `10^(-k)`, the grid at `k` becomes the integers, so correct rounding
means choosing a nearest integer to the scaled value, with ties resolved to
even. Half a step is then enough: distinct candidates are at least one step
apart, so a candidate within half a step is nearest, and one strictly within
half a step is uniquely nearest.
-/

/-- Distinct integer candidates are at least one step apart, so the sum of their
    distances to any value is at least one. -/
private theorem one_le_abs_sub_add_abs_sub {x : ℚ} {d d' : ℕ} (hne : d' ≠ d) :
    1 ≤ |(d' : ℚ) - x| + |(d : ℚ) - x| := by
  have hstep : (1 : ℚ) ≤ |(d' : ℚ) - (d : ℚ)| := by
    exact_mod_cast Int.one_le_abs (show (d' : ℤ) - d ≠ 0 by omega)
  calc (1 : ℚ) ≤ |(d' : ℚ) - (d : ℚ)| := hstep
    _ ≤ |(d' : ℚ) - x| + |x - (d : ℚ)| := abs_sub_le _ _ _
    _ = |(d' : ℚ) - x| + |(d : ℚ) - x| := by rw [abs_sub_comm x]

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

/-- Correct rounding in the scaled domain: `10^k` is positive, so it cancels
    from every comparison, leaving comparisons between `d`, `d'` and `x`. -/
private theorem correctly_rounded_iff_scaled (f : ℕ) (e : ℤ) (d : ℕ) (k : ℤ) :
    let x := value f e * 10 ^ (-k)
    CorrectlyRounded f e d k
      ↔ (∀ d' : ℕ, |(d : ℚ) - x| ≤ |(d' : ℚ) - x|) ∧
        ∀ d' : ℕ,
          |(d : ℚ) - x| = |(d' : ℚ) - x| → d' = d ∨ d % 2 = 0 := by
  intro x
  have hp : (0 : ℚ) < 10 ^ k := by positivity
  have hdist : ∀ n : ℕ,
      |(n : ℚ) - x| * 10 ^ k = |(n : ℚ) * 10 ^ k - value f e| := by
    intro n
    have h : ((n : ℚ) - x) * 10 ^ k = (n : ℚ) * 10 ^ k - value f e := by
      simp only [x, zpow_neg]
      field_simp
    rw [← h, abs_mul, abs_of_pos hp]
  simp only [CorrectlyRounded]
  constructor
  · rintro ⟨hnear, hties⟩
    refine ⟨fun d' => ?_, fun d' hd' => hties d' ?_⟩
    · have hscaled := hnear d'
      rw [← hdist d, ← hdist d'] at hscaled
      exact (mul_le_mul_iff_of_pos_right hp).mp hscaled
    · rw [← hdist d, ← hdist d', hd']
  · rintro ⟨hnear, hties⟩
    refine ⟨fun d' => ?_, fun d' hd' => hties d' ?_⟩
    · rw [← hdist d, ← hdist d']
      exact (mul_le_mul_iff_of_pos_right hp).mpr (hnear d')
    · rw [← hdist d, ← hdist d'] at hd'
      exact mul_right_cancel₀ (ne_of_gt hp) hd'

/-- A candidate within half a grid step is correctly rounded if an exact
    midpoint is resolved to an even candidate. -/
private theorem correctly_rounded_of_le_half (f : ℕ) (e : ℤ) (d : ℕ) (k : ℤ)
    (hle : |(d : ℚ) - value f e * 10 ^ (-k)| ≤ 1 / 2)
    (heven : |(d : ℚ) - value f e * 10 ^ (-k)| = 1 / 2 → d % 2 = 0) :
    CorrectlyRounded f e d k := by
  refine (correctly_rounded_iff_scaled f e d k).mpr
    ⟨fun d' => abs_sub_le_of_le_half hle d', fun d' hd' => ?_⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (eq_of_abs_sub_eq_of_lt_half hlt hd')
  · exact Or.inr (heven heq)

/-! ## Round-trips in the scaled domain

Scaled by `10^(-k)`, the grid at `k` becomes the integers, the exact value
becomes `x` and one ULP becomes `u = ulp e · 10^(-k)` grid steps. A round-trip
is then a bound on `|d - x|` by `u / 2`, non-strict for even `f` and strict for
odd `f`.
-/

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
  have hdist : |(d : ℚ) - x| * 10 ^ k = |(d : ℚ) * 10 ^ k - value f e| := by
    have h : ((d : ℚ) - x) * 10 ^ k = (d : ℚ) * 10 ^ k - value f e := by
      simp only [x, zpow_neg]; field_simp
    rw [← h, abs_mul, abs_of_pos hp]
  have hhalf : u / 2 * 10 ^ k = ulp e / 2 := by
    simp only [u, zpow_neg]; field_simp
  simp only [Roundtrips]
  split_ifs
  · rw [← hdist, ← hhalf]; exact mul_le_mul_iff_of_pos_right hp
  · rw [← hdist, ← hhalf]; exact mul_lt_mul_iff_of_pos_right hp

/-- Either parity of a round-trip bounds the scaled distance by half a ULP. -/
private theorem abs_sub_le_half_ulp (f : ℕ) (e k : ℤ) {d : ℕ}
    (hr : Roundtrips f e (d * 10 ^ k)) :
    |(d : ℚ) - value f e * 10 ^ (-k)| ≤ ulp e * 10 ^ (-k) / 2 := by
  have hs := (roundtrips_iff_scaled f e k d).mp hr
  split_ifs at hs <;> linarith

/-- Whether a value round-trips depends only on its distance to the exact value,
    so anything no farther away than one that round-trips does too. -/
private theorem roundtrips_of_abs_le (f : ℕ) (e : ℤ) {r r' : ℚ}
    (hr : Roundtrips f e r) (hle : |r' - value f e| ≤ |r - value f e|) :
    Roundtrips f e r' := by
  simp only [Roundtrips] at hr ⊢
  split_ifs at hr ⊢ <;> linarith

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

/-! ## Decimal reduction -/

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

/-! ## The exact reference method

This is the exact selection rule underlying Schubfach, stated at a decimal
exponent `k` and read in the scaled domain: prefer a multiple of ten that
round-trips, and settle for a nearest integer, ties to even, when there is none.
A multiple of ten round-trips exactly when a digit can be dropped,
`coarse_roundtrip_iff_next_grid`, so the first case is where the shortest
representation is coarser than the grid at `k`.

Only two properties of `k` are used. The grid must be fine enough that a
nearest grid point round-trips, `1 ≤ u`, and coarse enough that the round-trip
interval, one ULP wide, cannot hold two multiples of ten, `u < 10`. That second
bound also pins down where the one multiple of ten can be,
`coarse_roundtrip_adjacent`, which is how an implementation gets away with
testing two candidates.
-/

/-- Whether some multiple of ten round-trips on the grid at `k`. -/
def CoarseRoundtrip (f : ℕ) (e k : ℤ) : Prop :=
  ∃ c : ℕ, c % 10 = 0 ∧ Roundtrips f e (c * 10 ^ k)

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

/-- The exact method: a multiple of ten that round-trips if one exists, and
    otherwise a nearest value on the grid at `k`, ties to even. The second case
    says what the computation establishes, a half-step bound and evenness at an
    exact midpoint, rather than the correct rounding those two imply. -/
def ExactCandidate (f : ℕ) (e k : ℤ) (d : ℕ) : Prop :=
  let x := value f e * 10 ^ (-k)
  (d % 10 = 0 ∧ Roundtrips f e (d * 10 ^ k)) ∨
    (¬CoarseRoundtrip f e k ∧ |(d : ℚ) - x| ≤ 1 / 2 ∧
      (|(d : ℚ) - x| = 1 / 2 → d % 2 = 0))

/-- At most one multiple of ten round-trips: two distinct ones are ten grid
    steps apart, while the round-trip interval is `u < 10` steps wide. -/
private theorem coarse_roundtrip_unique (f : ℕ) (e k : ℤ)
    (hcoarse : ulp e * 10 ^ (-k) < 10) {c₁ c₂ : ℕ}
    (h₁ : c₁ % 10 = 0) (h₂ : c₂ % 10 = 0)
    (hr₁ : Roundtrips f e (c₁ * 10 ^ k)) (hr₂ : Roundtrips f e (c₂ * 10 ^ k)) :
    c₁ = c₂ := by
  let x := value f e * 10 ^ (-k)
  have hd₁ := abs_sub_le_half_ulp f e k hr₁
  have hd₂ := abs_sub_le_half_ulp f e k hr₂
  have hsum : |(c₁ : ℚ) - (c₂ : ℚ)| < 10 :=
    calc |(c₁ : ℚ) - (c₂ : ℚ)| ≤ |(c₁ : ℚ) - x| + |x - (c₂ : ℚ)| :=
          abs_sub_le _ _ _
      _ = |(c₁ : ℚ) - x| + |(c₂ : ℚ) - x| := by rw [abs_sub_comm x]
      _ < 10 := by linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hsum
  have hn₁ : c₁ < c₂ + 10 := by
    exact_mod_cast (show (c₁ : ℚ) < (c₂ : ℚ) + 10 by linarith)
  have hn₂ : c₂ < c₁ + 10 := by
    exact_mod_cast (show (c₂ : ℚ) < (c₁ : ℚ) + 10 by linarith)
  omega

/-- Where to look for it. Take a multiple of ten `c` bracketing the scaled value
    from below, to within half a ULP and less than one coarse step. Then a
    multiple of ten that round-trips is `c` or the next one up: the round-trip
    reaches half a ULP either side of the value too, which confines it to
    `(c - 10, c + 20)`, where the only multiples of ten are `c` and `c + 10`.
    The tolerance is the round-trip's own radius, so an implementation has two
    candidates to test from any bracket it locates the value to that well. -/
theorem coarse_roundtrip_adjacent (f : ℕ) (e k : ℤ)
    (hcoarse : ulp e * 10 ^ (-k) < 10) {c d : ℕ}
    (hc : c % 10 = 0) (hd : d % 10 = 0)
    (hlo : (c : ℚ) - ulp e * 10 ^ (-k) / 2 ≤ value f e * 10 ^ (-k))
    (hhi : value f e * 10 ^ (-k) < (c : ℚ) + 10 + ulp e * 10 ^ (-k) / 2)
    (hr : Roundtrips f e (d * 10 ^ k)) :
    d = c ∨ d = c + 10 := by
  obtain ⟨hlo', hhi'⟩ := abs_le.mp (abs_sub_le_half_ulp f e k hr)
  have h10 : c < d + 10 := by
    exact_mod_cast (show (c : ℚ) < (d : ℚ) + 10 by linarith)
  have h20 : d < c + 20 := by
    exact_mod_cast (show (d : ℚ) < (c : ℚ) + 20 by linarith)
  omega

/--
Correctness of the exact method. In the coarse case the candidate carries
trailing zeros, and after stripping them every value on the reduced grid is
still a multiple of ten back at `k`, where uniqueness identifies it with the
candidate; that single fact gives both shortness and correct rounding, and
leaves no tie to resolve. In the fine case the candidate has no trailing zero to
strip, since one would itself be a coarse candidate, so nothing on any coarser
grid round-trips, and correct rounding is the half-step bound read through
`correctly_rounded_of_le_half`.
-/
theorem exact_candidate_correct (f : ℕ) (e k : ℤ) {d : ℕ} (hf0 : 0 < f)
    (hfine : 1 ≤ ulp e * 10 ^ (-k)) (hcoarse : ulp e * 10 ^ (-k) < 10)
    (hd : ExactCandidate f e k d) :
    let (d', k') := reduceDecimal d k
    Shortest f e d' k' ∧ CorrectlyRounded f e d' k' := by
  -- Both cases round-trip: the coarse one by assumption, the fine one because
  -- the grid at `k` is no coarser than one ULP.
  have hrt : Roundtrips f e (d * 10 ^ k) := by
    rcases hd with ⟨-, hrt⟩ | ⟨-, hle, -⟩
    · exact hrt
    · exact roundtrips_of_le_half f e k d hfine hle
  obtain ⟨t, hkt, hstrip⟩ := reduce_shift d k
  have hstop := reduce_reduced d k
  have hval := reduce_value d k
  rcases hred : reduceDecimal d k with ⟨d', k'⟩
  simp only [hred] at hkt hstrip hstop hval ⊢
  have hrt' : Roundtrips f e ((d' : ℚ) * 10 ^ k') := by rw [hval]; exact hrt
  -- Reduction never reaches zero, which does not round-trip, so it stopped at a
  -- significand with no trailing zero.
  have hne : d' % 10 ≠ 0 := by
    rcases hstop with h0 | h10
    · rw [h0] at hrt'
      exact absurd (by simpa using hrt') (not_roundtrips_zero f e hf0)
    · exact h10
  have hmul10 (c s : ℕ) : (c * 10 ^ (s + 1)) % 10 = 0 := by
    rw [pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_mod_left _ _
  rcases hd with ⟨h10, -⟩ | ⟨hnone, hle, heven⟩
  · -- The coarse case.
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp only [pow_zero, Nat.mul_one] at hstrip
        omega
      · exact ht
    -- Every value that round-trips on the reduced grid is the candidate itself.
    have hstep (c : ℕ) (hc : Roundtrips f e ((c : ℚ) * 10 ^ k')) : c = d' := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hck : Roundtrips f e (((c * 10 ^ (s + 1) : ℕ) : ℚ) * 10 ^ k) := by
        rw [ten_pow_shift c (s + 1), show k + ((s + 1 : ℕ) : ℤ) = k' from by
          rw [hkt]]
        exact hc
      have heq := coarse_roundtrip_unique f e k hcoarse (hmul10 c s) h10 hck hrt
      rw [hstrip] at heq
      exact Nat.eq_of_mul_eq_mul_right (by positivity) heq
    refine ⟨⟨hrt', fun c hc => hne ?_⟩, ?_⟩
    · obtain ⟨c', h10', hc'⟩ :=
        (coarse_roundtrip_iff_next_grid f e k').mpr ⟨c, hc⟩
      rw [← hstep c' hc']
      exact h10'
    · have hclose (c : ℕ)
          (hc : |(c : ℚ) * 10 ^ k' - value f e|
            ≤ |(d' : ℚ) * 10 ^ k' - value f e|) : c = d' :=
        hstep c (roundtrips_of_abs_le f e hrt' hc)
      refine ⟨fun c => ?_, fun c hc => Or.inl (hclose c hc.ge)⟩
      by_contra hcon
      rw [hclose c (not_le.mp hcon).le] at hcon
      exact hcon le_rfl
  · -- The fine case.
    have hd10 : d % 10 ≠ 0 := fun h10 => hnone ⟨d, h10, hrt⟩
    have ht : t = 0 := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · exact ht
      · exfalso
        obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        exact hd10 (by rw [hstrip]; exact hmul10 d' s)
    subst ht
    simp only [pow_zero, Nat.mul_one] at hstrip
    rw [← hstrip, show k' = k from by rw [hkt]; simp]
    exact ⟨⟨hrt, fun c hc =>
        hnone ((coarse_roundtrip_iff_next_grid f e k).mpr ⟨c, hc⟩)⟩,
      correctly_rounded_of_le_half f e d k hle heven⟩

/-! ## Certified modular windows

An implementation reads its exact quantities through lossy comparisons, and
where a comparison is ambiguous the ambiguity is a narrow window of residues.
Closing such a window is a Diophantine question: can `g·f mod modulus` land in
`[lo, hi]` for some significand `f` in `[f0, f1]`? Nothing in this section knows
what the residue means.

One multiplier `q` answers the question. Write `y = g·f - modulus·j` for the
residue and `r = g·q - modulus·p` for the error of an approximation
`p/q ≈ g/modulus`. Then

    modulus·(p·f - q·j) = q·y - f·r,

so if `q·y - f·r` stays strictly between two consecutive multiples of `modulus`
throughout the box `f ∈ [f0, f1]`, `y ∈ [lo, hi]`, no `f` can put the residue in
the window. Convergent denominators of `g/modulus` make `r` small enough that
such a `q` is easy to find.

The multiplier is a witness, not an assumption. `ModWindows.search` runs during
elaboration, outside the proof term, and `modCertTactic` quotes what it returns
as a literal for the kernel to check against `ModWindows.refutedBy`. A bad
multiplier is a failed proof rather than an unsound one, so no theorem here
depends on how the search works.
-/

/-- A modular window problem: the progression `g·f mod modulus`, the range
    `f0 ≤ f ≤ f1` it runs over, and the closed windows of residues to
    exclude. -/
structure ModWindows where
  g : ℕ
  modulus : ℕ
  f0 : ℕ
  f1 : ℕ
  windows : List (ℤ × ℤ)

private def modWindowRefuted (g modulus f0 f1 lo hi q : ℤ) : Bool :=
  let p := (2 * (g * q) + modulus) / (2 * modulus)
  let r := g * q - modulus * p
  -- `f·r` runs between the two endpoint values, in whichever order the sign
  -- of `r` dictates.
  let lo' := q * lo - max (f0 * r) (f1 * r)
  let hi' := q * hi - min (f0 * r) (f1 * r)
  decide (0 < q ∧ modulus * (lo' / modulus) < lo'
    ∧ hi' < modulus * (lo' / modulus) + modulus)

/-- Every window of the problem refuted by the one multiplier `q`: a handful of
    big-integer operations per window, with the search for `q` left outside. -/
def ModWindows.refutedBy (W : ModWindows) (q : ℤ) : Bool :=
  W.windows.all fun w => modWindowRefuted W.g W.modulus W.f0 W.f1 w.1 w.2 q

/-- A value strictly between consecutive multiples of `modulus` is absurd. -/
private theorem window_gap_absurd {modulus lo' hi' v : ℤ}
    (hmodulus : 0 < modulus)
    (hlo : lo' ≤ modulus * v) (hhi : modulus * v ≤ hi')
    (hgap_lo : modulus * (lo' / modulus) < lo')
    (hgap_hi : hi' < modulus * (lo' / modulus) + modulus) :
    False := by
  have hv_lo : lo' / modulus < v :=
    lt_of_mul_lt_mul_left (lt_of_lt_of_le hgap_lo hlo) hmodulus.le
  have hv_hi : v < lo' / modulus + 1 := by
    refine lt_of_mul_lt_mul_left (a := modulus) ?_ hmodulus.le
    calc
      modulus * v ≤ hi' := hhi
      _ < modulus * (lo' / modulus) + modulus := hgap_hi
      _ = modulus * (lo' / modulus + 1) := by ring
  omega

/-- The certificate identity and the resulting bounds on the significand box. -/
private theorem window_bounds {g modulus f0 f1 lo hi q p r f j y : ℤ}
    (hq : 0 < q) (hr : r = g * q - modulus * p)
    (hf0 : f0 ≤ f) (hf1 : f ≤ f1)
    (hy : y = g * f - modulus * j) (hlo : lo ≤ y) (hhi : y ≤ hi) :
    q * lo - max (f0 * r) (f1 * r) ≤ modulus * (p * f - q * j) ∧
      modulus * (p * f - q * j) ≤ q * hi - min (f0 * r) (f1 * r) := by
  have hkey : modulus * (p * f - q * j) = q * y - f * r := by
    rw [hy, hr]
    ring
  have hqy0 : q * lo ≤ q * y := mul_le_mul_of_nonneg_left hlo hq.le
  have hqy1 : q * y ≤ q * hi := mul_le_mul_of_nonneg_left hhi hq.le
  have hfr : min (f0 * r) (f1 * r) ≤ f * r ∧ f * r ≤ max (f0 * r) (f1 * r) := by
    rcases le_total 0 r with hr0 | hr0
    · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hf0 hr0),
        le_trans (mul_le_mul_of_nonneg_right hf1 hr0) (le_max_right _ _)⟩
    · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hf1 hr0),
        le_trans (mul_le_mul_of_nonpos_right hf0 hr0) (le_max_left _ _)⟩
  exact ⟨by linarith [hfr.2], by linarith [hfr.1]⟩

private theorem not_window_hit {g modulus f0 f1 lo hi q f j y : ℤ}
    (hmodulus : 0 < modulus)
    (hcert : modWindowRefuted g modulus f0 f1 lo hi q = true)
    (hf0 : f0 ≤ f) (hf1 : f ≤ f1)
    (hy : y = g * f - modulus * j)
    (hlo : lo ≤ y) (hhi : y ≤ hi) :
    False := by
  simp only [modWindowRefuted, decide_eq_true_eq] at hcert
  obtain ⟨hq, hgap0, hgap1⟩ := hcert
  let p := (2 * (g * q) + modulus) / (2 * modulus)
  obtain ⟨hb0, hb1⟩ :=
    window_bounds
      (p := p)
      (r := g * q - modulus * p)
      hq rfl hf0 hf1 hy hlo hhi
  exact window_gap_absurd hmodulus hb0 hb1 hgap0 hgap1

/-- What a certificate says: no significand in range has its residue in any
    window the multiplier refutes. Everything an implementation has to supply is
    the identification of its own quantity with the residue. -/
theorem ModWindows.not_hit (W : ModWindows) (f : ℕ) (hmodulus : 0 < W.modulus)
    {q : ℤ} (hcert : W.refutedBy q = true) {lo hi : ℤ}
    (hmem : (lo, hi) ∈ W.windows) {y : ℕ} (hf0 : W.f0 ≤ f) (hf1 : f ≤ W.f1)
    (hy : y = W.g * f % W.modulus)
    (hlo : lo ≤ (y : ℤ)) (hhi : (y : ℤ) ≤ hi) :
    False := by
  have hwindow : modWindowRefuted W.g W.modulus W.f0 W.f1 lo hi q = true :=
    List.all_eq_true.mp hcert _ hmem
  refine not_window_hit (f := (f : ℤ))
    (j := ((W.g * f / W.modulus : ℕ) : ℤ))
    (by exact_mod_cast hmodulus) hwindow (by exact_mod_cast hf0)
    (by exact_mod_cast hf1) ?_ hlo hhi
  have hz : ((W.modulus * (W.g * f / W.modulus) + W.g * f % W.modulus : ℕ) : ℤ)
      = ((W.g * f : ℕ) : ℤ) := by
    exact_mod_cast Nat.div_add_mod (W.g * f) W.modulus
  rw [hy]
  push_cast at hz ⊢
  linarith

/--
The multiplier is searched for rather than tabulated, by the elaborator rather
than by the kernel. Convergent denominators of `g/modulus` give the relevant
best rational approximations. The Euclidean remainder `v` that produces `qc` is
the error `|g·qc - modulus·p|`; it must fall below `modulus/(f1 + 1)` before a
window can be refuted. Testing that first skips the small denominators and
leaves few window checks per problem. Such a denominator leaves the span of
`q·y - f·r` at about `2·√(n·(hi-lo)/modulus)` of `modulus`, where `n` is the
number of significands in the box, so it fits between consecutive multiples with
room to spare.
-/
private def modCertSearch (W : ModWindows) : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ
  | 0, _, _, _, qc => qc
  | n + 1, u, v, qp, qc =>
    if decide (((W.f1 : ℤ) + 1) * v < W.modulus) && W.refutedBy qc then
      qc
    else if v = 0 then
      qc
    else
      modCertSearch W n v (u % v) qc (u / v * qc + qp)

/-- A multiplier refuting every window, or the best attempt at one. Untrusted:
    what it returns is checked by `refutedBy`. -/
def ModWindows.search (W : ModWindows) : ℤ :=
  modCertSearch W 80 W.modulus ((W.g : ℤ) % (W.modulus : ℤ)) 0 1

open Lean Elab Tactic Meta in
/-- Close a goal `∃ q, W.refutedBy q = true`, where `W` is a definition applied
    to one integer literal, by running the given search on that literal during
    elaboration and quoting the multiplier it returns. Only the literal reaches
    the proof term, where the kernel checks the certificate. -/
def modCertTactic (search : ℤ → ℤ) : TacticM Unit := do
  let target ← whnfR (← (← getMainGoal).getType)
  let_expr Exists _ pred := target
    | throwError "mod_cert: expected `∃ q, W.refutedBy q = true`"
  let_expr Eq _ lhs _ := pred.bindingBody!
    | throwError "mod_cert: expected an equation under the existential"
  let_expr ModWindows.refutedBy problem _ := lhs
    | throwError "mod_cert: expected `W.refutedBy q`, got {lhs}"
  let .app _ argument := problem
    | throwError "mod_cert: {problem} is not applied to an index"
  let some index := argument.int?
    | throwError "mod_cert: the index {argument} is not a literal"
  let q ← Term.exprToSyntax (toExpr (search index))
  evalTactic (← `(tactic| exact ⟨$q, by decide +kernel⟩))
