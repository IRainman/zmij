import Mathlib

-- Exact rational value represented by binary significand f and exponent e.
def value (f : ℕ) (e : ℤ) : ℚ := f * 2 ^ e

-- Lower rounding boundary for a regularly spaced floating-point value (m⁻).
def lower (f : ℕ) (e : ℤ) : ℚ := (f - 1 / 2) * 2 ^ e

-- Upper rounding boundary (m⁺).
def upper (f : ℕ) (e : ℤ) : ℚ := (f + 1 / 2) * 2 ^ e

-- Whether the exact rational result r rounds to the regularly spaced value
-- f × 2^e under round-to-nearest, ties-to-even.
def Roundtrips (f : ℕ) (e : ℤ) (r : ℚ) : Prop :=
  if f % 2 = 0 then
    lower f e ≤ r ∧ r ≤ upper f e
  else
    lower f e < r ∧ r < upper f e

-- Whether f × 2^e is a regularly spaced normal binary64 value,
-- excluding powers of 2.
def Regular (f : ℕ) (e : ℤ) : Prop :=
  2 ^ 52 < f ∧ f < 2 ^ 53 ∧
    -1074 ≤ e ∧ e ≤ 971

-- Truncated 128-bit normalized binary significand of 10^k.
def power10Significand (k : ℤ) : ℕ :=
  let e : ℤ :=
    if 0 ≤ k then
      Nat.log 2 (10 ^ k.toNat) + 1
    else
      -Nat.log 2 (10 ^ (-k).toNat)
  ⌊(10 : ℚ) ^ k * 2 ^ (128 - e)⌋₊

-- Converts a regularly spaced binary floating-point value f · 2^e
-- to a decimal significand and exponent using yy's full path.
def toDecimal (f : ℕ) (e : ℤ) : ℕ × ℤ :=
  let k := e * 315653 / 2 ^ 20
  let h := Int.toNat (e + (-k * 217707) / 2 ^ 16)

  let p10 := power10Significand (-k)
  let p10Hi := p10 / 2 ^ 64

  let cb := f * 2 ^ (h + 1)
  let product := cb * p10 / 2 ^ 64
  let sigHi := product / 2 ^ 64
  let sigLo := product % 2 ^ 64

  let one := sigHi % 10
  let ten := sigHi - one
  let c := one * 2 ^ 60 + sigLo / 2 ^ 4
  let halfUlp := p10Hi / 2 ^ (4 - h)
  let t0 := 10 * 2 ^ 60
  let t1 := c + halfUlp

  let roundU1 : Prop :=
    if sigLo = 2 ^ 63 then
      sigHi % 2 = 1
    else
      2 ^ 63 < sigLo

  let roundD0 : Prop :=
    if halfUlp = c then
      f % 2 = 0
    else
      c < halfUlp

  let roundU0 : Prop :=
    if t1 + 1 = t0 then
      f % 2 = 0
    else if k = 0 ∧ t1 = t0 then
      f % 2 = 0
    else
      t0 ≤ t1

  let decOne := sigHi + if roundU1 then 1 else 0
  let decTen := ten + if roundU0 then 10 else 0

  let d := if roundD0 ∨ roundU0 then decTen else decOne
  (d, k)

theorem lower_scaled (f : ℕ) (e k : ℤ) :
    lower f e * 10 ^ (-k) =
      value f e * 10 ^ (-k) - 2 ^ e * 10 ^ (-k) / 2 := by
  simp [lower, value]
  ring

theorem upper_scaled (f : ℕ) (e k : ℤ) :
    upper f e * 10 ^ (-k) =
      value f e * 10 ^ (-k) + 2 ^ e * 10 ^ (-k) / 2 := by
  simp [upper, value]
  ring

theorem decimal_significand_distance
    (f : ℕ) (e : ℤ)
    (h : Regular f e) :
    let (d, k) := toDecimal f e
    let x := value f e * 10 ^ (-k)
    let u := (2 : ℚ) ^ e * 10 ^ (-k)
    if f % 2 = 0 then
      |d - x| ≤ u / 2
    else
      |d - x| < u / 2 := by
  sorry

-- The decimal significand produced by yy lies within the rounding interval
-- after scaling by the decimal exponent.
theorem decimal_significand_in_interval
    (f : ℕ) (e : ℤ)
    (h : Regular f e) :
    let (d, k) := toDecimal f e
    if f % 2 = 0 then
      lower f e * 10 ^ (-k) ≤ d ∧
        d ≤ upper f e * 10 ^ (-k)
    else
      lower f e * 10 ^ (-k) < d ∧
        d < upper f e * 10 ^ (-k) := by
  rcases hdk : toDecimal f e with ⟨d, k⟩
  let x := value f e * 10 ^ (-k)
  let u := (2 : ℚ) ^ e * 10 ^ (-k)

  have hd := decimal_significand_distance f e h

  have hlower :
      lower f e * 10 ^ (-k) = x - u / 2 := by
    dsimp [x, u, lower, value]
    ring

  have hupper :
      upper f e * 10 ^ (-k) = x + u / 2 := by
    dsimp [x, u, upper, value]
    ring

  by_cases heven : f % 2 = 0
  · simp only [heven, ↓reduceIte]
    rw [hlower, hupper]
    have hd' : |d - x| ≤ u / 2 := by
      simpa [hdk, x, u, heven] using hd
    have habs := abs_le.mp hd'
    constructor <;> linarith
  · simp only [heven, ↓reduceIte]
    rw [hlower, hupper]
    have hd' : |d - x| < u / 2 := by
      simpa [hdk, x, u, heven] using hd
    have habs := abs_lt.mp hd'
    constructor <;> linarith

theorem yy_roundtrips
    (f : ℕ) (e : ℤ)
    (h : Regular f e) :
    let (d, k) := toDecimal f e
    Roundtrips f e (d * 10 ^ k) := by
  rcases hdk : toDecimal f e with ⟨d, k⟩

  have hi := decimal_significand_in_interval f e h
  simp only [hdk] at hi

  have hpow_pos : (0 : ℚ) < 10 ^ k := by
    positivity

  have hcancel : (10 : ℚ) ^ (-k) * 10 ^ k = 1 := by
    simpa only [zpow_neg] using
      inv_mul_cancel₀ (ne_of_gt hpow_pos)

  by_cases heven : f % 2 = 0
  · simp only [Roundtrips, heven, ↓reduceIte]
    simp only [heven, ↓reduceIte] at hi
    constructor
    · calc
        lower f e =
            (lower f e * 10 ^ (-k)) * 10 ^ k := by
              rw [mul_assoc, hcancel, mul_one]
        _ ≤ (d : ℚ) * 10 ^ k :=
          mul_le_mul_of_nonneg_right hi.1 hpow_pos.le
    · calc
        (d : ℚ) * 10 ^ k ≤
            (upper f e * 10 ^ (-k)) * 10 ^ k :=
          mul_le_mul_of_nonneg_right hi.2 hpow_pos.le
        _ = upper f e := by
          rw [mul_assoc, hcancel, mul_one]

  · simp only [Roundtrips, heven, ↓reduceIte]
    simp only [heven, ↓reduceIte] at hi
    constructor
    · calc
        lower f e =
            (lower f e * 10 ^ (-k)) * 10 ^ k := by
              rw [mul_assoc, hcancel, mul_one]
        _ < (d : ℚ) * 10 ^ k :=
          mul_lt_mul_of_pos_right hi.1 hpow_pos
    · calc
        (d : ℚ) * 10 ^ k <
            (upper f e * 10 ^ (-k)) * 10 ^ k :=
          mul_lt_mul_of_pos_right hi.2 hpow_pos
        _ = upper f e := by
          rw [mul_assoc, hcancel, mul_one]
