import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-! Complete homogeneous coefficients in two and three variables.
The nested positive recurrences enumerate each monomial once. The Turán identity
is proved algebraically, without division by differences of variables, so equal
and zero variables are included. -/

namespace EntropyConstrainedMissingMass

/-- Sum of all monomials of total degree n in two variables. -/
def homogeneous2 (x y : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => x ^ (n + 1) + y * homogeneous2 x y n

/-- Sum of all monomials of total degree n in three variables. -/
def homogeneous3 (x y z : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => homogeneous2 x y (n + 1) + z * homogeneous3 x y z n

theorem homogeneous2_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    0 ≤ homogeneous2 x y n := by
  induction n with
  | zero => simp [homogeneous2]
  | succ n ih => exact add_nonneg (pow_nonneg hx _) (mul_nonneg hy ih)

theorem homogeneous3_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ homogeneous3 x y z n := by
  induction n with
  | zero => simp [homogeneous3]
  | succ n ih => exact add_nonneg (homogeneous2_nonneg hx hy _) (mul_nonneg hz ih)

theorem homogeneous3_pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) (n : ℕ) :
    0 < homogeneous3 x y z n := by
  induction n with
  | zero => simp [homogeneous3]
  | succ n ih => exact add_pos_of_nonneg_of_pos (homogeneous2_nonneg hx hy _) (mul_pos hz ih)

theorem homogeneous3_cubic_recurrence (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z (n + 3) =
      (x + y + z) * homogeneous3 x y z (n + 2) -
      (x * y + x * z + y * z) * homogeneous3 x y z (n + 1) +
      x * y * z * homogeneous3 x y z n := by
  simp only [homogeneous3, homogeneous2, pow_succ]
  ring

/-- The Turán determinant at positive index n+1. -/
def homogeneousTuran (x y z : ℝ) (n : ℕ) : ℝ :=
  homogeneous3 x y z (n + 1) ^ 2 - homogeneous3 x y z n * homogeneous3 x y z (n + 2)

theorem homogeneousTuran_recurrence (x y z : ℝ) (n : ℕ) :
    homogeneousTuran x y z (n + 3) =
      (x * y + x * z + y * z) * homogeneousTuran x y z (n + 2) -
      ((x + y + z) * (x * y * z)) * homogeneousTuran x y z (n + 1) +
      (x * y * z) ^ 2 * homogeneousTuran x y z n := by
  unfold homogeneousTuran
  simp only [homogeneous3, homogeneous2, pow_succ, Nat.add_assoc]
  ring

/-- The exact three-variable Turán identity, including coincident and zero variables. -/
theorem homogeneous3_turan (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z (n + 1) ^ 2 -
        homogeneous3 x y z n * homogeneous3 x y z (n + 2) =
      homogeneous3 (x * y) (x * z) (y * z) (n + 1) := by
  change homogeneousTuran x y z n = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain rfl | rfl | rfl | ⟨k, rfl⟩ : n = 0 ∨ n = 1 ∨ n = 2 ∨ ∃ k, n = k + 3 := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      by_cases h1 : n = 1
      · exact Or.inr (Or.inl h1)
      by_cases h2 : n = 2
      · exact Or.inr (Or.inr (Or.inl h2))
      exact Or.inr (Or.inr (Or.inr ⟨n - 3, by omega⟩))
    · simp [homogeneousTuran, homogeneous3, homogeneous2]
      ring
    · simp [homogeneousTuran, homogeneous3, homogeneous2]
      ring
    · simp [homogeneousTuran, homogeneous3, homogeneous2]
      ring
    · rw [homogeneousTuran_recurrence, ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]
      have hr := homogeneous3_cubic_recurrence (x * y) (x * z) (y * z) (k + 1)
      simp only [Nat.add_assoc] at hr ⊢
      rw [hr]
      ring

theorem homogeneous3_log_concave {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    homogeneous3 x y z n * homogeneous3 x y z (n + 2) ≤ homogeneous3 x y z (n + 1) ^ 2 := by
  have h := homogeneous3_nonneg (mul_nonneg hx hy) (mul_nonneg hx hz) (mul_nonneg hy hz) (n + 1)
  rw [← homogeneous3_turan] at h
  linarith

theorem homogeneous3_strict_log_concave {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (n : ℕ) :
    homogeneous3 x y z n * homogeneous3 x y z (n + 2) < homogeneous3 x y z (n + 1) ^ 2 := by
  have h := homogeneous3_pos (mul_nonneg hx.le hy.le) (mul_nonneg hx.le hz.le) (mul_pos hy hz) (n + 1)
  rw [← homogeneous3_turan] at h
  linarith


/-- Explicit monomial enumeration, avoiding any convergence interpretation. -/
theorem homogeneous2_eq_sum (x y : ℝ) (n : ℕ) :
    homogeneous2 x y n = ∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i) := by
  induction n with
  | zero => simp [homogeneous2]
  | succ n ih =>
    rw [homogeneous2, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have he : n + 1 - i = (n - i) + 1 := by have := Finset.mem_range.mp hi; omega
    rw [he, pow_succ]
    ring

theorem homogeneous3_eq_sum (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n = ∑ i ∈ Finset.range (n + 1), homogeneous2 x y i * z ^ (n - i) := by
  induction n with
  | zero => simp [homogeneous3, homogeneous2]
  | succ n ih =>
    rw [homogeneous3, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have he : n + 1 - i = (n - i) + 1 := by have := Finset.mem_range.mp hi; omega
    rw [he, pow_succ]
    ring

/-- Every exponent triple occurs exactly once, via i=a+b and j=a. -/
theorem homogeneous3_eq_monomial_sum (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n =
      ∑ i ∈ Finset.range (n + 1), (∑ j ∈ Finset.range (i + 1), x ^ j * y ^ (i - j)) * z ^ (n - i) := by
  simp_rw [homogeneous3_eq_sum, homogeneous2_eq_sum]

@[simp] theorem homogeneous3_zero (x y z : ℝ) : homogeneous3 x y z 0 = 1 := rfl

theorem homogeneous3_one (x y z : ℝ) : homogeneous3 x y z 1 = x + y + z := by
  simp [homogeneous3, homogeneous2]

theorem homogeneous3_two (x y z : ℝ) :
    homogeneous3 x y z 2 = (x + y + z) ^ 2 - (x * y + x * z + y * z) := by
  simp [homogeneous3, homogeneous2]
  ring

/-- Complete homogeneous coefficients depend only on the elementary symmetric values. -/
theorem homogeneous3_eq_of_elementary (x y z a b c : ℝ)
    (h1 : x + y + z = a + b + c)
    (h2 : x * y + x * z + y * z = a * b + a * c + b * c)
    (h3 : x * y * z = a * b * c) (n : ℕ) :
    homogeneous3 x y z n = homogeneous3 a b c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · interval_cases n
      · rfl
      · simpa only [homogeneous3_one] using h1
      · simp only [homogeneous3_two, h1, h2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [homogeneous3_cubic_recurrence, homogeneous3_cubic_recurrence,
        ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega), h1, h2, h3]

theorem homogeneous3_swap_left (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n = homogeneous3 y x z n :=
  homogeneous3_eq_of_elementary x y z y x z (by ring) (by ring) (by ring) n

theorem homogeneous3_swap_right (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n = homogeneous3 x z y n :=
  homogeneous3_eq_of_elementary x y z x z y (by ring) (by ring) (by ring) n

theorem homogeneous3_pos_of_ne_zero {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (n : ℕ) :
    0 < homogeneous3 x y z n := by
  rcases hne with hx0 | hy0 | hz0
  · rw [homogeneous3_swap_left x y z, homogeneous3_swap_right y x z]
    exact homogeneous3_pos hy hz (lt_of_le_of_ne hx (Ne.symm hx0)) n
  · rw [homogeneous3_swap_right]
    exact homogeneous3_pos hx hz (lt_of_le_of_ne hy (Ne.symm hy0)) n
  · exact homogeneous3_pos hx hy (lt_of_le_of_ne hz (Ne.symm hz0)) n

end EntropyConstrainedMissingMass
