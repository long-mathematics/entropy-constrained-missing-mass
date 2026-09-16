import EntropyConstrainedMissingMass.HomogeneousCoefficients
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The coefficient extremum estimate of §3. The transfer argument is discrete:
decreasing a pair product at fixed pair sum increases a positive coefficient. -/

namespace EntropyConstrainedMissingMass

def coefficientDifference (x y z : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => homogeneous3 x y z (n + 1) - homogeneous3 x y z n

@[simp] theorem coefficientDifference_zero (x y z : ℝ) : coefficientDifference x y z 0 = 1 := rfl

theorem coefficientDifference_eq (x y z : ℝ) (n : ℕ) :
    coefficientDifference x y z n = homogeneous3 x y z n -
      (if n = 0 then 0 else homogeneous3 x y z (n - 1)) := by
  cases n <;> simp [coefficientDifference, homogeneous3]

theorem coefficientDifference_one (x y z : ℝ) :
    coefficientDifference x y z 1 = x + y + z - 1 := by
  simp [coefficientDifference, homogeneous3, homogeneous2]

theorem coefficientDifference_swap_left (x y z : ℝ) (n : ℕ) :
    coefficientDifference x y z n = coefficientDifference y x z n := by
  cases n with
  | zero => rfl
  | succ n => simp only [coefficientDifference, homogeneous3_swap_left x y z]

theorem coefficientDifference_swap_right (x y z : ℝ) (n : ℕ) :
    coefficientDifference x y z n = coefficientDifference x z y n := by
  cases n with
  | zero => rfl
  | succ n => simp only [coefficientDifference, homogeneous3_swap_right x y z]

theorem coefficientDifference_pair_recurrence (x y z : ℝ) (n : ℕ) :
    coefficientDifference x y z (n + 2) =
      (y + z) * coefficientDifference x y z (n + 1) -
      y * z * coefficientDifference x y z n + x ^ (n + 2) - x ^ (n + 1) := by
  cases n with
  | zero => simp [coefficientDifference, homogeneous3, homogeneous2]; ring
  | succ n =>
    simp only [coefficientDifference, homogeneous3, homogeneous2, pow_succ]
    ring

theorem coefficientDifference_pos_nonzero {x y z : ℝ} {n : ℕ}
    (hpos : 0 < coefficientDifference x y z (n + 1)) : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases n <;> norm_num [coefficientDifference, homogeneous3, homogeneous2] at hpos

theorem coefficientDifference_prev_pos {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) {n : ℕ}
    (hpos : 0 < coefficientDifference x y z (n + 1)) :
    0 < coefficientDifference x y z n := by
  cases n with
  | zero => exact zero_lt_one
  | succ n =>
    have hnz := coefficientDifference_pos_nonzero hpos
    have hprev := homogeneous3_pos_of_ne_zero hx hy hz hnz (n + 1)
    have hnonneg := homogeneous3_nonneg hx hy hz n
    have hturan := homogeneous3_log_concave hx hy hz n
    simp only [coefficientDifference] at hpos ⊢
    nlinarith

/-- The positive coefficients form an initial segment. -/
theorem coefficientDifference_pos_of_le {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) {N : ℕ}
    (hpos : 0 < coefficientDifference x y z N) {j : ℕ} (hj : j ≤ N) :
    0 < coefficientDifference x y z j := by
  induction N with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    exact zero_lt_one
  | succ N ih =>
    by_cases heq : j = N + 1
    · simpa [heq] using hpos
    · exact ih (coefficientDifference_prev_pos hx hy hz hpos) (by omega)

/-- A discrete mass transfer: keep the pair sum fixed and decrease its product.
The positivity premise concerns the original coefficient only. -/
theorem coefficientDifference_le_of_pair_product {x y z Y Z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hsum : Y + Z = y + z) (hprod : Y * Z ≤ y * z) (N : ℕ)
    (hpos : 0 < coefficientDifference x y z N) :
    coefficientDifference x y z N ≤ coefficientDifference x Y Z N := by
  let d := fun n => coefficientDifference x Y Z n - coefficientDifference x y z n
  have hd0 : d 0 = 0 := by simp [d]
  have hd1 : d 1 = 0 := by simp only [d, coefficientDifference_one]; linarith
  have hrec (n : ℕ) : d (n + 2) - Y * d (n + 1) =
      Z * (d (n + 1) - Y * d n) +
        (y * z - Y * Z) * coefficientDifference x y z n := by
    dsimp [d]
    rw [coefficientDifference_pair_recurrence, coefficientDifference_pair_recurrence,
      ← hsum]
    ring
  have hnonneg (n : ℕ) (hn : n ≤ N) : 0 ≤ d n ∧ 0 ≤ d (n + 1) - Y * d n := by
    induction n with
    | zero => simp [hd0, hd1]
    | succ n ih =>
      have hprev := ih (by omega)
      have hb := (coefficientDifference_pos_of_le hx hy hz hpos (show n ≤ N by omega)).le
      constructor
      · have := mul_nonneg hY hprev.1
        linarith [hprev.2]
      · rw [show n + 1 + 1 = n + 2 by omega, hrec]
        exact add_nonneg (mul_nonneg hZ hprev.2) (mul_nonneg (sub_nonneg.mpr hprod) hb)
  exact sub_nonneg.mp (hnonneg N le_rfl).1

theorem coefficientDifference_zero_last_le_one {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) (n : ℕ) :
    coefficientDifference x y 0 n ≤ 1 := by
  cases n with
  | zero => exact le_rfl
  | succ n =>
    have hh := homogeneous2_nonneg hx hy n
    have hp : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx hx1
    have heq (k : ℕ) : homogeneous3 x y 0 k = homogeneous2 x y k := by
      cases k <;> simp [homogeneous3, homogeneous2]
    simp only [coefficientDifference, heq]
    rw [homogeneous2]
    nlinarith

theorem coefficientDifference_two_ones (r : ℝ) (n : ℕ) :
    coefficientDifference r 1 1 n = homogeneous2 r 1 n := by
  cases n <;> simp [coefficientDifference, homogeneous3, homogeneous2]

theorem homogeneous2_one_geometric_identity (r : ℝ) (n : ℕ) :
    (1 - r) * homogeneous2 r 1 n = 1 - r ^ (n + 1) := by
  induction n with
  | zero => simp [homogeneous2]
  | succ n ih =>
    rw [homogeneous2, one_mul]
    calc
      (1 - r) * (r ^ (n + 1) + homogeneous2 r 1 n) =
          (1 - r) * r ^ (n + 1) + (1 - r) * homogeneous2 r 1 n := by ring
      _ = (1 - r) * r ^ (n + 1) + (1 - r ^ (n + 1)) := by rw [ih]
      _ = 1 - r ^ (n + 1 + 1) := by rw [pow_succ r (n + 1)]; ring

theorem coefficientDifference_two_ones_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    coefficientDifference r 1 1 n ≤ (1 - r)⁻¹ := by
  rw [coefficientDifference_two_ones, ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  have heq := homogeneous2_one_geometric_identity r n
  have hpow := pow_nonneg hr (n + 1)
  nlinarith

/-- The manuscript's coefficient-extremum lemma, including all boundary coordinates. -/
theorem coefficient_extremum {x y z : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hsigma : 0 < 3 - x - y - z) (N : ℕ) :
    coefficientDifference x y z N ≤ max 1 (3 - x - y - z)⁻¹ := by
  by_cases hnonpos : coefficientDifference x y z N ≤ 0
  · exact hnonpos.trans (zero_le_one.trans (le_max_left _ _))
  have hpos : 0 < coefficientDifference x y z N := lt_of_not_ge hnonpos
  by_cases hyz : y + z ≤ 1
  · have htransfer := coefficientDifference_le_of_pair_product hx hy hz
      (add_nonneg hy hz) (le_refl 0) (by ring : y + z + 0 = y + z)
      (by simpa using mul_nonneg hy hz : (y + z) * 0 ≤ y * z) N hpos
    exact htransfer.trans
      ((coefficientDifference_zero_last_le_one hx hx1 (add_nonneg hy hz) hyz N).trans
        (le_max_left _ _))
  · let r := y + z - 1
    have hr : 0 ≤ r := by dsimp [r]; linarith
    have hr1 : r ≤ 1 := by dsimp [r]; linarith
    have hsum : 1 + r = y + z := by dsimp [r]; ring
    have hprod : 1 * r ≤ y * z := by
      have := mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hz1)
      dsimp [r]
      nlinarith
    have htransfer := coefficientDifference_le_of_pair_product hx hy hz
      zero_le_one hr hsum hprod N hpos
    rw [coefficientDifference_swap_left x 1 r] at htransfer
    have hpos' : 0 < coefficientDifference 1 x r N := hpos.trans_le htransfer
    by_cases hxr : x + r ≤ 1
    · have htransfer' := coefficientDifference_le_of_pair_product zero_le_one hx hr
        (add_nonneg hx hr) (le_refl 0) (by ring : x + r + 0 = x + r)
        (by simpa using mul_nonneg hx hr : (x + r) * 0 ≤ x * r) N hpos'
      exact (htransfer.trans htransfer').trans
        ((coefficientDifference_zero_last_le_one zero_le_one le_rfl (add_nonneg hx hr) hxr N).trans
          (le_max_left _ _))
    · let q := x + r - 1
      have hq : 0 ≤ q := by dsimp [q]; linarith
      have hq1 : q < 1 := by dsimp [q, r]; linarith
      have hsum' : 1 + q = x + r := by dsimp [q]; ring
      have hprod' : 1 * q ≤ x * r := by
        have := mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hr1)
        dsimp [q]
        nlinarith
      have htransfer' := coefficientDifference_le_of_pair_product zero_le_one hx hr
        zero_le_one hq hsum' hprod' N hpos'
      rw [coefficientDifference_swap_right 1 1 q, coefficientDifference_swap_left 1 q 1]
        at htransfer'
      have hbound := coefficientDifference_two_ones_le hq hq1 N
      have hden : 1 - q = 3 - x - y - z := by dsimp [q, r]; ring
      rw [hden] at hbound
      exact ((htransfer.trans htransfer').trans hbound).trans (le_max_right _ _)

end EntropyConstrainedMissingMass
