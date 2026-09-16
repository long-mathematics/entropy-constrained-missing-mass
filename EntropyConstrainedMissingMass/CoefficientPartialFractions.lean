import EntropyConstrainedMissingMass.HomogeneousCoefficients
import Mathlib.Tactic.FieldSimp

/-! Exact partial fractions for complete homogeneous coefficients, and for their
first-order differences. They also verify the starting coefficient at index zero. -/

namespace EntropyConstrainedMissingMass

theorem homogeneous3_eq_of_recurrence (x y z : ℝ) (f : ℕ → ℝ)
    (h0 : f 0 = 1) (h1 : f 1 = x + y + z)
    (h2 : f 2 = (x + y + z) ^ 2 - (x * y + x * z + y * z))
    (hr : ∀ n, f (n + 3) = (x + y + z) * f (n + 2) -
      (x * y + x * z + y * z) * f (n + 1) + x * y * z * f n) (n : ℕ) :
    homogeneous3 x y z n = f n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 3
    · interval_cases n
      · exact h0.symm
      · simpa only [homogeneous3_one] using h1.symm
      · simpa only [homogeneous3_two] using h2.symm
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [homogeneous3_cubic_recurrence, hr,
        ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]

theorem homogeneous3_partial_fraction (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (n : ℕ) :
    homogeneous3 x y z n =
      x ^ (n + 2) / ((x - y) * (x - z)) +
      y ^ (n + 2) / ((y - x) * (y - z)) +
      z ^ (n + 2) / ((z - x) * (z - y)) := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
  have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hyx' : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hzx' : z - x ≠ 0 := sub_ne_zero.mpr hxz.symm
  have hzy' : z - y ≠ 0 := sub_ne_zero.mpr hyz.symm
  apply homogeneous3_eq_of_recurrence x y z (fun k =>
    x ^ (k + 2) / ((x - y) * (x - z)) +
    y ^ (k + 2) / ((y - x) * (y - z)) +
    z ^ (k + 2) / ((z - x) * (z - y)))
  · norm_num
    field_simp
    ring
  · norm_num
    field_simp
    ring
  · norm_num
    field_simp
    ring
  · intro k
    simp only [pow_add]
    field_simp
    ring

/-- The coefficient at a negative index is zero. -/
def previousHomogeneous3 (x y z : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => homogeneous3 x y z n

/-- The coefficient of `(1 - β w)G(w)` at a natural index. -/
def weightedCoefficient (β x y z : ℝ) (n : ℕ) : ℝ :=
  homogeneous3 x y z n - β * previousHomogeneous3 x y z n

@[simp] theorem weightedCoefficient_zero (β x y z : ℝ) : weightedCoefficient β x y z 0 = 1 := by
  simp [weightedCoefficient, previousHomogeneous3]

theorem weightedCoefficient_partial_fraction (β x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (n : ℕ) :
    weightedCoefficient β x y z n =
      (x * (x - β) / ((x - y) * (x - z))) * x ^ n +
      (y * (y - β) / ((y - x) * (y - z))) * y ^ n +
      (z * (z - β) / ((z - x) * (z - y))) * z ^ n := by
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hxz
  have hyz' : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hyx' : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hzx' : z - x ≠ 0 := sub_ne_zero.mpr hxz.symm
  have hzy' : z - y ≠ 0 := sub_ne_zero.mpr hyz.symm
  cases n with
  | zero =>
    rw [weightedCoefficient_zero]
    simp only [pow_zero, mul_one]
    field_simp
    ring
  | succ n =>
    simp only [weightedCoefficient, previousHomogeneous3,
      homogeneous3_partial_fraction x y z hxy hxz hyz, pow_add]
    ring

/-- After cancelling the middle exponential, the two remaining terms are strictly negative. -/
theorem weightedCoefficient_middle_strict_concavity {β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (n : ℕ) :
    weightedCoefficient β x y z (n + 2) - 2 * y * weightedCoefficient β x y z (n + 1) +
      y ^ 2 * weightedCoefficient β x y z n < 0 := by
  have hxz := hyz.trans hxy
  have hx : 0 < x := (hz.trans hyz).trans hxy
  have hβz : z < β := hxz.trans hβx
  have hc1 : x * (x - β) / ((x - y) * (x - z)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx (sub_neg.mpr hβx))
      (mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hxz))
  have hc3 : z * (z - β) / ((z - x) * (z - y)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz (sub_neg.mpr hβz))
      (mul_pos_of_neg_of_neg (sub_neg.mpr hxz) (sub_neg.mpr hyz))
  have heq : weightedCoefficient β x y z (n + 2) -
      2 * y * weightedCoefficient β x y z (n + 1) + y ^ 2 * weightedCoefficient β x y z n =
      (x * (x - β) / ((x - y) * (x - z))) * x ^ n * (x - y) ^ 2 +
      (z * (z - β) / ((z - x) * (z - y))) * z ^ n * (z - y) ^ 2 := by
    simp only [weightedCoefficient_partial_fraction β x y z hxy.ne.symm hxz.ne.symm hyz.ne.symm,
      pow_add]
    ring
  rw [heq]
  exact add_neg (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc1 (pow_pos hx _))
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy.ne.symm)))
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc3 (pow_pos hz _))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hyz.ne)))

end EntropyConstrainedMissingMass
