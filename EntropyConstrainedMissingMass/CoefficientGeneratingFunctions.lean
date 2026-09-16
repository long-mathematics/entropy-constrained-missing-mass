import EntropyConstrainedMissingMass.CoefficientPartialFractions
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Formal power series connecting the finite coefficient representation to the manuscript. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

def linearFactor (a : ℝ) : PowerSeries ℝ := 1 - C a * X

def homogeneousSeries (x y z : ℝ) : PowerSeries ℝ := mk (homogeneous3 x y z)

@[simp] theorem coeff_homogeneousSeries (x y z : ℝ) (n : ℕ) :
    coeff n (homogeneousSeries x y z) = homogeneous3 x y z n := coeff_mk _ _

@[simp] theorem constantCoeff_linearFactor (a : ℝ) : constantCoeff (linearFactor a) = 1 := by
  simp [linearFactor]

theorem coeff_linearFactor_mul_zero (a : ℝ) (f : PowerSeries ℝ) :
    coeff 0 (linearFactor a * f) = coeff 0 f := by
  simp [linearFactor, sub_mul, mul_assoc]

theorem coeff_linearFactor_mul_succ (a : ℝ) (f : PowerSeries ℝ) (n : ℕ) :
    coeff (n + 1) (linearFactor a * f) = coeff (n + 1) f - a * coeff n f := by
  simp [linearFactor, sub_mul, mul_assoc, coeff_succ_X_mul]

theorem linearFactor_mul_homogeneousSeries (x y z : ℝ) :
    linearFactor z * homogeneousSeries x y z = mk (homogeneous2 x y) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero, homogeneous3, homogeneous2]
  | succ n =>
    simp only [coeff_linearFactor_mul_succ, coeff_homogeneousSeries, coeff_mk, homogeneous3]
    ring

theorem linearFactor_mul_homogeneous2 (x y : ℝ) :
    linearFactor y * mk (homogeneous2 x y) = mk (fun n => x ^ n) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero, homogeneous2]
  | succ n =>
    simp only [coeff_linearFactor_mul_succ, coeff_mk, homogeneous2]
    ring

theorem linearFactor_mul_geometric (x : ℝ) :
    linearFactor x * mk (fun n => x ^ n) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero]
  | succ n => simp [coeff_linearFactor_mul_succ, pow_succ, mul_comm]

theorem product_linearFactor_mul_homogeneousSeries (x y z : ℝ) :
    (linearFactor x * linearFactor y * linearFactor z) * homogeneousSeries x y z = 1 := by
  rw [mul_assoc, mul_assoc, linearFactor_mul_homogeneousSeries,
    linearFactor_mul_homogeneous2, linearFactor_mul_geometric]

/-- The generating function is exactly the product of the three geometric inverses. -/
theorem homogeneousSeries_eq_product_inverse (x y z : ℝ) :
    homogeneousSeries x y z = (linearFactor x)⁻¹ * (linearFactor y)⁻¹ * (linearFactor z)⁻¹ := by
  have h : constantCoeff (linearFactor x * linearFactor y * linearFactor z) ≠ 0 := by simp
  have heq : (linearFactor x * linearFactor y * linearFactor z)⁻¹ = homogeneousSeries x y z :=
    (inv_eq_iff_mul_eq_one h).mpr (by simpa only [mul_comm] using product_linearFactor_mul_homogeneousSeries x y z)
  rw [← heq, PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev]
  ring

/-- The weighted difference is the coefficient of `(1-βw)G`. -/
theorem coeff_linearFactor_homogeneousSeries (β x y z : ℝ) (n : ℕ) :
    coeff n (linearFactor β * homogeneousSeries x y z) = weightedCoefficient β x y z n := by
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero]
  | succ n => simp [coeff_linearFactor_mul_succ, weightedCoefficient, previousHomogeneous3]

end
end EntropyConstrainedMissingMass
