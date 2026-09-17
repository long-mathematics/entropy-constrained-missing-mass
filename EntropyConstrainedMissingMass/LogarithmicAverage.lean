import EntropyConstrainedMissingMass.RepeatedFourVariation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The literal weighted logarithmic average in the repeated-size proof. -/
open Set MeasureTheory
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The weighting `du/u` cancels the factor u in weighted curvature. -/
theorem weighted_second_derivative_integral {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    (∫ u in x..y, (u * deriv (deriv f) u)/u) = deriv f y - deriv f x := by
  have hc1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 1) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc0 : ContDiffOn ℝ 0 (deriv (deriv f)) (Ioo 0 1) :=
    hc1.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hc2 := hc0.continuousOn
  have hsubset : Icc x y ⊆ Ioo (0 : ℝ) 1 := fun u hu => ⟨hx.trans_le hu.1,hu.2.trans_lt hy⟩
  have hi : IntervalIntegrable (deriv (deriv f)) volume x y :=
    (hc2.mono hsubset).intervalIntegrable_of_Icc hxy.le
  have hd : ∀ u ∈ uIcc x y, HasDerivAt (deriv f) (deriv (deriv f) u) u := by
    intro u hu
    rw [uIcc_of_le hxy.le] at hu
    exact ((hc1.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsubset hu))).hasDerivAt
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hxy.le] at hu
  have hu0 : u ≠ 0 := ne_of_gt (hx.trans_le hu.1)
  field_simp

/-- The source logarithmic secant and integral average are exactly equal. -/
theorem weighted_log_average {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hx : 0 < x) (hxy : x < y) (hy : y < 1) :
    (deriv f y - deriv f x) / (Real.log y - Real.log x) =
      (∫ u in x..y, (u * deriv (deriv f) u)/u) / Real.log (y/x) := by
  rw [weighted_second_derivative_integral hf hx hxy hy,
    Real.log_div (ne_of_gt (hx.trans hxy)) (ne_of_gt hx)]

end
end EntropyConstrainedMissingMass
