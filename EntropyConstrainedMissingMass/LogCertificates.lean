import EntropyConstrainedMissingMass.BranchEntropy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact logarithm-series remainder and rational interval certificate interfaces. -/
open Set MeasureTheory
namespace EntropyConstrainedMissingMass
noncomputable section

def logSeries (v : ℝ) (R : ℕ) : ℝ := 2 * ∑ r ∈ Finset.range R, v^(2*r+1)/(2*r+1)

def logRemainder (v : ℝ) (R : ℕ) : ℝ := 2*v^(2*R+1)/((2*R+1)*(1-v^2))

/-- The exact sharp positive-series enclosure displayed in Appendix D. -/
theorem log_certificate {v : ℝ} (hv : 0 ≤ v) (hv1 : v < 1) (R : ℕ) :
    0 ≤ Real.log ((1+v)/(1-v)) - logSeries v R ∧
      Real.log ((1+v)/(1-v)) - logSeries v R ≤ logRemainder v R := by
  have hden : 0 < 1-v^2 := by nlinarith
  let F : ℝ → ℝ := fun x => 1/2*Real.log ((1+x)/(1-x)) -
    ∑ i ∈ Finset.range R, x^(2*i+1)/(2*i+1)
  let f : ℝ → ℝ := fun x => x^(2*R)/(1-x^2)
  have hc : ContinuousOn f (Icc 0 v) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    exact ne_of_gt this
  have hi : IntervalIntegrable f volume 0 v := hc.intervalIntegrable_of_Icc hv
  have he : (∫ x in (0 : ℝ)..v, f x) = F v := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) v, HasDerivAt F (f x) x := by
      intro x hx
      rw [uIcc_of_le hv] at hx
      have h := Real.hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range R
        (show -1 < x by linarith [hx.1]) (hx.2.trans_lt hv1)
      simpa only [F, f, pow_mul] using h
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hb : (∫ x in (0 : ℝ)..v, f x) ≤
      ∫ x in (0 : ℝ)..v, x^(2*R)/(1-v^2) := by
    apply intervalIntegral.integral_mono_on hv hi ((by fun_prop : Continuous
      (fun x : ℝ => x^(2*R)/(1-v^2))).intervalIntegrable _ _)
    intro x hx
    have hxden : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    exact div_le_div_of_nonneg_left (pow_nonneg hx.1 _) hden (by nlinarith [hx.1,hx.2])
  rw [he, intervalIntegral.integral_div, integral_pow] at hb
  simp only [zero_pow (by omega : 2*R+1 ≠ 0), sub_zero] at hb
  have hlo := Real.sum_range_le_log_div hv hv1 R
  dsimp [F] at hb
  dsimp [logSeries, logRemainder]
  constructor
  · linarith
  · have heq : 2 * (v^(2*R+1)/(↑(2*R)+1)/(1-v^2)) =
        2*v^(2*R+1)/((2*(R : ℝ)+1)*(1-v^2)) := by push_cast; field_simp
    push_cast at hb
    push_cast at heq
    linarith

/-- Normalize a positive logarithm to its nonnegative atanh parameter. -/
theorem log_certificate_normalized {y : ℝ} (hy : 1 ≤ y) (R : ℕ) :
    logSeries ((y-1)/(y+1)) R ≤ Real.log y ∧
      Real.log y ≤ logSeries ((y-1)/(y+1)) R + logRemainder ((y-1)/(y+1)) R := by
  have hp : 0 < y+1 := by linarith
  have hv : 0 ≤ (y-1)/(y+1) := div_nonneg (by linarith) hp.le
  have hv1 : (y-1)/(y+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have h := log_certificate hv hv1 R
  have he : (1+(y-1)/(y+1))/(1-(y-1)/(y+1)) = y := by field_simp; ring
  rw [he] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Range reduction by an integer power of two, including negative exponents. -/
theorem log_range_reduction {x y : ℝ} (hy : 0 < y) (j : ℤ)
    (hx : x = (2 : ℝ)^j*y) : Real.log x = (j : ℝ)*Real.log 2 + Real.log y := by
  rw [hx, Real.log_mul (by positivity) (ne_of_gt hy), Real.log_zpow]

end
end EntropyConstrainedMissingMass
