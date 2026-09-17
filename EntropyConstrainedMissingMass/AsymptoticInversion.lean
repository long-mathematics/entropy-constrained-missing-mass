import EntropyConstrainedMissingMass.AsymptoticEntropy

/-! Quantitative inversion of d-log d, with the exact filter meaning used in Section 6. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass

/-- The logarithm increment is bounded by the relative increment. -/
theorem log_increment_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at h
  convert h using 1
  field_simp

private theorem inverse_log_ordered {x y : ℝ} (hy : 2 ≤ y) (hxy : y ≤ x) :
    x - y ≤ 2 * ((x - Real.log x) - (y - Real.log y)) := by
  have hyp : 0 < y := by linarith
  have hxp : 0 < x := hyp.trans_le hxy
  have hlo : 0 ≤ Real.log x - Real.log y :=
    sub_nonneg.mpr (Real.log_le_log hyp hxy)
  have hu := (le_div_iff₀ hyp).mp (log_increment_le hxp hyp)
  have hp := mul_nonneg (sub_nonneg.mpr hy) hlo
  nlinarith only [hu, hp]

/-- An explicit inverse Lipschitz bound, avoiding any assumed asymptotic inverse theorem. -/
theorem inverse_log_abs_bound {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    |x - y| ≤ 2 * |(x - Real.log x) - (y - Real.log y)| := by
  by_cases hxy : y ≤ x
  · have h := inverse_log_ordered hy hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
  · have h := inverse_log_ordered hx (le_of_not_ge hxy)
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy)), abs_sub_comm]
    exact h.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))

/-- The stationary-model substitution has the required small residual. -/
theorem inverse_log_model_residual {T : ℝ} (hT : 2 ≤ T) :
    |((T + Real.log T + 1) - Real.log (T + Real.log T + 1)) - (T + 1)| ≤
      (Real.log T + 1) / T := by
  have hTp : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hD : T ≤ T + Real.log T + 1 := by linarith
  have hdiff : 0 ≤ Real.log (T + Real.log T + 1) - Real.log T :=
    sub_nonneg.mpr (Real.log_le_log hTp hD)
  have heq : ((T + Real.log T + 1) - Real.log (T + Real.log T + 1)) - (T + 1) =
      -(Real.log (T + Real.log T + 1) - Real.log T) := by ring
  rw [heq, abs_neg, abs_of_nonneg hdiff]
  convert log_increment_le (hTp.trans_le hD) hTp using 1
  ring

/-- A finite, explicit error bound for entropy inversion. -/
theorem entropy_inversion_error_bound {T d ε : ℝ} (hT : 2 ≤ T) (hd : 2 ≤ d)
    (hr : |(d - Real.log d) - (T + 1)| ≤ ε) :
    |d - (T + Real.log T + 1)| ≤ 2 * (ε + (Real.log T + 1) / T) := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hi := inverse_log_abs_bound hd (show 2 ≤ T + Real.log T + 1 by linarith)
  have ht := abs_sub_le (d - Real.log d) (T + 1)
    ((T + Real.log T + 1) - Real.log (T + Real.log T + 1))
  rw [abs_sub_comm (T + 1)] at ht
  have hm := inverse_log_model_residual hT
  linarith only [hi, ht, hr, hm]

/-- From d-log d=T+1+O(1/T), recover d=T+log T+1+O(log T/T), along an actual filter. -/
theorem entropy_inversion_isBigO (d : ℝ → ℝ)
    (hd : ∀ᶠ T in atTop, 2 ≤ d T)
    (hr : (fun T : ℝ => (d T - Real.log (d T)) - (T + 1)) =O[atTop] (fun T => 1 / T)) :
    (fun T : ℝ => d T - (T + Real.log T + 1)) =O[atTop]
      (fun T => Real.log T / T) := by
  obtain ⟨C, hC, hr⟩ := Asymptotics.isBigO_iff'.mp hr
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * (C + 2), ?_⟩
  filter_upwards [hd, hr, eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (Real.exp 1)] with T hd hr hT hTe
  have hTp : 0 < T := by linarith
  have hlog : 1 ≤ Real.log T := by
    have hh := Real.log_le_log (Real.exp_pos 1) hTe
    simpa only [Real.log_exp] using hh
  have hlogp : 0 < Real.log T := by linarith
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 1) hTp)] at hr
  have hb := entropy_inversion_error_bound hT hd hr
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos hlogp hTp)]
  apply hb.trans
  have hnum : C + (Real.log T + 1) ≤ (C + 2) * Real.log T := by
    nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hlog), hlog]
  have hdiv := (div_le_div_iff_of_pos_right hTp).mpr hnum
  convert mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

end EntropyConstrainedMissingMass
