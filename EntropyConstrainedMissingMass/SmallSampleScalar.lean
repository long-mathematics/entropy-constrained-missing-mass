import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Strict scalar inequalities in the exclusion of heavy candidates for t=1,2.
These inequalities do not assume or assert the constrained second-variation condition. -/

namespace EntropyConstrainedMissingMass

noncomputable def logRatioGap (r : ℝ) : ℝ := r - 1 / r - 2 * Real.log r

@[simp] theorem logRatioGap_one : logRatioGap 1 = 0 := by simp [logRatioGap]

theorem hasDerivAt_logRatioGap {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt logRatioGap ((r - 1) ^ 2 / r ^ 2) r := by
  have hd := ((hasDerivAt_id r).sub ((hasDerivAt_id r).inv hr)).sub
    ((Real.hasDerivAt_log hr).const_mul 2)
  convert hd using 1
  · funext x
    simp [logRatioGap, one_div]
  · dsimp only [id_eq]
    field_simp
    ring

theorem logRatioGap_pos {r : ℝ} (hr : 1 < r) : 0 < logRatioGap r := by
  have hc : ContinuousOn logRatioGap (Set.Ici 1) := by
    exact (continuousOn_id.sub (continuousOn_const.div continuousOn_id (fun x hx => by
      change 1 ≤ x at hx; change x ≠ 0; linarith))).sub
      ((continuousOn_id.log (fun x hx => by change 1 ≤ x at hx; change x ≠ 0; linarith)).const_mul 2)
  have hmono : StrictMonoOn logRatioGap (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1) hc
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : 1 < x := hx
    rw [(hasDerivAt_logRatioGap (by linarith : x ≠ 0)).deriv]
    exact div_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos (by linarith))
  simpa only [logRatioGap_one] using hmono (show 1 ∈ Set.Ici (1 : ℝ) by simp) hr.le hr

noncomputable def smallSampleNumerator (m r : ℝ) : ℝ :=
  (r - 1) * (4 * m + r - 3) - (4 * m + 4 * r - 6) * Real.log r

@[simp] theorem smallSampleNumerator_one (m : ℝ) : smallSampleNumerator m 1 = 0 := by
  simp [smallSampleNumerator]

theorem smallSampleNumerator_decompose (m r : ℝ) :
    smallSampleNumerator m r = smallSampleNumerator 2 r +
      4 * (m - 2) * (r - 1 - Real.log r) := by
  unfold smallSampleNumerator
  ring

theorem hasDerivAt_smallSampleNumerator_two {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (smallSampleNumerator 2) (2 * logRatioGap r) r := by
  have h₁ := ((hasDerivAt_id r).sub_const 1).mul
    ((hasDerivAt_const r (4 * (2 : ℝ))).add (hasDerivAt_id r) |>.sub_const 3)
  have h₂ := (((hasDerivAt_const r (4 * (2 : ℝ))).add
    ((hasDerivAt_id r).const_mul 4)).sub_const 6).mul (Real.hasDerivAt_log hr)
  convert h₁.sub h₂ using 1
  · rfl
  · dsimp only [logRatioGap, id_eq, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    field_simp
    ring

theorem smallSampleNumerator_two_pos {r : ℝ} (hr : 1 < r) :
    0 < smallSampleNumerator 2 r := by
  have hc : ContinuousOn (smallSampleNumerator 2) (Set.Ici 1) := by
    unfold smallSampleNumerator
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.mul
      · fun_prop
      · exact continuousOn_id.log (fun x hx => by change 1 ≤ x at hx; change x ≠ 0; linarith)
  have hmono : StrictMonoOn (smallSampleNumerator 2) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1) hc
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : 1 < x := hx
    rw [(hasDerivAt_smallSampleNumerator_two (by linarith : x ≠ 0)).deriv]
    exact mul_pos (by norm_num) (logRatioGap_pos hx1)
  simpa only [smallSampleNumerator_one] using hmono
    (show 1 ∈ Set.Ici (1 : ℝ) by simp) hr.le hr

theorem smallSampleNumerator_pos {m r : ℝ} (hm : 2 ≤ m) (hr : 1 < r) :
    0 < smallSampleNumerator m r := by
  rw [smallSampleNumerator_decompose]
  have hlog := Real.log_lt_sub_one_of_pos (by linarith : 0 < r) (by linarith : r ≠ 1)
  have hnonneg : 0 ≤ 4 * (m - 2) * (r - 1 - Real.log r) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hm)) (by linarith)
  exact add_pos_of_pos_of_nonneg (smallSampleNumerator_two_pos hr) hnonneg

theorem logarithmic_mean_ratio_gt_one {r : ℝ} (hr : 1 < r) :
    1 < (r - 1) / Real.log r := by
  apply (one_lt_div (Real.log_pos hr)).mpr
  exact Real.log_lt_sub_one_of_pos (by linarith) (by linarith)

end EntropyConstrainedMissingMass
