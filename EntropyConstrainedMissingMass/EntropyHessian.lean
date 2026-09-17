import EntropyConstrainedMissingMass.TripleGeometry
import EntropyConstrainedMissingMass.KernelEstimate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Entropy in the actual local symmetric coordinates for three distinct positive roots. -/

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.TripleGeometry

/-- Entropy of the three selected atoms; their total mass need not be one. -/
noncomputable def tripleEntropy (x : Triple) : ℝ := ∑ i : Fin 3, Real.negMulLog (x i)

/-- Entropy in the smooth symmetric-coordinate chart. -/
noncomputable def localEntropy (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (c : Triple) : ℝ :=
  tripleEntropy (localRoots x h01 h12 c)

private theorem triple_pos (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (i : Fin 3) : 0 < x i := by
  fin_cases i
  · exact h0
  · exact h0.trans h01
  · exact (h0.trans h01).trans h12

theorem sum_inv_rootDenom (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    (∑ i : Fin 3, 1 / rootDenom x i) = 0 := by
  have h02 := h01.trans h12
  simp [Fin.sum_univ_succ, rootDenom]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h12.ne,
    sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm, sub_ne_zero.mpr h12.ne.symm]
  ring

theorem sum_root_div_rootDenom (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    (∑ i : Fin 3, x i / rootDenom x i) = 0 := by
  have h02 := h01.trans h12
  simp [Fin.sum_univ_succ, rootDenom]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h12.ne,
    sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm, sub_ne_zero.mpr h12.ne.symm]
  ring

/-- The convergent logarithmic representation integrated against arbitrary finite weights. -/
theorem integral_weighted_log (x b : Triple) (hx : ∀ i, 0 < x i) :
    (∫ s in Ioi (0 : ℝ), ∑ i : Fin 3, b i * (1 / (s + 1) - 1 / (s + x i))) =
      ∑ i : Fin 3, b i * Real.log (x i) := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, (Curvature.integral_reciprocal_difference (x i) (hx i)).2]
  · intro i _
    exact (Curvature.integral_reciprocal_difference (x i) (hx i)).1.const_mul (b i)

/-- Exact logarithmic evaluation of the first reciprocal-cubic integral. -/
theorem I0_eq_log_sum (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    Curvature.I0 (x 0) (x 1) (x 2) = ∑ i : Fin 3, (-1 / rootDenom x i) * Real.log (x i) := by
  rw [← integral_weighted_log x (fun i => -1 / rootDenom x i) (triple_pos x h0 h01 h12)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hz : ∀ i, s + x i ≠ 0 := fun i => ne_of_gt (add_pos hs (triple_pos x h0 h01 h12 i))
  have hpart := partial_fractions_one x h01 h12 s hz
  have hsum := sum_inv_rootDenom x h01 h12
  have heq : (∑ i : Fin 3, (-1 / rootDenom x i) * (1 / (s + 1) - 1 / (s + x i))) =
      -(∑ i : Fin 3, 1 / rootDenom x i) * (1 / (s + 1)) +
        ∑ i : Fin 3, 1 / ((s + x i) * rootDenom x i) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  rw [heq, hsum, neg_zero, zero_mul, zero_add, hpart]
  rfl

/-- Exact logarithmic evaluation of the first-moment reciprocal-cubic integral. -/
theorem I1_eq_log_sum (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    Curvature.I1 (x 0) (x 1) (x 2) = ∑ i : Fin 3, (x i / rootDenom x i) * Real.log (x i) := by
  rw [← integral_weighted_log x (fun i => x i / rootDenom x i) (triple_pos x h0 h01 h12)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hz : ∀ i, s + x i ≠ 0 := fun i => ne_of_gt (add_pos hs (triple_pos x h0 h01 h12 i))
  have hpart := partial_fractions_root x h01 h12 s hz
  have hsum := sum_root_div_rootDenom x h01 h12
  have heq : (∑ i : Fin 3, (x i / rootDenom x i) * (1 / (s + 1) - 1 / (s + x i))) =
      (∑ i : Fin 3, x i / rootDenom x i) * (1 / (s + 1)) -
        ∑ i : Fin 3, x i / ((s + x i) * rootDenom x i) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  rw [heq, hsum, zero_mul, zero_sub, hpart]
  dsimp [Curvature.D]
  ring

/-- Actual first derivative of the local entropy in the `E` direction. -/
theorem hasDerivAt_localEntropy_E (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => localEntropy x h01 h12 (symmetricMap x + r • ![0, 1, 0]))
      (Curvature.I1 (x 0) (x 1) (x 2)) 0 := by
  have hd : ∀ i : Fin 3, HasDerivAt
      (fun r : ℝ => Real.negMulLog (localRoots x h01 h12 (symmetricMap x + r • ![0, 1, 0]) i))
      ((-Real.log (x i) - 1) * (-(x i) / rootDenom x i)) 0 := by
    intro i
    have h := Real.hasDerivAt_negMulLog (ne_of_gt (triple_pos x h0 h01 h12 i))
    have h' : HasDerivAt Real.negMulLog (-Real.log (x i) - 1)
        (localRoots x h01 h12 (symmetricMap x + (0 : ℝ) • ![0, 1, 0]) i) := by simpa using h
    exact h'.comp 0 (hasDerivAt_localRoots_E x h01 h12 i)
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i) using 1
  · rfl
  · rw [I1_eq_log_sum x h0 h01 h12]
    have hs := sum_root_div_rootDenom x h01 h12
    calc
      (∑ i : Fin 3, (x i / rootDenom x i) * Real.log (x i)) =
          (∑ i : Fin 3, (x i / rootDenom x i) * Real.log (x i)) + ∑ i : Fin 3, x i / rootDenom x i := by rw [hs, add_zero]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Actual first derivative of the local entropy in the `P` direction. -/
theorem hasDerivAt_localEntropy_P (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => localEntropy x h01 h12 (symmetricMap x + r • ![0, 0, 1]))
      (Curvature.I0 (x 0) (x 1) (x 2)) 0 := by
  have hd : ∀ i : Fin 3, HasDerivAt
      (fun r : ℝ => Real.negMulLog (localRoots x h01 h12 (symmetricMap x + r • ![0, 0, 1]) i))
      ((-Real.log (x i) - 1) * (1 / rootDenom x i)) 0 := by
    intro i
    have h := Real.hasDerivAt_negMulLog (ne_of_gt (triple_pos x h0 h01 h12 i))
    have h' : HasDerivAt Real.negMulLog (-Real.log (x i) - 1)
        (localRoots x h01 h12 (symmetricMap x + (0 : ℝ) • ![0, 0, 1]) i) := by simpa using h
    exact h'.comp 0 (hasDerivAt_localRoots_P x h01 h12 i)
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i) using 1
  · rfl
  · rw [I0_eq_log_sum x h0 h01 h12]
    have hs := sum_inv_rootDenom x h01 h12
    calc
      (∑ i : Fin 3, (-1 / rootDenom x i) * Real.log (x i)) =
          (∑ i : Fin 3, (-1 / rootDenom x i) * Real.log (x i)) - ∑ i : Fin 3, 1 / rootDenom x i := by rw [hs, sub_zero]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- A positive coefficient controls a two-sided parameter neighborhood of a denominator. -/
theorem denominator_perturb_lower {d v a r : ℝ} (_hd : 0 < d) (hv : 0 ≤ v)
    (hav : a * v ≤ d) (hr : -(a / 2) < r) : d / 2 ≤ d + r * v := by
  have hm := mul_le_mul_of_nonneg_right hr.le hv
  nlinarith

/-- Differentiation of a reciprocal integral with a uniform, integrable derivative majorant.
This is used with the positive cubic denominator and its `E` or `P` coefficient. -/
theorem hasDerivAt_reciprocal_integral_perturb
    (d n v : ℝ → ℝ) (hdm : Measurable d) (hnm : Measurable n) (hvm : Measurable v)
    (a : ℝ) (ha : 0 < a)
    (hpos : ∀ s ∈ Ioi (0 : ℝ), 0 < d s ∧ 0 ≤ n s ∧ 0 ≤ v s ∧ a * v s ≤ d s)
    (hi : IntegrableOn (fun s => n s / d s) (Ioi (0 : ℝ)))
    (hmajor : IntegrableOn (fun s => n s * v s / (d s) ^ 2) (Ioi (0 : ℝ))) :
    HasDerivAt (fun r : ℝ => ∫ s in Ioi (0 : ℝ), n s / (d s + r * v s))
      (-(∫ s in Ioi (0 : ℝ), n s * v s / (d s) ^ 2)) 0 := by
  let F : ℝ → ℝ → ℝ := fun r s => n s / (d s + r * v s)
  let F' : ℝ → ℝ → ℝ := fun r s => -(n s * v s) / (d s + r * v s) ^ 2
  have hnhds : Ioo (-(a / 2)) (a / 2) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by positivity)
  have hm : ∀ᶠ r in nhds (0 : ℝ), AEStronglyMeasurable (F r) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Filter.Eventually.of_forall
    intro r
    exact (hnm.div (hdm.add (measurable_const.mul hvm))).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (F' 0) (volume.restrict (Ioi (0 : ℝ))) := by
    exact ((hnm.mul hvm).neg.div ((hdm.add (measurable_const.mul hvm)).pow_const 2)).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioo (-(a / 2)) (a / 2),
      ‖F' r s‖ ≤ 4 * (n s * v s / (d s) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro r hr
    obtain ⟨hd, hn, hv, hav⟩ := hpos s hs
    have hl := denominator_perturb_lower hd hv hav hr.1
    have hp : 0 < d s + r * v s := lt_of_lt_of_le (half_pos hd) hl
    have hnum := mul_nonneg hn hv
    dsimp [F']
    rw [abs_div, abs_neg, abs_of_nonneg hnum, abs_of_pos (sq_pos_of_pos hp)]
    calc
      n s * v s / (d s + r * v s) ^ 2 ≤ n s * v s / (d s / 2) ^ 2 :=
        div_le_div_of_nonneg_left hnum (sq_pos_of_pos (half_pos hd))
          (pow_le_pow_left₀ (half_pos hd).le hl 2)
      _ = 4 * (n s * v s / (d s) ^ 2) := by ring
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioo (-(a / 2)) (a / 2),
      HasDerivAt (fun r => F r s) (F' r s) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro r hr
    obtain ⟨hd, _, hv, hav⟩ := hpos s hs
    have hp : 0 < d s + r * v s := lt_of_lt_of_le (half_pos hd)
      (denominator_perturb_lower hd hv hav hr.1)
    convert ((hasDerivAt_const r (n s)).div
      (((hasDerivAt_id r).mul_const (v s)).const_add (d s)) hp.ne') using 1 <;>
      simp [F, F']
    rfl
  have hbase : Integrable (F 0) (volume.restrict (Ioi (0 : ℝ))) := by simpa [F, IntegrableOn] using hi
  have hresult := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnhds hm hbase hm'
    hbound (hmajor.const_mul 4) hdiff).2
  simpa [F, F', neg_div, integral_neg] using hresult

theorem D_expand (x : Triple) (s : ℝ) :
    Curvature.D (x 0) (x 1) (x 2) s =
      s ^ 3 + symmetricMap x 0 * s ^ 2 + symmetricMap x 1 * s + symmetricMap x 2 := by
  dsimp [Curvature.D, symmetricMap]
  ring

private theorem symmetricCoefficients_pos (x : Triple) (hx : ∀ i, 0 < x i) :
    0 < symmetricMap x 0 ∧ 0 < symmetricMap x 1 ∧ 0 < symmetricMap x 2 := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  dsimp [symmetricMap]
  exact ⟨by positivity, by positivity, by positivity⟩

theorem D_ge_P (x : Triple) (hx : ∀ i, 0 < x i) {s : ℝ} (hs : 0 ≤ s) :
    symmetricMap x 2 ≤ Curvature.D (x 0) (x 1) (x 2) s := by
  obtain ⟨hS, hE, _⟩ := symmetricCoefficients_pos x hx
  rw [D_expand]
  have h1 : 0 ≤ s ^ 3 := pow_nonneg hs _
  have h2 : 0 ≤ symmetricMap x 0 * s ^ 2 := mul_nonneg hS.le (sq_nonneg _)
  have h3 : 0 ≤ symmetricMap x 1 * s := mul_nonneg hE.le hs
  linarith

theorem D_ge_E_mul (x : Triple) (hx : ∀ i, 0 < x i) {s : ℝ} (hs : 0 ≤ s) :
    symmetricMap x 1 * s ≤ Curvature.D (x 0) (x 1) (x 2) s := by
  obtain ⟨hS, _, hP⟩ := symmetricCoefficients_pos x hx
  rw [D_expand]
  have h1 : 0 ≤ s ^ 3 := pow_nonneg hs _
  have h2 : 0 ≤ symmetricMap x 0 * s ^ 2 := mul_nonneg hS.le (sq_nonneg _)
  linarith

/-- Integrability of the two lower-degree Hessian integrands. -/
theorem integrableOn_div_D_sq (x : Triple) (hx : ∀ i, 0 < x i) :
    IntegrableOn (fun s : ℝ => 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) (Ioi (0 : ℝ)) ∧
    IntegrableOn (fun s : ℝ => s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) (Ioi (0 : ℝ)) := by
  have hP := (symmetricCoefficients_pos x hx).2.2
  have h0 := Curvature.integrableOn_I0 (x 0) (x 1) (x 2) (hx 0) (hx 1) (hx 2)
  have h1 := Curvature.integrableOn_I1 (x 0) (x 1) (x 2) (hx 0) (hx 1) (hx 2)
  have hbound : ∀ s ∈ Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2 ≤
      (1 / symmetricMap x 2) * (1 / Curvature.D (x 0) (x 1) (x 2) s) := by
    intro s hs
    have hd := Curvature.D_pos (x 0) (x 1) (x 2) (hx 0) (hx 1) (hx 2) s hs.le
    have hle := D_ge_P x hx hs.le
    calc
      1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2 ≤
          1 / (symmetricMap x 2 * Curvature.D (x 0) (x 1) (x 2) s) := by
        apply one_div_le_one_div_of_le (mul_pos hP hd)
        nlinarith
      _ = _ := by ring
  constructor
  · refine (h0.const_mul (1 / symmetricMap x 2)).mono' (by apply Measurable.aestronglyMeasurable; unfold Curvature.D; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound s hs
  · refine (h1.const_mul (1 / symmetricMap x 2)).mono' (by apply Measurable.aestronglyMeasurable; unfold Curvature.D; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs.le (sq_nonneg _))]
    have ht := mul_le_mul_of_nonneg_left (hbound s hs) hs.le
    convert ht using 1 <;> ring

/-- Differentiating `I0` in the constant coefficient `P`, under the integral sign. -/
theorem hasDerivAt_integral_I0_P (x : Triple) (hx : ∀ i, 0 < x i) :
    HasDerivAt (fun r : ℝ => ∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s + r))
      (-(∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have ht := hasDerivAt_reciprocal_integral_perturb (Curvature.D (x 0) (x 1) (x 2)) (fun _ => 1) (fun _ => 1)
    (by unfold Curvature.D; fun_prop) measurable_const measurable_const
    (symmetricMap x 2) (symmetricCoefficients_pos x hx).2.2
    (by
      intro s hs
      refine ⟨Curvature.D_pos _ _ _ (hx 0) (hx 1) (hx 2) s hs.le, by norm_num, by norm_num, ?_⟩
      simpa using D_ge_P x hx hs.le)
    (Curvature.integrableOn_I0 _ _ _ (hx 0) (hx 1) (hx 2))
    (by simpa using (integrableOn_div_D_sq x hx).1)
  simpa using ht

/-- Differentiating `I0` in the coefficient `E`, under the integral sign. -/
theorem hasDerivAt_integral_I0_E (x : Triple) (hx : ∀ i, 0 < x i) :
    HasDerivAt (fun r : ℝ => ∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s + r * s))
      (-(∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have ht := hasDerivAt_reciprocal_integral_perturb (Curvature.D (x 0) (x 1) (x 2)) (fun _ => 1) id
    (by unfold Curvature.D; fun_prop) measurable_const measurable_id
    (symmetricMap x 1) (symmetricCoefficients_pos x hx).2.1
    (by
      intro s hs
      exact ⟨Curvature.D_pos _ _ _ (hx 0) (hx 1) (hx 2) s hs.le, by norm_num, hs.le, D_ge_E_mul x hx hs.le⟩)
    (Curvature.integrableOn_I0 _ _ _ (hx 0) (hx 1) (hx 2))
    (by simpa using (integrableOn_div_D_sq x hx).2)
  simpa using ht

/-- Differentiating `I1` in the coefficient `P`, under the integral sign. -/
theorem hasDerivAt_integral_I1_P (x : Triple) (hx : ∀ i, 0 < x i) :
    HasDerivAt (fun r : ℝ => ∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s + r))
      (-(∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have ht := hasDerivAt_reciprocal_integral_perturb (Curvature.D (x 0) (x 1) (x 2)) id (fun _ => 1)
    (by unfold Curvature.D; fun_prop) measurable_id measurable_const
    (symmetricMap x 2) (symmetricCoefficients_pos x hx).2.2
    (by
      intro s hs
      refine ⟨Curvature.D_pos _ _ _ (hx 0) (hx 1) (hx 2) s hs.le, hs.le, by norm_num, ?_⟩
      simpa using D_ge_P x hx hs.le)
    (Curvature.integrableOn_I1 _ _ _ (hx 0) (hx 1) (hx 2))
    (by simpa using (integrableOn_div_D_sq x hx).2)
  simpa using ht

/-- Differentiating `I1` in the coefficient `E`, under the integral sign. -/
theorem hasDerivAt_integral_I1_E (x : Triple) (hx : ∀ i, 0 < x i) :
    HasDerivAt (fun r : ℝ => ∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s + r * s))
      (-(∫ s in Ioi (0 : ℝ), s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have ht := hasDerivAt_reciprocal_integral_perturb (Curvature.D (x 0) (x 1) (x 2)) id id
    (by unfold Curvature.D; fun_prop) measurable_id measurable_id
    (symmetricMap x 1) (symmetricCoefficients_pos x hx).2.1
    (by
      intro s hs
      exact ⟨Curvature.D_pos _ _ _ (hx 0) (hx 1) (hx 2) s hs.le, hs.le, hs.le, D_ge_E_mul x hx hs.le⟩)
    (Curvature.integrableOn_I1 _ _ _ (hx 0) (hx 1) (hx 2))
    (by simpa [sq] using Curvature.integrableOn_curvature_numerator (x 0) (x 1) (x 2) 0 (hx 0) (hx 1) (hx 2))
  simpa [sq] using ht

/-- The open chart used by the inverse function theorem for the symmetric map. -/
noncomputable def symmetricChart (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    OpenPartialHomeomorph Triple Triple :=
  contDiff_symmetricMap.contDiffAt.toOpenPartialHomeomorph symmetricMap
    (hasFDerivAt_symmetricMap_equiv x h01 h12) (by simp)

@[simp] theorem symmetricChart_symm (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ((symmetricChart x h01 h12).symm : Triple → Triple) = localRoots x h01 h12 := rfl

theorem mem_symmetricChart_target (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    symmetricMap x ∈ (symmetricChart x h01 h12).target :=
  ContDiffAt.image_mem_toOpenPartialHomeomorph_target _ _ _

/-- Overlapping ordered-root inverse charts agree near each point in their overlap. -/
theorem localRoots_charts_eventuallyEq (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (c : Triple) (hc : c ∈ (symmetricChart x h01 h12).target)
    (hy01 : localRoots x h01 h12 c 0 < localRoots x h01 h12 c 1)
    (hy12 : localRoots x h01 h12 c 1 < localRoots x h01 h12 c 2) :
    localRoots x h01 h12 =ᶠ[nhds c] localRoots (localRoots x h01 h12 c) hy01 hy12 := by
  let y := localRoots x h01 h12 c
  have hsy : symmetricMap y = c := (symmetricChart x h01 h12).right_inv hc
  have ht : Tendsto (localRoots x h01 h12) (nhds c) (nhds y) :=
    (symmetricChart x h01 h12).continuousAt_symm hc
  have hleft := ht.eventually (eventually_localRoots_left_inverse y hy01 hy12)
  have htarget : ∀ᶠ d in nhds c, d ∈ (symmetricChart x h01 h12).target :=
    (symmetricChart x h01 h12).open_target.mem_nhds hc
  have hright : ∀ᶠ d in nhds c, symmetricMap (localRoots x h01 h12 d) = d :=
    htarget.mono (fun d hd => (symmetricChart x h01 h12).right_inv hd)
  filter_upwards [hleft, hright] with d hld hrd
  rw [hrd] at hld
  exact hld.symm

/-- The partial derivative in `E`, defined through an actual scalar derivative. -/
noncomputable def partialE (H : Triple → ℝ) (c : Triple) : ℝ :=
  deriv (fun r : ℝ => H (c + r • ![0, 1, 0])) 0

/-- The partial derivative in `P`, defined through an actual scalar derivative. -/
noncomputable def partialP (H : Triple → ℝ) (c : Triple) : ℝ :=
  deriv (fun r : ℝ => H (c + r • ![0, 0, 1])) 0

/-- The first entropy derivative identities hold on a full neighborhood of the base point. -/
theorem eventually_partialEntropy_integrals (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ c in nhds (symmetricMap x),
      partialE (localEntropy x h01 h12) c =
        Curvature.I1 (localRoots x h01 h12 c 0) (localRoots x h01 h12 c 1) (localRoots x h01 h12 c 2) ∧
      partialP (localEntropy x h01 h12) c =
        Curvature.I0 (localRoots x h01 h12 c 0) (localRoots x h01 h12 c 1) (localRoots x h01 h12 c 2) := by
  have ht := (symmetricChart x h01 h12).open_target.mem_nhds (mem_symmetricChart_target x h01 h12)
  filter_upwards [ht, eventually_localRoots_positive_ordered x h0 h01 h12] with c hc hord
  let y := localRoots x h01 h12 c
  have hsy : symmetricMap y = c := (symmetricChart x h01 h12).right_inv hc
  have heq := localRoots_charts_eventuallyEq x h01 h12 c hc hord.2.1 hord.2.2
  have hE : Tendsto (fun r : ℝ => c + r • ![(0 : ℝ), 1, 0]) (nhds 0) (nhds c) := by
    have hcont : Continuous (fun r : ℝ => c + r • (![(0 : ℝ), 1, 0] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto (0 : ℝ)
  have hP : Tendsto (fun r : ℝ => c + r • ![(0 : ℝ), 0, 1]) (nhds 0) (nhds c) := by
    have hcont : Continuous (fun r : ℝ => c + r • (![(0 : ℝ), 0, 1] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hcont.tendsto (0 : ℝ)
  constructor
  · have hd := hasDerivAt_localEntropy_E y hord.1 hord.2.1 hord.2.2
    rw [hsy] at hd
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [hE.eventually heq] with r hr
    exact congrArg tripleEntropy hr
  · have hd := hasDerivAt_localEntropy_P y hord.1 hord.2.1 hord.2.2
    rw [hsy] at hd
    apply HasDerivAt.deriv
    apply hd.congr_of_eventuallyEq
    filter_upwards [hP.eventually heq] with r hr
    exact congrArg tripleEntropy hr

/-- Reciprocal-cubic moments expressed directly in symmetric coordinates. -/
noncomputable def coefficientMoment (c : Triple) (k : ℕ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), s ^ k / (s ^ 3 + c 0 * s ^ 2 + c 1 * s + c 2)

theorem coefficientMoment_shift_E (x : Triple) (r : ℝ) (k : ℕ) :
    coefficientMoment (symmetricMap x + r • ![0, 1, 0]) k =
      ∫ s in Ioi (0 : ℝ), s ^ k / (Curvature.D (x 0) (x 1) (x 2) s + r * s) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp
  rw [D_expand]
  congr 1
  dsimp [symmetricMap]
  ring

theorem coefficientMoment_shift_P (x : Triple) (r : ℝ) (k : ℕ) :
    coefficientMoment (symmetricMap x + r • ![0, 0, 1]) k =
      ∫ s in Ioi (0 : ℝ), s ^ k / (Curvature.D (x 0) (x 1) (x 2) s + r) := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp
  rw [D_expand]
  congr 1
  dsimp [symmetricMap]
  ring

/-- The local first derivatives are reciprocal-cubic moment functions on a neighborhood. -/
theorem eventually_partialEntropy_coefficients (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ c in nhds (symmetricMap x),
      partialE (localEntropy x h01 h12) c = coefficientMoment c 1 ∧
      partialP (localEntropy x h01 h12) c = coefficientMoment c 0 := by
  filter_upwards [eventually_partialEntropy_integrals x h0 h01 h12,
    eventually_localRoots_right_inverse x h01 h12] with c hc hr
  have hd : ∀ s : ℝ, Curvature.D (localRoots x h01 h12 c 0) (localRoots x h01 h12 c 1)
      (localRoots x h01 h12 c 2) s = s ^ 3 + c 0 * s ^ 2 + c 1 * s + c 2 := by
    intro s
    rw [D_expand, hr]
  constructor
  · rw [hc.1]
    unfold Curvature.I1 coefficientMoment
    simp only [pow_one]
    simp_rw [hd]
  · rw [hc.2]
    unfold Curvature.I0 coefficientMoment
    simp only [pow_zero]
    simp_rw [hd]

/-- The entropy Hessian entry `H_EE`, as an actual derivative of the partial derivative. -/
theorem hasDerivAt_partialEntropy_EE (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => partialE (localEntropy x h01 h12) (symmetricMap x + r • ![0, 1, 0]))
      (-(∫ s in Ioi (0 : ℝ), s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  apply (hasDerivAt_integral_I1_E x (triple_pos x h0 h01 h12)).congr_of_eventuallyEq
  have ht : Tendsto (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 1, 0] : Triple))
      (nhds 0) (nhds (symmetricMap x)) := by
    have hc : Continuous (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 1, 0] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  filter_upwards [ht.eventually (eventually_partialEntropy_coefficients x h0 h01 h12)] with r hr
  rw [hr.1, coefficientMoment_shift_E]
  simp only [pow_one]

/-- The mixed entropy Hessian entry `H_EP`. -/
theorem hasDerivAt_partialEntropy_EP (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => partialE (localEntropy x h01 h12) (symmetricMap x + r • ![0, 0, 1]))
      (-(∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  apply (hasDerivAt_integral_I1_P x (triple_pos x h0 h01 h12)).congr_of_eventuallyEq
  have ht : Tendsto (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 0, 1] : Triple))
      (nhds 0) (nhds (symmetricMap x)) := by
    have hc : Continuous (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 0, 1] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  filter_upwards [ht.eventually (eventually_partialEntropy_coefficients x h0 h01 h12)] with r hr
  rw [hr.1, coefficientMoment_shift_P]
  simp only [pow_one]

/-- The mixed entropy Hessian entry `H_PE`, with the same convergent integral. -/
theorem hasDerivAt_partialEntropy_PE (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => partialP (localEntropy x h01 h12) (symmetricMap x + r • ![0, 1, 0]))
      (-(∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  apply (hasDerivAt_integral_I0_E x (triple_pos x h0 h01 h12)).congr_of_eventuallyEq
  have ht : Tendsto (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 1, 0] : Triple))
      (nhds 0) (nhds (symmetricMap x)) := by
    have hc : Continuous (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 1, 0] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  filter_upwards [ht.eventually (eventually_partialEntropy_coefficients x h0 h01 h12)] with r hr
  rw [hr.2, coefficientMoment_shift_E]
  simp only [pow_zero]

/-- The entropy Hessian entry `H_PP`. -/
theorem hasDerivAt_partialEntropy_PP (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => partialP (localEntropy x h01 h12) (symmetricMap x + r • ![0, 0, 1]))
      (-(∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  apply (hasDerivAt_integral_I0_P x (triple_pos x h0 h01 h12)).congr_of_eventuallyEq
  have ht : Tendsto (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 0, 1] : Triple))
      (nhds 0) (nhds (symmetricMap x)) := by
    have hc : Continuous (fun r : ℝ => symmetricMap x + r • (![(0 : ℝ), 0, 1] : Triple)) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  filter_upwards [ht.eventually (eventually_partialEntropy_coefficients x h0 h01 h12)] with r hr
  rw [hr.2, coefficientMoment_shift_P]
  simp only [pow_zero]

end EntropyConstrainedMissingMass.TripleGeometry
