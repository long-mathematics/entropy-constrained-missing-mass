import EntropyConstrainedMissingMass.MixtureCurvature

/-! Centered moments and the weighted Cauchy–Schwarz step for compact positive laws. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set

namespace EntropyConstrainedMissingMass.Curvature
noncomputable section
variable {a b : ℝ} (μ : Measure (Icc a b)) [IsProbabilityMeasure μ]

def mixtureMoment (n : ℕ) : ℝ := ∫ v : Icc a b, (v : ℝ) ^ n ∂μ

private theorem integrable_parameter {f : Icc a b → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem integrable_mixtureMoment (n : ℕ) : Integrable (fun v : Icc a b => (v : ℝ) ^ n) μ :=
  integrable_parameter μ (by fun_prop)

@[simp] theorem mixtureMoment_zero : mixtureMoment μ 0 = 1 := by simp [mixtureMoment]
omit [IsProbabilityMeasure μ] in
@[simp] theorem mixtureMoment_one : mixtureMoment μ 1 = mixtureMean μ := by
  simp [mixtureMoment, mixtureMean]

/-- The variance is exactly the second moment minus the squared mean. -/
theorem mixture_variance_eq :
    (∫ v : Icc a b, ((v : ℝ) - mixtureMean μ) ^ 2 ∂μ) =
      mixtureMoment μ 2 - (mixtureMean μ) ^ 2 := by
  let c := mixtureMean μ
  have hi1 := integrable_mixtureMoment μ 1
  simp only [pow_one] at hi1
  have hi2 := integrable_mixtureMoment μ 2
  have heq : (fun v : Icc a b => ((v : ℝ) - c) ^ 2) =
      fun v : Icc a b => (v : ℝ) ^ 2 - (2 * c) * (v : ℝ) + c ^ 2 := by funext v; ring
  have hiSub : Integrable (fun v : Icc a b => (v : ℝ) ^ 2 - (2 * c) * (v : ℝ)) μ :=
    hi2.sub (hi1.const_mul (2 * c))
  rw [heq, integral_add hiSub (integrable_const _),
    integral_sub hi2 (hi1.const_mul (2 * c)), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change mixtureMoment μ 2 - 2 * c * c + c ^ 2 = mixtureMoment μ 2 - c ^ 2
  ring

/-- The weighted centered moment simplifies because c is the actual mean. -/
theorem mixture_weighted_variance_eq :
    (∫ v : Icc a b, ((v : ℝ) - mixtureMean μ) ^ 2 * ((v : ℝ) + mixtureMean μ) ∂μ) =
      mixtureMoment μ 3 - mixtureMean μ * mixtureMoment μ 2 := by
  let c := mixtureMean μ
  have hi1 := integrable_mixtureMoment μ 1
  simp only [pow_one] at hi1
  have hi2 := integrable_mixtureMoment μ 2
  have hi3 := integrable_mixtureMoment μ 3
  have heq : (fun v : Icc a b => ((v : ℝ) - c) ^ 2 * ((v : ℝ) + c)) =
      fun v : Icc a b => (v : ℝ) ^ 3 - c * (v : ℝ) ^ 2 - c ^ 2 * (v : ℝ) + c ^ 3 := by
    funext v; ring
  have hiSub : Integrable (fun v : Icc a b => (v : ℝ) ^ 3 - c * (v : ℝ) ^ 2) μ :=
    hi3.sub (hi2.const_mul c)
  have hiSub2 : Integrable (fun v : Icc a b => (v : ℝ) ^ 3 - c * (v : ℝ) ^ 2 - c ^ 2 * (v : ℝ)) μ :=
    hiSub.sub (hi1.const_mul (c ^ 2))
  rw [heq, integral_add hiSub2
      (integrable_const _), integral_sub hiSub (hi1.const_mul (c ^ 2)),
    integral_sub hi3 (hi2.const_mul c), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  change mixtureMoment μ 3 - c * mixtureMoment μ 2 - c ^ 2 * c + c ^ 3 =
    mixtureMoment μ 3 - c * mixtureMoment μ 2
  ring

/-- Cauchy–Schwarz written as an integrated nonnegative square, avoiding square-root choices. -/
theorem mixture_dispersion_lower (ha : 0 < a)
    (hden : 0 < mixtureMoment μ 3 - mixtureMean μ * mixtureMoment μ 2) :
    (mixtureMoment μ 2 - (mixtureMean μ) ^ 2) ^ 2 /
      (mixtureMoment μ 3 - mixtureMean μ * mixtureMoment μ 2) ≤ mixtureDispersion μ := by
  let c := mixtureMean μ
  let A := mixtureMoment μ 2 - c ^ 2
  let B := mixtureMoment μ 3 - c * mixtureMoment μ 2
  let k := A / B
  have hc : 0 < c := mixtureMean_pos μ ha
  have hiA : Integrable (fun v : Icc a b => ((v : ℝ) - c) ^ 2) μ :=
    integrable_parameter μ (by fun_prop)
  have hiB : Integrable (fun v : Icc a b => ((v : ℝ) - c) ^ 2 * ((v : ℝ) + c)) μ :=
    integrable_parameter μ (by fun_prop)
  have hiD : Integrable (fun v : Icc a b => ((v : ℝ) - c) ^ 2 / ((v : ℝ) + c)) μ := by
    apply integrable_parameter μ
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro v
    have hv : 0 < (v : ℝ) := ha.trans_le v.property.1
    positivity
  have hpoint (v : Icc a b) :
      (2 * k) * ((v : ℝ) - c) ^ 2 - k ^ 2 * (((v : ℝ) - c) ^ 2 * ((v : ℝ) + c)) ≤
        ((v : ℝ) - c) ^ 2 / ((v : ℝ) + c) := by
    have hv : 0 < (v : ℝ) := ha.trans_le v.property.1
    have hd : 0 < (v : ℝ) + c := add_pos hv hc
    apply (le_div_iff₀ hd).mpr
    have hs := mul_nonneg (sq_nonneg ((v : ℝ) - c)) (sq_nonneg (1 - k * ((v : ℝ) + c)))
    nlinarith
  have h := integral_mono ((hiA.const_mul (2 * k)).sub (hiB.const_mul (k ^ 2))) hiD hpoint
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hiA.const_mul (2 * k)) (hiB.const_mul (k ^ 2)),
    integral_const_mul, integral_const_mul, mixture_variance_eq, mixture_weighted_variance_eq] at h
  change 2 * k * A - k ^ 2 * B ≤ mixtureDispersion μ at h
  have hB : B ≠ 0 := ne_of_gt hden
  have heq : 2 * k * A - k ^ 2 * B = A ^ 2 / B := by dsimp [k]; field_simp; ring
  rw [heq] at h
  exact h

/-- The third-moment identity supplied by the tilted simplex gives the manuscript denominator. -/
theorem mixture_dispersion_lower_of_third_moment (ha : 0 < a) (S : ℝ)
    (hm : mixtureMean μ < S / 3) (h2 : 0 < mixtureMoment μ 2)
    (h3 : mixtureMoment μ 3 = (S / 3) * mixtureMoment μ 2) :
    (mixtureMoment μ 2 - (mixtureMean μ) ^ 2) ^ 2 /
      ((S / 3 - mixtureMean μ) * mixtureMoment μ 2) ≤ mixtureDispersion μ := by
  have heq : mixtureMoment μ 3 - mixtureMean μ * mixtureMoment μ 2 =
      (S / 3 - mixtureMean μ) * mixtureMoment μ 2 := by rw [h3]; ring
  have hden : 0 < mixtureMoment μ 3 - mixtureMean μ * mixtureMoment μ 2 := by
    rw [heq]
    exact mul_pos (sub_pos.mpr hm) h2
  simpa only [heq] using mixture_dispersion_lower μ ha hden

end
end EntropyConstrainedMissingMass.Curvature
