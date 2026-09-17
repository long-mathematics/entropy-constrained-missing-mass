import EntropyConstrainedMissingMass.SimplexLaw
import EntropyConstrainedMissingMass.MixtureMoments

/-! The reciprocal-square tilted simplex law and its exact moments. -/

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter

namespace EntropyConstrainedMissingMass.Curvature

private theorem integrable_inverse_cube_prod {a b : ℝ} (μ : Measure (Icc a b))
    [IsProbabilityMeasure μ] (ha : 0 < a) :
    Integrable (fun p : ℝ × Icc a b => 1 / (p.1 + (p.2 : ℝ)) ^ 3)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  have hm : Measurable (fun p : ℝ × Icc a b => 1 / (p.1 + (p.2 : ℝ)) ^ 3) := by fun_prop
  refine ((integrableOn_inv_add_pow a ha 1).comp_fst μ).mono' hm.aestronglyMeasurable ?_
  have hs : ∀ᵐ p : ℝ × Icc a b ∂((volume.restrict (Ioi (0 : ℝ))).prod μ), 0 < p.1 := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Eventually.of_forall (fun _ => hs)
  filter_upwards [hs] with p hp
  have hv : 0 < (p.2 : ℝ) := lt_of_lt_of_le ha p.2.property.1
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (p.1 + (p.2 : ℝ)) ^ 3)]
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  linarith [p.2.property.1]

private theorem integrable_first_inverse_cube_prod {a b : ℝ} (μ : Measure (Icc a b))
    [IsProbabilityMeasure μ] (ha : 0 < a) :
    Integrable (fun p : ℝ × Icc a b => p.1 / (p.1 + (p.2 : ℝ)) ^ 3)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  have hm : Measurable (fun p : ℝ × Icc a b => p.1 / (p.1 + (p.2 : ℝ)) ^ 3) := by fun_prop
  refine ((integrableOn_uniform_first_moment a ha).comp_fst μ).mono' hm.aestronglyMeasurable ?_
  have hs : ∀ᵐ p : ℝ × Icc a b ∂((volume.restrict (Ioi (0 : ℝ))).prod μ), 0 < p.1 := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Eventually.of_forall (fun _ => hs)
  filter_upwards [hs] with p hp
  have hv : 0 < (p.2 : ℝ) := lt_of_lt_of_le ha p.2.property.1
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < p.1 / (p.1 + (p.2 : ℝ)) ^ 3)]
  apply div_le_div_of_nonneg_left (le_of_lt hp) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  linarith [p.2.property.1]

/-- Fubini identifies the reciprocal-square moment with twice I0. -/
theorem simplexLaw_inverse_square (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ v : ScaleInterval x y z, 1 / (v : ℝ) ^ 2 ∂simplexLaw x y z) = 2 * I0 x y z := by
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hprod := integrable_inverse_cube_prod (simplexLaw x y z) hlo
  have heq : I0 x y z = ∫ s in Ioi (0 : ℝ),
      ∫ v : ScaleInterval x y z, 1 / (s + (v : ℝ)) ^ 3 ∂simplexLaw x y z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    exact (simplexLaw_inverse_cube x y z s hx hy hz (le_of_lt hs)).symm
  rw [integral_integral_swap (f := fun s (v : ScaleInterval x y z) =>
    1 / (s + (v : ℝ)) ^ 3) hprod] at heq
  have hiEq : (∫ v : ScaleInterval x y z,
      (∫ s in Ioi (0 : ℝ), 1 / (s + (v : ℝ)) ^ 3) ∂simplexLaw x y z) =
      (1 / 2 : ℝ) * ∫ v : ScaleInterval x y z, 1 / (v : ℝ) ^ 2 ∂simplexLaw x y z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall (fun v => ?_)
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    dsimp only
    rw [integral_inv_add_pow v hv 1]
    norm_num
    ring
  rw [hiEq] at heq
  linarith

/-- Fubini identifies the reciprocal first moment with twice I1. -/
theorem simplexLaw_inverse (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ v : ScaleInterval x y z, 1 / (v : ℝ) ∂simplexLaw x y z) = 2 * I1 x y z := by
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hprod := integrable_first_inverse_cube_prod (simplexLaw x y z) hlo
  have heq : I1 x y z = ∫ s in Ioi (0 : ℝ),
      ∫ v : ScaleInterval x y z, s / (s + (v : ℝ)) ^ 3 ∂simplexLaw x y z := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    have hfun : (fun v : ScaleInterval x y z => s / (s + (v : ℝ)) ^ 3) =
        (fun v : ScaleInterval x y z => s * (1 / (s + (v : ℝ)) ^ 3)) := by funext v; ring
    rw [hfun, integral_const_mul, simplexLaw_inverse_cube x y z s hx hy hz (le_of_lt hs)]
    ring
  rw [integral_integral_swap (f := fun s (v : ScaleInterval x y z) =>
    s / (s + (v : ℝ)) ^ 3) hprod] at heq
  have hiEq : (∫ v : ScaleInterval x y z,
      (∫ s in Ioi (0 : ℝ), s / (s + (v : ℝ)) ^ 3) ∂simplexLaw x y z) =
      (1 / 2 : ℝ) * ∫ v : ScaleInterval x y z, 1 / (v : ℝ) ∂simplexLaw x y z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine Eventually.of_forall (fun v => ?_)
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    have h := I1_uniform v hv
    unfold I1 at h
    simp_rw [D_uniform] at h
    dsimp only
    rw [h]
    ring
  rw [hiEq] at heq
  linarith

/-- Reciprocal-square tilting of the genuine simplex scale distribution. -/
noncomputable def tiltedSimplexLaw (x y z : ℝ) : Measure (ScaleInterval x y z) :=
  (simplexLaw x y z).withDensity (fun v => ENNReal.ofReal (1 / (2 * I0 x y z * (v : ℝ) ^ 2)))

/-- Integral formula for the actual tilted measure. -/
theorem integral_tiltedSimplexLaw (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (f : ScaleInterval x y z → ℝ) :
    (∫ v, f v ∂tiltedSimplexLaw x y z) =
      ∫ v : ScaleInterval x y z, (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * f v ∂simplexLaw x y z := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold tiltedSimplexLaw
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    refine Eventually.of_forall (fun v => ?_)
    dsimp only
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  · fun_prop
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- The normalizing constant is exactly 2 I0, so the tilted law is a probability law. -/
theorem tiltedSimplexLaw_probability (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IsProbabilityMeasure (tiltedSimplexLaw x y z) := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hcont : Continuous (fun v : ScaleInterval x y z => 1 / (2 * I0 x y z * (v : ℝ) ^ 2)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    positivity
  have hint : Integrable (fun v : ScaleInterval x y z => 1 / (2 * I0 x y z * (v : ℝ) ^ 2))
      (simplexLaw x y z) := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm : (∫ v : ScaleInterval x y z, 1 / (2 * I0 x y z * (v : ℝ) ^ 2) ∂simplexLaw x y z) = 1 := by
    have heq : (fun v : ScaleInterval x y z => 1 / (2 * I0 x y z * (v : ℝ) ^ 2)) =
        (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z)) * (1 / (v : ℝ) ^ 2)) := by
      funext v
      simp only [one_div, mul_inv_rev]
      ring
    rw [heq, integral_const_mul, simplexLaw_inverse_square x y z hx hy hz]
    field_simp
  constructor
  unfold tiltedSimplexLaw
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun v => by
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    positivity)), hnorm]
  norm_num

/-- The tilted law's mean is precisely the geometric parameter m. -/
theorem tiltedSimplexLaw_mean (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    mixtureMean (tiltedSimplexLaw x y z) = m x y z := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold mixtureMean
  rw [integral_tiltedSimplexLaw x y z hx hy hz]
  have heq : (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * (v : ℝ)) =
      (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z)) * (1 / (v : ℝ))) := by
    funext v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    field_simp
  rw [heq, integral_const_mul, simplexLaw_inverse x y z hx hy hz]
  unfold m
  field_simp

/-- The second moment after tilting is 1/(2I0). -/
theorem tiltedSimplexLaw_second_moment (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    mixtureMoment (tiltedSimplexLaw x y z) 2 = 1 / (2 * I0 x y z) := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold mixtureMoment
  rw [integral_tiltedSimplexLaw x y z hx hy hz]
  have heq : (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * (v : ℝ) ^ 2) =
      (fun _ : ScaleInterval x y z => 1 / (2 * I0 x y z)) := by
    funext v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    field_simp
  rw [heq]
  simp

/-- The third moment after tilting retains the original simplex mean. -/
theorem tiltedSimplexLaw_third_moment (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    mixtureMoment (tiltedSimplexLaw x y z) 3 = ((x + y + z) / 3) / (2 * I0 x y z) := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold mixtureMoment
  rw [integral_tiltedSimplexLaw x y z hx hy hz]
  have heq : (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * (v : ℝ) ^ 3) =
      (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z)) * (v : ℝ)) := by
    funext v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    field_simp
  rw [heq, integral_const_mul]
  change (1 / (2 * I0 x y z)) * mixtureMean (simplexLaw x y z) = _
  rw [simplexLaw_mean]
  ring

/-- The mixture density of the tilted law is the normalized cubic reciprocal. -/
theorem tiltedSimplexLaw_density (x y z s : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : 0 ≤ s) :
    mixtureDensity (tiltedSimplexLaw x y z) s = 1 / (I0 x y z * D x y z s) := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  unfold mixtureDensity
  rw [integral_tiltedSimplexLaw x y z hx hy hz]
  have heq : (fun v : ScaleInterval x y z => (1 / (2 * I0 x y z * (v : ℝ) ^ 2)) * kernel v s) =
      (fun v : ScaleInterval x y z => (1 / I0 x y z) * (1 / (s + (v : ℝ)) ^ 3)) := by
    funext v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    unfold kernel
    field_simp
  rw [heq, integral_const_mul, simplexLaw_inverse_cube x y z s hx hy hz hs]
  simp only [one_div, mul_inv_rev]
  ring

/-- The original and tilted laws have the same almost-everywhere null sets
in the direction needed to preserve nondegeneracy. -/
theorem simplexLaw_absolutelyContinuous_tilted (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    simplexLaw x y z ≪ tiltedSimplexLaw x y z := by
  have hi := I0_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · refine Eventually.of_forall (fun v => ?_)
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

/-- A nonuniform triple gives a genuinely nonconstant scale distribution. -/
theorem simplexLaw_not_ae_constant (x y z : ℝ) (hn : ¬ (x = y ∧ y = z)) (c : ℝ) :
    ¬ ((fun v : ScaleInterval x y z => (v : ℝ)) =ᵐ[simplexLaw x y z] (fun _ => c)) := by
  intro heq
  have h1 := integral_congr_ae heq
  have h2 := integral_congr_ae (heq.fun_comp (fun v : ℝ => v ^ 2))
  change mixtureMean (simplexLaw x y z) = _ at h1
  rw [simplexLaw_mean] at h1
  simp only [integral_const, probReal_univ, one_smul] at h1
  change (∫ v : ScaleInterval x y z, (v : ℝ) ^ 2 ∂simplexLaw x y z) =
    ∫ _ : ScaleInterval x y z, c ^ 2 ∂simplexLaw x y z at h2
  rw [simplexLaw_second_moment] at h2
  simp only [integral_const, probReal_univ, one_smul] at h2
  rw [← h1] at h2
  have hxy : (x - y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (z - x)]
  have hyz : (y - z) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (z - x)]
  exact hn ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hxy), sub_eq_zero.mp (sq_eq_zero_iff.mp hyz)⟩

/-- Strictly positive weighted variance for the tilted nonuniform simplex law. -/
theorem tiltedSimplexLaw_weighted_variance_pos (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hn : ¬ (x = y ∧ y = z)) :
    0 < ∫ v : ScaleInterval x y z, ((v : ℝ) - m x y z) ^ 2 * ((v : ℝ) + m x y z)
      ∂tiltedSimplexLaw x y z := by
  let := tiltedSimplexLaw_probability x y z hx hy hz
  have hm := m_pos x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hnonneg : ∀ v : ScaleInterval x y z,
      0 ≤ ((v : ℝ) - m x y z) ^ 2 * ((v : ℝ) + m x y z) := by
    intro v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    positivity
  have hi : Integrable (fun v : ScaleInterval x y z =>
      ((v : ℝ) - m x y z) ^ 2 * ((v : ℝ) + m x y z)) (tiltedSimplexLaw x y z) :=
    (by fun_prop : Continuous (fun v : ScaleInterval x y z =>
      ((v : ℝ) - m x y z) ^ 2 * ((v : ℝ) + m x y z))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hge : 0 ≤ ∫ v : ScaleInterval x y z,
      ((v : ℝ) - m x y z) ^ 2 * ((v : ℝ) + m x y z) ∂tiltedSimplexLaw x y z :=
    integral_nonneg hnonneg
  apply lt_of_le_of_ne hge
  intro hzero
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hzero.symm
  have hconst : (fun v : ScaleInterval x y z => (v : ℝ)) =ᵐ[tiltedSimplexLaw x y z]
      (fun _ => m x y z) := by
    filter_upwards [hae] with v hv
    have hvp : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    have hsum : (v : ℝ) + m x y z ≠ 0 := by positivity
    have hsq : ((v : ℝ) - m x y z) ^ 2 = 0 := (mul_eq_zero.mp hv).resolve_right hsum
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  exact simplexLaw_not_ae_constant x y z hn (m x y z)
    ((simplexLaw_absolutelyContinuous_tilted x y z hx hy hz).ae_le hconst)

/-- The mean inequality is strict for every nonuniform positive triple. -/
theorem m_lt_mean_of_nonuniform (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hn : ¬ (x = y ∧ y = z)) : m x y z < (x + y + z) / 3 := by
  let := tiltedSimplexLaw_probability x y z hx hy hz
  have hpos := tiltedSimplexLaw_weighted_variance_pos x y z hx hy hz hn
  have heq := mixture_weighted_variance_eq (tiltedSimplexLaw x y z)
  rw [tiltedSimplexLaw_mean x y z hx hy hz, tiltedSimplexLaw_second_moment x y z hx hy hz,
    tiltedSimplexLaw_third_moment x y z hx hy hz] at heq
  rw [heq] at hpos
  have hi := I0_pos x y z hx hy hz
  have hnum : ((x + y + z) / 3) / (2 * I0 x y z) -
      m x y z * (1 / (2 * I0 x y z)) = ((x + y + z) / 3 - m x y z) / (2 * I0 x y z) := by ring
  rw [hnum] at hpos
  have hnumpos := (lt_div_iff₀ (by positivity : 0 < 2 * I0 x y z)).mp hpos
  exact sub_pos.mp (by simpa using hnumpos)

end EntropyConstrainedMissingMass.Curvature
