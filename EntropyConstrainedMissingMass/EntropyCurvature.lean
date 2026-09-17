import EntropyConstrainedMissingMass.SimplexTilt
import EntropyConstrainedMissingMass.CurvatureMeanBound
import EntropyConstrainedMissingMass.CurvatureAlgebra

/-!
# The sharp entropy-curvature inequality

The integrals are those of Appendix A.  The proof uses the actual uniform
simplex distribution, its reciprocal-square tilt, the sharp kernel estimate,
and the weighted moment inequality.  No analytic estimate is assumed.
-/

open MeasureTheory Set
namespace EntropyConstrainedMissingMass.Curvature

/-- The tilted mixture quadratic integral is the defining curvature, rescaled by I0. -/
theorem tiltedSimplexLaw_curvature (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    K x y z = I0 x y z * ∫ s in Ioi (0 : ℝ),
      (s - mixtureMean (tiltedSimplexLaw x y z)) ^ 2 *
        (mixtureDensity (tiltedSimplexLaw x y z) s) ^ 2 := by
  have hi := I0_pos x y z hx hy hz
  have heq : (∫ s in Ioi (0 : ℝ),
      (s - mixtureMean (tiltedSimplexLaw x y z)) ^ 2 *
        (mixtureDensity (tiltedSimplexLaw x y z) s) ^ 2) =
      (1 / I0 x y z ^ 2) * ∫ s in Ioi (0 : ℝ),
        (s - m x y z) ^ 2 / D x y z s ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [tiltedSimplexLaw_mean x y z hx hy hz,
      tiltedSimplexLaw_density x y z s hx hy hz (le_of_lt hs)]
    ring
  rw [heq]
  unfold K
  field_simp

/-- The quantitative lower bound before the final rational optimization in Appendix A. -/
theorem curvature_lower_of_nonuniform (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hn : ¬ (x = y ∧ y = z)) :
    (8 / 15 : ℝ) * I1 x y z +
      (1 - 2 * m x y z * I1 x y z) ^ 2 / (x + y + z - 3 * m x y z) ≤ K x y z := by
  let := tiltedSimplexLaw_probability x y z hx hy hz
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hi := I0_pos x y z hx hy hz
  have hm := m_lt_mean_of_nonuniform x y z hx hy hz hn
  have hmean := tiltedSimplexLaw_mean x y z hx hy hz
  have hsecond := tiltedSimplexLaw_second_moment x y z hx hy hz
  have hthird := tiltedSimplexLaw_third_moment x y z hx hy hz
  have h2 : 0 < mixtureMoment (tiltedSimplexLaw x y z) 2 := by rw [hsecond]; positivity
  have h3 : mixtureMoment (tiltedSimplexLaw x y z) 3 =
      ((x + y + z) / 3) * mixtureMoment (tiltedSimplexLaw x y z) 2 := by
    rw [hthird, hsecond]; ring
  have hdisp := mixture_dispersion_lower_of_third_moment (tiltedSimplexLaw x y z)
    hlo (x + y + z) (by simpa only [hmean] using hm) h2 h3
  rw [hmean, hsecond] at hdisp
  have hmix := mixture_curvature_bound (tiltedSimplexLaw x y z) hlo
  have hscaled := mul_le_mul_of_nonneg_left hmix (le_of_lt hi)
  rw [← tiltedSimplexLaw_curvature x y z hx hy hz, hmean] at hscaled
  have hdispScaled := mul_le_mul_of_nonneg_left hdisp (by positivity : 0 ≤ (2 / 3 : ℝ) * I0 x y z)
  have hden : x + y + z - 3 * m x y z ≠ 0 := ne_of_gt (by linarith)
  have hden' : (x + y + z) / 3 - m x y z ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  have hrel : I0 x y z * m x y z = I1 x y z := by
    unfold m
    field_simp
  have halg : (2 / 3 : ℝ) * I0 x y z *
      ((1 / (2 * I0 x y z) - m x y z ^ 2) ^ 2 /
        (((x + y + z) / 3 - m x y z) * (1 / (2 * I0 x y z)))) =
      (1 - 2 * m x y z * I1 x y z) ^ 2 / (x + y + z - 3 * m x y z) := by
    rw [← hrel]
    field_simp
  rw [halg] at hdispScaled
  nlinarith only [hscaled, hdispScaled, hrel]

/-- The sharp bound is strict for every nonuniform positive triple. -/
theorem entropy_curvature_strict (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hn : ¬ (x = y ∧ y = z)) :
    16 / (15 * (x + y + z + m x y z)) < K x y z :=
  entropy_curvature_strict_of_lower_bound (x + y + z) (m x y z) (I1 x y z) (K x y z)
    (by positivity) (m_pos x y z hx hy hz)
    (m_lt_mean_of_nonuniform x y z hx hy hz hn) (sum_mul_I1_ge x y z hx hy hz)
    (curvature_lower_of_nonuniform x y z hx hy hz hn)

/-- The simplex tilt gives the mean bound, including the uniform case. -/
theorem m_le_mean (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    m x y z ≤ (x + y + z) / 3 := by
  by_cases hn : x = y ∧ y = z
  · obtain ⟨hxy, hyz⟩ := hn
    subst x
    subst y
    rw [m_uniform z hz]
    linarith
  · exact le_of_lt (m_lt_mean_of_nonuniform x y z hx hy hz hn)

/-- Equality in the mean bound characterizes uniform triples. -/
theorem m_eq_mean_iff (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    m x y z = (x + y + z) / 3 ↔ x = y ∧ y = z := by
  constructor
  · intro heq
    by_contra hn
    exact (ne_of_lt (m_lt_mean_of_nonuniform x y z hx hy hz hn)) heq
  · rintro ⟨hxy, hyz⟩
    subst x
    subst y
    rw [m_uniform z hz]
    ring

/-- The sharp entropy-curvature inequality of the paper, for all positive triples. -/
theorem entropy_curvature_bound (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    16 / (15 * (x + y + z + m x y z)) ≤ K x y z := by
  by_cases hn : x = y ∧ y = z
  · obtain ⟨hxy, hyz⟩ := hn
    subst x
    subst y
    rw [m_uniform z hz, K_uniform z hz]
    have heq := entropy_curvature_uniform_endpoint z
    convert le_of_eq heq.symm using 1
    ring
  · exact le_of_lt (entropy_curvature_strict x y z hx hy hz hn)

/-- Equality in the sharp curvature bound holds exactly at uniform triples. -/
theorem entropy_curvature_eq_iff (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    K x y z = 16 / (15 * (x + y + z + m x y z)) ↔ x = y ∧ y = z := by
  constructor
  · intro heq
    by_contra hn
    exact (ne_of_lt (entropy_curvature_strict x y z hx hy hz hn)) heq.symm
  · rintro ⟨hxy, hyz⟩
    subst x
    subst y
    rw [m_uniform z hz, K_uniform z hz]
    convert entropy_curvature_uniform_endpoint z using 1
    ring

/-- Lemma `lem:entropy`, including both sharp equality characterizations. -/
theorem entropy_curvature (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (0 < m x y z ∧ m x y z ≤ (x + y + z) / 3) ∧
      16 / (15 * (x + y + z + m x y z)) ≤ K x y z ∧
      (m x y z = (x + y + z) / 3 ↔ x = y ∧ y = z) ∧
      (K x y z = 16 / (15 * (x + y + z + m x y z)) ↔ x = y ∧ y = z) :=
  ⟨⟨m_pos x y z hx hy hz, m_le_mean x y z hx hy hz⟩,
    entropy_curvature_bound x y z hx hy hz, m_eq_mean_iff x y z hx hy hz,
    entropy_curvature_eq_iff x y z hx hy hz⟩

end EntropyConstrainedMissingMass.Curvature
