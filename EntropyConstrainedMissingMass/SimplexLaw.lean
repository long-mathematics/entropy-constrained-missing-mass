import EntropyConstrainedMissingMass.SimplexIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A genuine probability law for the uniform-simplex parametrization. -/

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Topology unitInterval

namespace EntropyConstrainedMissingMass
namespace Curvature

abbrev SimplexSquare := I × I

/-- Jacobian weight of the square parametrization of the uniform simplex. -/
def simplexWeight (q : SimplexSquare) : ℝ := 2 * (1 - (q.1 : ℝ))

/-- The square-coordinate probability measure inducing uniform simplex coordinates. -/
noncomputable def simplexMeasure : Measure SimplexSquare :=
  volume.withDensity (fun q => ENNReal.ofReal (simplexWeight q))

theorem simplexWeight_nonneg (q : SimplexSquare) : 0 ≤ simplexWeight q := by
  unfold simplexWeight
  have h := q.1.property.2
  positivity

/-- Integrals on the canonical unit-interval probability space are ordinary interval integrals. -/
theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ u : I, f (u : ℝ)) = ∫ u in (0 : ℝ)..1, f u := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

private theorem continuous_simplexWeight : Continuous simplexWeight := by
  unfold simplexWeight
  fun_prop

private theorem integrable_simplexWeight : Integrable simplexWeight :=
  continuous_simplexWeight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The Jacobian weight integrates to one. -/
theorem integral_simplexWeight : (∫ q : SimplexSquare, simplexWeight q) = 1 := by
  change (∫ q : SimplexSquare, simplexWeight q ∂(volume.prod volume)) = 1
  rw [integral_prod _ integrable_simplexWeight]
  simp only [simplexWeight, integral_const, probReal_univ, one_smul]
  rw [integral_unitInterval (fun u : ℝ => 2 * (1 - u))]
  have hi : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
    continuous_id.intervalIntegrable (0 : ℝ) 1
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const hi]
  norm_num

instance simplexMeasure_probability : IsProbabilityMeasure simplexMeasure where
  measure_univ := by
    unfold simplexMeasure
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_simplexWeight
      (Filter.Eventually.of_forall simplexWeight_nonneg), integral_simplexWeight]
    norm_num

/-- Integration against the simplex law is integration with its nonnegative Jacobian weight. -/
theorem integral_simplexMeasure (f : SimplexSquare → ℝ) :
    (∫ q, f q ∂simplexMeasure) = ∫ q, simplexWeight q * f q := by
  unfold simplexMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      rw [ENNReal.toReal_ofReal (simplexWeight_nonneg q), smul_eq_mul])
  · exact continuous_simplexWeight.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- Weighted Fubini on the simplex square, for continuous functions. -/
theorem integral_simplexMeasure_eq_iterated (f : ℝ → ℝ → ℝ)
    (hf : Continuous (fun q : SimplexSquare => f q.1 q.2)) :
    (∫ q : SimplexSquare, f q.1 q.2 ∂simplexMeasure) =
      ∫ u in (0 : ℝ)..1, 2 * (1 - u) * ∫ v in (0 : ℝ)..1, f u v := by
  rw [integral_simplexMeasure]
  have hi : Integrable (fun q : SimplexSquare => simplexWeight q * f q.1 q.2) :=
    (continuous_simplexWeight.mul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change (∫ q : SimplexSquare, simplexWeight q * f q.1 q.2 ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  simp only [simplexWeight, integral_const_mul]
  simp_rw [integral_unitInterval]
  exact integral_unitInterval (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, f u v)

/-- The barycentric coordinates are nonnegative and sum to one under this law. -/
theorem simplex_coordinates (q : SimplexSquare) :
    0 ≤ (q.1 : ℝ) ∧ 0 ≤ (1 - (q.1 : ℝ)) * (q.2 : ℝ) ∧
      0 ≤ (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)) ∧
      (q.1 : ℝ) + (1 - (q.1 : ℝ)) * (q.2 : ℝ) +
        (1 - (q.1 : ℝ)) * (1 - (q.2 : ℝ)) = 1 := by
  have hu0 := q.1.property.1
  have hu1 := q.1.property.2
  have hv0 := q.2.property.1
  have hv1 := q.2.property.2
  refine ⟨hu0, by positivity, by positivity, ?_⟩
  ring

/-- The interval containing all simplex scales. -/
abbrev ScaleInterval (x y z : ℝ) := Icc (min x (min y z)) (max x (max y z))

/-- The simplex scale as an element of its compact range interval. -/
def simplexScale (x y z : ℝ) (q : SimplexSquare) : ScaleInterval x y z :=
  ⟨simplexValue x y z q.1 q.2, simplexValue_mem x y z _ _ q.1 q.2
    ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
    q.1.property q.2.property⟩

theorem continuous_simplexScale (x y z : ℝ) : Continuous (simplexScale x y z) := by
  apply Continuous.subtype_mk
  unfold simplexValue
  fun_prop

/-- The law of the affine simplex scale. -/
noncomputable def simplexLaw (x y z : ℝ) : Measure (ScaleInterval x y z) :=
  simplexMeasure.map (simplexScale x y z)

instance simplexLaw_probability (x y z : ℝ) : IsProbabilityMeasure (simplexLaw x y z) := by
  unfold simplexLaw
  infer_instance

/-- The lower endpoint of the scale interval is positive for a positive triple. -/
theorem scaleInterval_lower_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < min x (min y z) := lt_min hx (lt_min hy hz)

/-- The exact pushforward integration formula. -/
theorem integral_simplexLaw (x y z : ℝ) (f : ScaleInterval x y z → ℝ) (hf : Continuous f) :
    (∫ v, f v ∂simplexLaw x y z) = ∫ q, f (simplexScale x y z q) ∂simplexMeasure := by
  exact integral_map (continuous_simplexScale x y z).measurable.aemeasurable
    hf.aestronglyMeasurable

/-- First moment of the actual simplex probability law. -/
theorem simplexLaw_mean (x y z : ℝ) : mixtureMean (simplexLaw x y z) = (x + y + z) / 3 := by
  unfold mixtureMean
  rw [integral_simplexLaw x y z _ continuous_subtype_val]
  change (∫ q : SimplexSquare, simplexValue x y z q.1 q.2 ∂simplexMeasure) = _
  rw [integral_simplexMeasure_eq_iterated (simplexValue x y z) (by unfold simplexValue; fun_prop),
    simplex_first_moment]

/-- Second moment of the actual simplex probability law. -/
theorem simplexLaw_second_moment (x y z : ℝ) :
    (∫ v : ScaleInterval x y z, (v : ℝ) ^ 2 ∂simplexLaw x y z) =
      (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z) / 6 := by
  rw [integral_simplexLaw x y z _ (by fun_prop)]
  change (∫ q : SimplexSquare, (simplexValue x y z q.1 q.2) ^ 2 ∂simplexMeasure) = _
  rw [integral_simplexMeasure_eq_iterated (fun u v => (simplexValue x y z u v) ^ 2)
    (by unfold simplexValue; fun_prop), simplex_second_moment]

/-- The inverse-cubic integral representation now holds as an expectation under
an actual compactly supported probability measure. -/
theorem simplexLaw_inverse_cube (x y z s : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : 0 ≤ s) :
    (∫ v : ScaleInterval x y z, 1 / (s + (v : ℝ)) ^ 3 ∂simplexLaw x y z) = 1 / D x y z s := by
  have hlo := scaleInterval_lower_pos x y z hx hy hz
  have hf : Continuous (fun v : ScaleInterval x y z => 1 / (s + (v : ℝ)) ^ 3) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le hlo v.property.1
    positivity
  rw [integral_simplexLaw x y z _ hf]
  change (∫ q : SimplexSquare, 1 / (s + simplexValue x y z q.1 q.2) ^ 3 ∂simplexMeasure) = _
  have hcont : Continuous (fun q : SimplexSquare => 1 / (s + simplexValue x y z q.1 q.2) ^ 3) :=
    hf.comp (continuous_simplexScale x y z)
  rw [integral_simplexMeasure_eq_iterated (fun u v => 1 / (s + simplexValue x y z u v) ^ 3) hcont,
    simplex_denominator_representation x y z s hx hy hz hs]

end Curvature
end EntropyConstrainedMissingMass
