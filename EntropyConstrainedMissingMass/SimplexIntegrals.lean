import EntropyConstrainedMissingMass.MixtureCurvature
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The elementary simplex integrals

The square parametrization `(u,v) ↦ (u,(1-u)v,(1-u)(1-v))`, with density
`2(1-u)`, represents the uniform probability law on the two-dimensional simplex.
The rational antiderivatives below work even when atom sizes coincide.
-/

open MeasureTheory Set
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- The affine scale obtained from barycentric simplex coordinates. -/
def simplexValue (x y z u v : ℝ) : ℝ :=
  u * x + (1 - u) * v * y + (1 - u) * (1 - v) * z

private theorem affine_segment_pos (a b u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : u ∈ Icc (0 : ℝ) 1) : 0 < a + (b - a) * u := by
  by_cases hu0 : u = 0
  · simpa [hu0] using ha
  · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    have h1 : 0 ≤ (1 - u) * a := mul_nonneg (by linarith [hu.2]) (le_of_lt ha)
    have h2 := mul_pos hup hb
    nlinarith

/-- The inverse cubic integral along any positive line segment, without a
nondegeneracy assumption on its endpoints. -/
theorem integral_affine_inv_cube (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ v in (0 : ℝ)..1, 1 / (a + (b - a) * v) ^ 3) =
      (a + b) / (2 * a ^ 2 * b ^ 2) := by
  let F : ℝ → ℝ := fun v => v * (2 * a + (b - a) * v) /
    (2 * a ^ 2 * (a + (b - a) * v) ^ 2)
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt F (1 / (a + (b - a) * v) ^ 3) v := by
    intro v hv
    have hbase := affine_segment_pos a b v ha hb (by simpa using hv)
    have hNum := (hasDerivAt_id v).mul
      (((hasDerivAt_id v).const_mul (b - a)).const_add (2 * a))
    have hDen := ((((hasDerivAt_id v).const_mul (b - a)).const_add a).fun_pow 2).const_mul (2 * a ^ 2)
    convert hNum.div hDen (by positivity) using 1
    · rfl
    · simp only [id_eq, Pi.mul_apply]
      norm_num
      field_simp
      ring
  have hcont : ContinuousOn (fun v : ℝ => 1 / (a + (b - a) * v) ^ 3) (Icc 0 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro v hv
      exact pow_ne_zero _ (ne_of_gt (affine_segment_pos a b v ha hb hv))
  have hi : IntervalIntegrable (fun v : ℝ => 1 / (a + (b - a) * v) ^ 3) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [F]
  field_simp
  ring

private theorem integral_outer_inverse (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ u in (0 : ℝ)..1, (1 - u) * ((z + (x - z) * u) + (y + (x - y) * u)) /
      ((z + (x - z) * u) ^ 2 * (y + (x - y) * u) ^ 2)) = 1 / (x * y * z) := by
  let A : ℝ → ℝ := fun u => z + (x - z) * u
  let B : ℝ → ℝ := fun u => y + (x - y) * u
  let F : ℝ → ℝ := fun u => -(1 - u) ^ 2 / (x * A u * B u)
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      ((1 - u) * (A u + B u) / ((A u) ^ 2 * (B u) ^ 2)) u := by
    intro u hu
    have hA : 0 < A u := affine_segment_pos z x u hz hx (by simpa using hu)
    have hB : 0 < B u := affine_segment_pos y x u hy hx (by simpa using hu)
    have hNum := (((hasDerivAt_id u).const_sub 1).fun_pow 2).neg
    have hDA := ((hasDerivAt_id u).const_mul (x - z)).const_add z
    have hDB := ((hasDerivAt_id u).const_mul (x - y)).const_add y
    have hDen := (hDA.const_mul x).mul hDB
    convert hNum.div hDen (by change x * A u * B u ≠ 0; positivity) using 1
    · rfl
    · dsimp [A, B] at *
      norm_num
      field_simp
      ring
  have hcont : ContinuousOn (fun u => (1 - u) * (A u + B u) / ((A u) ^ 2 * (B u) ^ 2))
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div
    · dsimp [A, B]; fun_prop
    · dsimp [A, B]; fun_prop
    · intro u hu
      have hA : 0 < A u := affine_segment_pos z x u hz hx hu
      have hB : 0 < B u := affine_segment_pos y x u hy hx hu
      positivity
  have hi : IntervalIntegrable (fun u => (1 - u) * (A u + B u) / ((A u) ^ 2 * (B u) ^ 2))
      volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num)
  change (∫ u in (0 : ℝ)..1, (1 - u) * (A u + B u) / ((A u) ^ 2 * (B u) ^ 2)) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [F, A, B]
  field_simp

/-- The normalized simplex average of the reciprocal cube is the reciprocal
product. This is the mixture representation's analytic core. -/
theorem simplex_inverse_cube (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, 1 / (simplexValue x y z u v) ^ 3) = 1 / (x * y * z) := by
  have heq : (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, 1 / (simplexValue x y z u v) ^ 3) =
      ∫ u in (0 : ℝ)..1, (1 - u) * ((z + (x - z) * u) + (y + (x - y) * u)) /
        ((z + (x - z) * u) ^ 2 * (y + (x - y) * u) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hA := affine_segment_pos z x u hz hx hu'
    have hB := affine_segment_pos y x u hy hx hu'
    have hinner : (fun v : ℝ => 1 / (simplexValue x y z u v) ^ 3) =
        (fun v : ℝ => 1 / ((z + (x - z) * u) +
          ((y + (x - y) * u) - (z + (x - z) * u)) * v) ^ 3) := by
      funext v
      congr 2
      unfold simplexValue
      ring
    dsimp only
    rw [hinner, integral_affine_inv_cube _ _ hA hB]
    field_simp
  rw [heq, integral_outer_inverse x y z hx hy hz]

/-- Adding the same location to all three scales shifts the simplex value by
that location because its barycentric coordinates sum to one. -/
theorem simplexValue_add (x y z s u v : ℝ) :
    simplexValue (s + x) (s + y) (s + z) u v = s + simplexValue x y z u v := by
  unfold simplexValue
  ring

/-- The shifted reciprocal-cube representation of the denominator `D`. -/
theorem simplex_denominator_representation (x y z s : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hs : 0 ≤ s) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, 1 / (s + simplexValue x y z u v) ^ 3) = 1 / D x y z s := by
  have h := simplex_inverse_cube (s + x) (s + y) (s + z) (by positivity) (by positivity) (by positivity)
  simpa only [simplexValue_add, D] using h

/-- Convexity keeps every simplex scale between common lower and upper bounds. -/
theorem simplexValue_mem (x y z a b u v : ℝ)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hz : z ∈ Icc a b)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    simplexValue x y z u v ∈ Icc a b := by
  have h2 : 0 ≤ (1 - u) * v := mul_nonneg (by linarith [hu.2]) hv.1
  have h3 : 0 ≤ (1 - u) * (1 - v) :=
    mul_nonneg (by linarith [hu.2]) (by linarith [hv.2])
  constructor
  · have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx.1 hu.1)
      (mul_le_mul_of_nonneg_left hy.1 h2)) (mul_le_mul_of_nonneg_left hz.1 h3)
    convert h using 1 <;> (try unfold simplexValue) <;> ring
  · have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx.2 hu.1)
      (mul_le_mul_of_nonneg_left hy.2 h2)) (mul_le_mul_of_nonneg_left hz.2 h3)
    convert h using 1 <;> (try unfold simplexValue) <;> ring

private theorem integral_poly_two (A B C : ℝ) :
    (∫ u in (0 : ℝ)..1, A * u ^ 2 + B * u + C) = A / 3 + B / 2 + C := by
  have hA : IntervalIntegrable (fun u : ℝ => A * u ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun u : ℝ => B * u) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hA.add hB) intervalIntegrable_const,
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  norm_num
  ring

private theorem integral_poly_three (A B C D : ℝ) :
    (∫ u in (0 : ℝ)..1, A * u ^ 3 + (B * u ^ 2 + C * u + D)) =
      A / 4 + B / 3 + C / 2 + D := by
  have hA : IntervalIntegrable (fun u : ℝ => A * u ^ 3) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun u : ℝ => B * u ^ 2 + C * u + D) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    integral_poly_two]
  norm_num
  ring

private theorem simplex_inner_moments (x y z u : ℝ) :
    (∫ v in (0 : ℝ)..1, simplexValue x y z u v) =
      (z + (x - z) * u) + ((1 - u) * (y - z)) / 2 ∧
    (∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (z + (x - z) * u) ^ 2 + (z + (x - z) * u) * ((1 - u) * (y - z)) +
        ((1 - u) * (y - z)) ^ 2 / 3 := by
  let A := z + (x - z) * u
  let B := (1 - u) * (y - z)
  constructor
  · have heq : (fun v : ℝ => simplexValue x y z u v) =
        (fun v : ℝ => 0 * v ^ 2 + B * v + A) := by funext v; dsimp [A, B, simplexValue]; ring
    rw [heq, integral_poly_two]
    dsimp [A, B]
    ring
  · have heq : (fun v : ℝ => (simplexValue x y z u v) ^ 2) =
        (fun v : ℝ => B ^ 2 * v ^ 2 + (2 * A * B) * v + A ^ 2) := by
      funext v
      dsimp [A, B, simplexValue]
      ring
    rw [heq, integral_poly_two]
    dsimp [A, B]
    ring

/-- The first moment of a uniform simplex scale. -/
theorem simplex_first_moment (x y z : ℝ) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, simplexValue x y z u v) = (x + y + z) / 3 := by
  have heq : (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, simplexValue x y z u v) =
      (fun u : ℝ => (-2 * x + y + z) * u ^ 2 + (2 * x - 2 * y - 2 * z) * u + (y + z)) := by
    funext u
    rw [(simplex_inner_moments x y z u).1]
    ring
  rw [heq, integral_poly_two]
  ring

/-- The second moment records nondegeneracy whenever the triple is nonuniform. -/
theorem simplex_second_moment (x y z : ℝ) :
    (∫ u in (0 : ℝ)..1, 2 * (1 - u) *
      ∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z) / 6 := by
  have heq : (fun u : ℝ => 2 * (1 - u) * ∫ v in (0 : ℝ)..1, (simplexValue x y z u v) ^ 2) =
      (fun u : ℝ =>
        (-2 * x ^ 2 + 2 * x * y + 2 * x * z - 2 * y ^ 2 / 3 - 2 * y * z / 3 - 2 * z ^ 2 / 3) * u ^ 3 +
        ((2 * x ^ 2 - 4 * x * y - 4 * x * z + 2 * y ^ 2 + 2 * y * z + 2 * z ^ 2) * u ^ 2 +
        (2 * x * y + 2 * x * z - 2 * y ^ 2 - 2 * y * z - 2 * z ^ 2) * u +
        (2 * y ^ 2 / 3 + 2 * y * z / 3 + 2 * z ^ 2 / 3))) := by
    funext u
    rw [(simplex_inner_moments x y z u).2]
    ring
  rw [heq, integral_poly_three]
  ring

end Curvature
end EntropyConstrainedMissingMass
