import EntropyConstrainedMissingMass.ObjectiveCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Strict quasiconvexity of `u fₜ''(u)` on the negative-curvature interval.
The proof uses the strictly decreasing quadratic controlling its derivative,
so does not need to introduce the quadratic roots. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set

def weightedCurvature (t : ℕ) (u : ℝ) : ℝ :=
  u * deriv (deriv (missingMassTerm t)) u

def curvatureDerivativeQuadratic (t : ℕ) (u : ℝ) : ℝ :=
  (t : ℝ) * ((t : ℝ) + 1) * u ^ 2 - 4 * (t : ℝ) * u + 2

theorem weightedCurvature_eq (t : ℕ) (ht : 2 ≤ t) (u : ℝ) :
    weightedCurvature t u =
      u * (t : ℝ) * (1 - u) ^ (t - 2) * (((t : ℝ) + 1) * u - 2) := by
  rw [weightedCurvature, deriv_deriv_missingMassTerm t ht]
  ring

theorem continuous_weightedCurvature (t : ℕ) (ht : 2 ≤ t) :
    Continuous (weightedCurvature t) := by
  change Continuous (fun u => weightedCurvature t u)
  simp_rw [weightedCurvature_eq t ht]
  fun_prop

theorem weightedCurvature_one (u : ℝ) : weightedCurvature 1 u = -2 * u := by
  have hfun : deriv (missingMassTerm 1) = fun x : ℝ => 1 - 2 * x := by
    funext x
    rw [deriv_missingMassTerm 1 (by omega)]
    norm_num
    ring
  rw [weightedCurvature, hfun]
  have hd := (((hasDerivAt_id u).const_mul 2).const_sub 1).deriv
  simp only [mul_one, id_eq] at hd
  rw [hd]
  ring

theorem hasDerivAt_weightedCurvature_ge_three (t : ℕ) (ht : 3 ≤ t) (u : ℝ) :
    HasDerivAt (weightedCurvature t)
      (-(t : ℝ) * (1 - u) ^ (t - 3) * curvatureDerivativeQuadratic t u) u := by
  have hfun : weightedCurvature t = fun x : ℝ =>
      x * (t : ℝ) * (1 - x) ^ (t - 2) * (((t : ℝ) + 1) * x - 2) :=
    funext (weightedCurvature_eq t (by omega))
  rw [hfun]
  have hd := ((((hasDerivAt_id u).mul_const (t : ℝ)).mul
    (((hasDerivAt_id u).const_sub 1).fun_pow (t - 2))).mul
    (((hasDerivAt_id u).const_mul ((t : ℝ) + 1)).sub_const 2))
  convert hd using 1
  · rfl
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    have hn2 : 3 + n - 2 = n + 1 := by omega
    have hn3 : 3 + n - 3 = n := by omega
    simp only [hn2, hn3, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, curvatureDerivativeQuadratic, id_eq, Pi.mul_apply]
    rw [pow_succ]
    ring

/-- A formula valid also at sample size two, avoiding negative natural exponents. -/
theorem deriv_weightedCurvature_mul_one_sub (t : ℕ) (ht : 2 ≤ t) (u : ℝ) :
    deriv (weightedCurvature t) u * (1 - u) =
      -(t : ℝ) * (1 - u) ^ (t - 2) * curvatureDerivativeQuadratic t u := by
  by_cases ht2 : t = 2
  · subst t
    have hfun : weightedCurvature 2 = fun x : ℝ => 6 * x ^ 2 - 4 * x := by
      funext x
      rw [weightedCurvature_eq 2 (by omega)]
      norm_num
      ring
    rw [hfun]
    have hd := ((((hasDerivAt_id u).fun_pow 2).const_mul 6).sub
      ((hasDerivAt_id u).const_mul 4)).deriv
    change deriv (fun x : ℝ => 6 * x ^ 2 - 4 * x) u = _ at hd
    rw [hd]
    norm_num [curvatureDerivativeQuadratic]
    ring
  · have ht3 : 3 ≤ t := by omega
    rw [(hasDerivAt_weightedCurvature_ge_three t ht3 u).deriv]
    have hexp : t - 2 = (t - 3) + 1 := by omega
    rw [hexp, pow_succ]
    ring

theorem curvatureDerivativeQuadratic_strictAnti (t : ℕ) (ht : 1 ≤ t)
    {x y : ℝ} (hxy : x < y) (hy : y ≤ 2 / ((t : ℝ) + 1)) :
    curvatureDerivativeQuadratic t y < curvatureDerivativeQuadratic t x := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hy' := (le_div_iff₀ ht1).1 hy
  have hgap : 0 < 4 - ((t : ℝ) + 1) * (x + y) := by nlinarith
  have hprod := mul_pos (mul_pos ht0 (sub_pos.mpr hxy)) hgap
  unfold curvatureDerivativeQuadratic
  nlinarith

theorem deriv_weightedCurvature_neg (t : ℕ) (ht : 2 ≤ t) {u : ℝ} (hu : u < 1)
    (hq : 0 < curvatureDerivativeQuadratic t u) : deriv (weightedCurvature t) u < 0 := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hb : 0 < 1 - u := sub_pos.mpr hu
  have hmul := deriv_weightedCurvature_mul_one_sub t ht u
  have hneg : -(t : ℝ) * (1 - u) ^ (t - 2) * curvatureDerivativeQuadratic t u < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos ht0) (pow_pos hb _)) hq
  nlinarith

theorem deriv_weightedCurvature_pos (t : ℕ) (ht : 2 ≤ t) {u : ℝ} (hu : u < 1)
    (hq : curvatureDerivativeQuadratic t u < 0) : 0 < deriv (weightedCurvature t) u := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hb : 0 < 1 - u := sub_pos.mpr hu
  have hmul := deriv_weightedCurvature_mul_one_sub t ht u
  have hpos : 0 < -(t : ℝ) * (1 - u) ^ (t - 2) * curvatureDerivativeQuadratic t u :=
    mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (neg_neg_of_pos ht0) (pow_pos hb _)) hq
  nlinarith

/-- The strict three-point inequality used in the repeated-size criterion.
The lower bound `x > 0` is not needed for this analytic inequality. -/
theorem weightedCurvature_strict_quasiconvex (t : ℕ) (ht : 1 ≤ t)
    {x v y : ℝ} (hxv : x < v) (hvy : v < y) (hy1 : y < 1)
    (hy : y ≤ 2 / ((t : ℝ) + 1)) :
    weightedCurvature t v < max (weightedCurvature t x) (weightedCurvature t y) := by
  by_cases ht1 : t = 1
  · subst t
    simp only [weightedCurvature_one]
    exact lt_of_lt_of_le (by linarith : -2 * v < -2 * x) (le_max_left _ _)
  have ht2 : 2 ≤ t := by omega
  by_cases hq : 0 ≤ curvatureDerivativeQuadratic t v
  · have hanti : StrictAntiOn (weightedCurvature t) (Icc x v) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x v)
        (continuous_weightedCurvature t ht2).continuousOn
      intro u hu
      rw [interior_Icc] at hu
      apply deriv_weightedCurvature_neg t ht2 (lt_trans hu.2 (lt_trans hvy hy1))
      exact lt_of_le_of_lt hq
        (curvatureDerivativeQuadratic_strictAnti t ht hu.2 (hvy.le.trans hy))
    exact lt_of_lt_of_le
      (hanti (left_mem_Icc.mpr hxv.le) (right_mem_Icc.mpr hxv.le) hxv) (le_max_left _ _)
  · have hqneg : curvatureDerivativeQuadratic t v < 0 := lt_of_not_ge hq
    have hmono : StrictMonoOn (weightedCurvature t) (Icc v y) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc v y)
        (continuous_weightedCurvature t ht2).continuousOn
      intro u hu
      rw [interior_Icc] at hu
      apply deriv_weightedCurvature_pos t ht2 (lt_trans hu.2 hy1)
      exact lt_trans (curvatureDerivativeQuadratic_strictAnti t ht hu.1 (hu.2.le.trans hy)) hqneg
    exact lt_of_lt_of_le
      (hmono (left_mem_Icc.mpr hvy.le) (right_mem_Icc.mpr hvy.le) hvy) (le_max_right _ _)

/-- The manuscript's interval, with its ambient open probability interval made explicit. -/
def negativeCurvatureInterval (t : ℕ) : Set ℝ :=
  {u | 0 < u ∧ u < 1 ∧ u ≤ 2 / ((t : ℝ) + 1)}

/-- For sample sizes above one, the interval really is the nonpositive-curvature region. -/
theorem deriv2_missingMassTerm_nonpos_iff (t : ℕ) (ht : 2 ≤ t) {u : ℝ} (hu : u < 1) :
    deriv (deriv (missingMassTerm t)) u ≤ 0 ↔ u ≤ 2 / ((t : ℝ) + 1) := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hfactor : 0 < (t : ℝ) * (1 - u) ^ (t - 2) :=
    mul_pos ht0 (pow_pos (sub_pos.mpr hu) _)
  rw [deriv_deriv_missingMassTerm t ht, mul_nonpos_iff]
  simp only [hfactor.le, not_le.mpr hfactor, true_and, false_and, or_false]
  rw [sub_nonpos]
  rw [le_div_iff₀ (by positivity : 0 < (t : ℝ) + 1)]
  rw [mul_comm]

theorem weightedCurvature_strict_quasiconvex_on_interval (t : ℕ) (ht : 1 ≤ t)
    {x v y : ℝ} (_hx : x ∈ negativeCurvatureInterval t)
    (hy : y ∈ negativeCurvatureInterval t) (hxv : x < v) (hvy : v < y) :
    weightedCurvature t v < max (weightedCurvature t x) (weightedCurvature t y) :=
  weightedCurvature_strict_quasiconvex t ht hxv hvy hy.2.1 hy.2.2

end
end EntropyConstrainedMissingMass
