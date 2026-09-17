import EntropyConstrainedMissingMass.DividedDifferences
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! The scalar Rolle argument making the P derivative strictly positive at a stationary triple. -/

namespace EntropyConstrainedMissingMass

theorem deriv2_missingMassTerm_eq_zero_iff (t : ℕ) (ht : 2 ≤ t) {u : ℝ} (hu : u < 1) :
    deriv (deriv (missingMassTerm t)) u = 0 ↔ u = 2 / ((t : ℝ) + 1) := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have hp : (t : ℝ) * (1 - u) ^ (t - 2) ≠ 0 := ne_of_gt (mul_pos ht0 (pow_pos (sub_pos.mpr hu) _))
  rw [deriv_deriv_missingMassTerm t ht, mul_eq_zero, or_iff_right hp, sub_eq_zero]
  rw [eq_div_iff (by positivity : (t : ℝ) + 1 ≠ 0)]
  exact ⟨fun h => by nlinarith only [h], fun h => by nlinarith only [h]⟩

theorem existsUnique_second_derivative_zero (t : ℕ) (ht : 2 ≤ t) :
    ∃! u : ℝ, u ∈ Set.Ioo 0 1 ∧ deriv (deriv (missingMassTerm t)) u = 0 := by
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < (t : ℝ) + 1 := by positivity
  have hu0 : 0 < 2 / ((t : ℝ) + 1) := div_pos (by norm_num) hden
  have hu1 : 2 / ((t : ℝ) + 1) < 1 := (div_lt_one hden).mpr (by linarith)
  refine ⟨2 / ((t : ℝ) + 1), ⟨⟨hu0, hu1⟩, (deriv2_missingMassTerm_eq_zero_iff t ht hu1).mpr rfl⟩, ?_⟩
  intro u hu
  exact (deriv2_missingMassTerm_eq_zero_iff t ht hu.1.2).mp hu.2

theorem continuous_deriv_missingMassTerm (t : ℕ) (ht : 1 ≤ t) :
    Continuous (deriv (missingMassTerm t)) := by
  have heq : deriv (missingMassTerm t) = fun u : ℝ =>
      ((t : ℝ) + 1) * (1 - u) ^ t - (t : ℝ) * (1 - u) ^ (t - 1) :=
    funext (deriv_missingMassTerm t ht)
  rw [heq]
  fun_prop

/-- Two applications of Rolle exclude three distinct roots of a horizontal derivative level. -/
theorem not_three_equal_objective_derivatives (t : ℕ) (ht : 2 ≤ t)
    {x y z : ℝ} (hxy : x < y) (hyz : y < z) (hz : z < 1) :
    ¬ (deriv (missingMassTerm t) x = deriv (missingMassTerm t) y ∧
      deriv (missingMassTerm t) y = deriv (missingMassTerm t) z) := by
  intro heq
  have hc := continuous_deriv_missingMassTerm t (by omega)
  obtain ⟨u, hu, hdu⟩ := exists_deriv_eq_zero hxy hc.continuousOn heq.1
  obtain ⟨v, hv, hdv⟩ := exists_deriv_eq_zero hyz hc.continuousOn heq.2
  have huval := (deriv2_missingMassTerm_eq_zero_iff t ht (hu.2.trans (hyz.trans hz))).mp hdu
  have hvval := (deriv2_missingMassTerm_eq_zero_iff t ht (hv.2.trans hz)).mp hdv
  linarith [hu.2, hv.1]

namespace TripleGeometry

/-- Vanishing of both divided differences forces a statistic to agree at all three roots. -/
theorem values_eq_of_secondDifference_zero (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (f : ℝ → ℝ) (hP : secondDifference x f = 0)
    (hE : secondDifference x (fun u => u * f u) = 0) :
    f (x 0) = f (x 1) ∧ f (x 1) = f (x 2) := by
  have h02 := h01.trans h12
  have hd01 : x 0 - x 1 ≠ 0 := sub_ne_zero.mpr h01.ne
  have hd02 : x 0 - x 2 ≠ 0 := sub_ne_zero.mpr h02.ne
  have hd12 : x 1 - x 2 ≠ 0 := sub_ne_zero.mpr h12.ne
  have hd10 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr h01.ne.symm
  have hd20 : x 2 - x 0 ≠ 0 := sub_ne_zero.mpr h02.ne.symm
  have hd21 : x 2 - x 1 ≠ 0 := sub_ne_zero.mpr h12.ne.symm
  have ha : (x 0 - x 1) * (x 2 * secondDifference x f -
      secondDifference x (fun u => u * f u)) = f (x 1) - f (x 0) := by
    simp [secondDifference, Fin.sum_univ_succ, rootDenom]
    field_simp
    ring
  have hb : (x 1 - x 2) * (x 0 * secondDifference x f -
      secondDifference x (fun u => u * f u)) = f (x 2) - f (x 1) := by
    simp [secondDifference, Fin.sum_univ_succ, rootDenom]
    field_simp
    ring
  rw [hP, hE] at ha hb
  constructor <;> linarith

/-- The exact algebraic/Rolle step used after genuine local variations supply stationarity. -/
theorem objective_P_pos_of_stationary (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (hx2 : x 2 < 1) (t : ℕ) (ht : 2 ≤ t) (m : ℝ)
    (hP : 0 ≤ secondDifference x (deriv (missingMassTerm t)))
    (hstat : -secondDifference x (fun u => u * deriv (missingMassTerm t) u) -
      m * secondDifference x (deriv (missingMassTerm t)) = 0) :
    0 < secondDifference x (deriv (missingMassTerm t)) := by
  by_contra hn
  have hz : secondDifference x (deriv (missingMassTerm t)) = 0 := le_antisymm (le_of_not_gt hn) hP
  have hE : secondDifference x (fun u => u * deriv (missingMassTerm t) u) = 0 := by
    rw [hz] at hstat
    linarith
  exact not_three_equal_objective_derivatives t ht h01 h12 hx2
    (values_eq_of_secondDifference_zero x h01 h12 _ hz hE)

/-- The sample-size-one objective is affine in E at fixed sum. -/
theorem triple_objective_one (x : Triple) :
    (∑ i : Fin 3, missingMassTerm 1 (x i)) =
      symmetricMap x 0 - (symmetricMap x 0) ^ 2 + 2 * symmetricMap x 1 := by
  simp [missingMassTerm, symmetricMap, Fin.sum_univ_succ]
  ring

theorem secondDifference_identity (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    secondDifference x (fun u => u) = 0 := by
  have heq : (fun u : ℝ => u) = fun u => 1 - (1 - u) := by funext u; ring
  rw [heq, secondDifference_sub, secondDifference_constant x h01 h12,
    secondDifference_shifted_linear x h01 h12]
  ring

theorem secondDifference_square (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    secondDifference x (fun u => u ^ 2) = 1 := by
  have heq : (fun u : ℝ => u ^ 2) = fun u => (1 - u) ^ 2 + 2 * u - 1 := by funext u; ring
  rw [heq, secondDifference_sub, secondDifference_add, secondDifference_const_mul,
    secondDifference_identity x h01 h12, secondDifference_constant x h01 h12]
  have hh := secondDifference_shifted_pow x h01 h12 0
  simpa using hh

theorem secondDifference_deriv_one (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    secondDifference x (deriv (missingMassTerm 1)) = 0 := by
  have heq : deriv (missingMassTerm 1) = fun u : ℝ => 1 - 2 * u := by
    funext u
    rw [deriv_missingMassTerm 1 (by omega)]
    norm_num
    ring
  rw [heq, secondDifference_sub, secondDifference_const_mul,
    secondDifference_constant x h01 h12, secondDifference_identity x h01 h12]
  ring

theorem neg_secondDifference_mul_deriv_one (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    -secondDifference x (fun u => u * deriv (missingMassTerm 1) u) = 2 := by
  have heq : (fun u : ℝ => u * deriv (missingMassTerm 1) u) = fun u => u - 2 * u ^ 2 := by
    funext u
    rw [deriv_missingMassTerm 1 (by omega)]
    norm_num
    ring
  rw [heq, secondDifference_sub, secondDifference_const_mul,
    secondDifference_identity x h01 h12, secondDifference_square x h01 h12]
  ring

theorem hasDerivAt_localObjective_one_E (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 (missingMassTerm 1)
      (symmetricMap x + r • ![0, 1, 0])) 2 0 := by
  rw [← neg_secondDifference_mul_deriv_one x h01 h12]
  exact hasDerivAt_localStatistic_E x h01 h12 _ _
    (fun i => (hasDerivAt_missingMassTerm 1 (by omega) (x i)).differentiableAt.hasDerivAt)

theorem hasDerivAt_localObjective_one_P (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 (missingMassTerm 1)
      (symmetricMap x + r • ![0, 0, 1])) 0 0 := by
  have hd := hasDerivAt_localStatistic_P x h01 h12 (missingMassTerm 1) (deriv (missingMassTerm 1))
    (fun i => (hasDerivAt_missingMassTerm 1 (by omega) (x i)).differentiableAt.hasDerivAt)
  simpa only [secondDifference_deriv_one x h01 h12] using hd

end TripleGeometry
end EntropyConstrainedMissingMass
