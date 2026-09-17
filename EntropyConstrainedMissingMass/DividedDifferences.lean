import EntropyConstrainedMissingMass.TripleGeometry
import EntropyConstrainedMissingMass.CoefficientPartialFractions
import EntropyConstrainedMissingMass.ObjectiveCalculus

/-! Second divided differences connect actual root derivatives to homogeneous coefficients. -/

namespace EntropyConstrainedMissingMass.TripleGeometry
noncomputable section

/-- The second divided difference at the three selected roots. -/
def secondDifference (x : Triple) (f : ℝ → ℝ) : ℝ :=
  ∑ i : Fin 3, f (x i) / rootDenom x i

theorem secondDifference_add (x : Triple) (f g : ℝ → ℝ) :
    secondDifference x (fun u => f u + g u) = secondDifference x f + secondDifference x g := by
  simp [secondDifference, add_div, Finset.sum_add_distrib]

theorem secondDifference_sub (x : Triple) (f g : ℝ → ℝ) :
    secondDifference x (fun u => f u - g u) = secondDifference x f - secondDifference x g := by
  simp [secondDifference, sub_div, Finset.sum_sub_distrib]

theorem secondDifference_const_mul (x : Triple) (a : ℝ) (f : ℝ → ℝ) :
    secondDifference x (fun u => a * f u) = a * secondDifference x f := by
  simp [secondDifference, mul_div_assoc, Finset.mul_sum]

theorem secondDifference_constant (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (c : ℝ) :
    secondDifference x (fun _ => c) = 0 := by
  have h02 := h01.trans h12
  simp [secondDifference, Fin.sum_univ_succ, rootDenom]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h12.ne,
    sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm, sub_ne_zero.mpr h12.ne.symm]
  ring

theorem secondDifference_shifted_linear (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    secondDifference x (fun u => 1 - u) = 0 := by
  have h02 := h01.trans h12
  simp [secondDifference, Fin.sum_univ_succ, rootDenom]
  field_simp [sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne, sub_ne_zero.mpr h12.ne,
    sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm, sub_ne_zero.mpr h12.ne.symm]
  ring

/-- Polynomial divided differences at degree n+2 are the complete homogeneous coefficients. -/
theorem secondDifference_shifted_pow (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) :
    secondDifference x (fun u => (1 - u) ^ (n + 2)) =
      homogeneous3 (1 - x 0) (1 - x 1) (1 - x 2) n := by
  have hq01 : 1 - x 0 ≠ 1 - x 1 := by linarith
  have hq02 : 1 - x 0 ≠ 1 - x 2 := by linarith
  have hq12 : 1 - x 1 ≠ 1 - x 2 := by linarith
  rw [homogeneous3_partial_fraction _ _ _ hq01 hq02 hq12]
  simp [secondDifference, Fin.sum_univ_succ, rootDenom]
  ring

theorem secondDifference_shifted_pow_previous (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (n : ℕ) : secondDifference x (fun u => (1 - u) ^ (n + 1)) =
      previousHomogeneous3 (1 - x 0) (1 - x 1) (1 - x 2) n := by
  cases n with
  | zero => simpa [previousHomogeneous3] using secondDifference_shifted_linear x h01 h12
  | succ n => exact secondDifference_shifted_pow x h01 h12 n

/-- The first root derivative of the objective, expressed with the source coefficient k_n. -/
theorem secondDifference_objective_deriv (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (n : ℕ) : secondDifference x (deriv (missingMassTerm (n + 2))) =
      ((n : ℝ) + 3) * weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
        (1 - x 0) (1 - x 1) (1 - x 2) n := by
  have heq : deriv (missingMassTerm (n + 2)) = fun u : ℝ =>
      ((n : ℝ) + 3) * (1 - u) ^ (n + 2) - ((n : ℝ) + 2) * (1 - u) ^ (n + 1) := by
    funext u
    rw [deriv_missingMassTerm (n + 2) (by omega)]
    push_cast
    ring
  rw [heq, secondDifference_sub, secondDifference_const_mul, secondDifference_const_mul,
    secondDifference_shifted_pow x h01 h12, secondDifference_shifted_pow_previous x h01 h12]
  unfold weightedCoefficient
  have hd : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/-- The E derivative is the negative divided difference of u f′(u). -/
theorem neg_secondDifference_mul_objective_deriv (x : Triple)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) :
    -secondDifference x (fun u => u * deriv (missingMassTerm (n + 2)) u) =
      ((n : ℝ) + 3) *
        (weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - x 0) (1 - x 1) (1 - x 2) (n + 1) -
        weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - x 0) (1 - x 1) (1 - x 2) n) := by
  have heq : (fun u : ℝ => u * deriv (missingMassTerm (n + 2)) u) = fun u =>
      (2 * (n : ℝ) + 5) * (1 - u) ^ (n + 2) -
      ((n : ℝ) + 3) * (1 - u) ^ (n + 3) - ((n : ℝ) + 2) * (1 - u) ^ (n + 1) := by
    funext u
    rw [deriv_missingMassTerm (n + 2) (by omega)]
    simp only [show n + 2 - 1 = n + 1 by omega, Nat.cast_add, Nat.cast_ofNat, pow_add]
    ring
  rw [heq, secondDifference_sub, secondDifference_sub,
    secondDifference_const_mul, secondDifference_const_mul, secondDifference_const_mul,
    secondDifference_shifted_pow x h01 h12 n,
    show n + 3 = (n + 1) + 2 by omega, secondDifference_shifted_pow x h01 h12 (n + 1),
    secondDifference_shifted_pow_previous x h01 h12 n]
  simp only [weightedCoefficient, previousHomogeneous3]
  have hd : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- The sum of a scalar statistic in the actual local root coordinates. -/
def localStatistic (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (f : ℝ → ℝ) (c : Triple) : ℝ := ∑ i : Fin 3, f (localRoots x h01 h12 c i)

/-- Chain rule through the actual smooth inverse-root map. -/
theorem hasDerivAt_localStatistic_direction (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (f f' : ℝ → ℝ) (hf : ∀ i, HasDerivAt f (f' (x i)) (x i)) (w : Triple) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 f (symmetricMap x + r • w))
      (∑ i : Fin 3, f' (x i) * (((x i) ^ 2 * w 0 - x i * w 1 + w 2) / rootDenom x i)) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hfi : HasDerivAt f (f' (x i)) (localRoots x h01 h12 (symmetricMap x + (0 : ℝ) • w) i) := by
    simpa using hf i
  exact hfi.comp 0 (hasDerivAt_localRoots_direction x h01 h12 w i)

theorem hasDerivAt_localStatistic_P (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (f f' : ℝ → ℝ) (hf : ∀ i, HasDerivAt f (f' (x i)) (x i)) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 f (symmetricMap x + r • ![0, 0, 1]))
      (secondDifference x f') 0 := by
  simpa [secondDifference, div_eq_mul_inv] using
    hasDerivAt_localStatistic_direction x h01 h12 f f' hf ![0, 0, 1]

theorem hasDerivAt_localStatistic_E (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (f f' : ℝ → ℝ) (hf : ∀ i, HasDerivAt f (f' (x i)) (x i)) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 f (symmetricMap x + r • ![0, 1, 0]))
      (-secondDifference x (fun u => u * f' u)) 0 := by
  convert hasDerivAt_localStatistic_direction x h01 h12 f f' hf ![0, 1, 0] using 1
  unfold secondDifference
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp
  ring

theorem hasDerivAt_localObjective_P (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 (missingMassTerm (n + 2))
      (symmetricMap x + r • ![0, 0, 1]))
      (((n : ℝ) + 3) * weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
        (1 - x 0) (1 - x 1) (1 - x 2) n) 0 := by
  rw [← secondDifference_objective_deriv x h01 h12 n]
  exact hasDerivAt_localStatistic_P x h01 h12 _ _
    (fun i => (hasDerivAt_missingMassTerm (n + 2) (by omega) (x i)).differentiableAt.hasDerivAt)

theorem hasDerivAt_localObjective_E (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) :
    HasDerivAt (fun r : ℝ => localStatistic x h01 h12 (missingMassTerm (n + 2))
      (symmetricMap x + r • ![0, 1, 0]))
      (((n : ℝ) + 3) *
        (weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - x 0) (1 - x 1) (1 - x 2) (n + 1) -
        weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - x 0) (1 - x 1) (1 - x 2) n)) 0 := by
  rw [← neg_secondDifference_mul_objective_deriv x h01 h12 n]
  exact hasDerivAt_localStatistic_E x h01 h12 _ _
    (fun i => (hasDerivAt_missingMassTerm (n + 2) (by omega) (x i)).differentiableAt.hasDerivAt)

end
end EntropyConstrainedMissingMass.TripleGeometry
