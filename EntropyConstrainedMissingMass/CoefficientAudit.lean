import EntropyConstrainedMissingMass.CoefficientComparison

/-! Literal boundary and ratio consequences of the discrete coefficient proof. -/
namespace EntropyConstrainedMissingMass

/-- The sigma exclusion applies to positive indices; b₀=1 has no such implication. -/
theorem coefficientDifference_sigma_lt_two {x y z : ℝ} {N : ℕ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hN : 1 ≤ N)
    (hpos : 0 < coefficientDifference x y z N) : 3 - x - y - z < 2 := by
  have h := coefficientDifference_pos_of_le hx hy hz hpos hN
  rw [coefficientDifference_one] at h
  linarith

/-- The boundary with one zero coordinate has exactly one surviving power. -/
theorem coefficientDifference_one_zero (r : ℝ) (N : ℕ) :
    coefficientDifference r 1 0 N = r ^ N := by
  have heq (k : ℕ) : homogeneous3 r 1 0 k = homogeneous2 r 1 k := by
    cases k <;> simp [homogeneous3, homogeneous2]
  cases N with
  | zero => simp
  | succ N => simp [coefficientDifference, heq, homogeneous2]

/-- The boundary with two coordinates one is the finite geometric sum. -/
theorem coefficientDifference_two_ones_sum (r : ℝ) (N : ℕ) :
    coefficientDifference r 1 1 N = ∑ j ∈ Finset.range (N + 1), r ^ j := by
  rw [coefficientDifference_two_ones, homogeneous2_eq_sum]
  simp

/-- Literal adjacent-ratio monotonicity on the positive initial segment. -/
theorem weightedCoefficient_ratio_strict {β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (n : ℕ)
    (hpos : 0 < weightedCoefficient β x y z (n + 1)) :
    weightedCoefficient β x y z (n + 2) / weightedCoefficient β x y z (n + 1) <
      weightedCoefficient β x y z (n + 1) / weightedCoefficient β x y z n := by
  have hprev := weightedCoefficient_prev_pos (hz.trans (hyz.trans hxy)) (hz.trans hyz) hz hpos
  apply (div_lt_div_iff₀ hpos hprev).mpr
  have h := weightedCoefficient_strict_log_concave hβx hxy hyz hz n hprev
  nlinarith only [h]

end EntropyConstrainedMissingMass
