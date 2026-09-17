import EntropyConstrainedMissingMass.CoefficientComparison

/-! The strict quantitative contradiction from the coefficient and curvature estimates.
The analytic curvature estimate and the variational identities are explicit inputs here. -/

namespace EntropyConstrainedMissingMass

theorem comparison_constant_le_entropy_recip {S m : ℝ}
    (hS : 0 < S) (hS1 : S ≤ 1) (hm : 0 ≤ m) :
    max (1 / (1 + m)) (1 / (S + 3 * m)) ≤ 1 / (S + m) := by
  apply max_le
  · exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The manuscript's positive-curvature gap, before multiplication by t+1. -/
theorem coefficient_curvature_gap {α x y z m K : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (_hz : z < 1)
    (hS1 : x + y + z ≤ 1) (hm : 0 < m) (hα : 0 < α) (n : ℕ)
    (hk : 0 < weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hstat : weightedCoefficient α (1 - x) (1 - y) (1 - z) (n + 1) =
      (1 + m) * weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hK : 16 / (15 * (x + y + z + m)) ≤ K) :
    weightedCoefficient α (1 - x) (1 - y) (1 - z) n / (15 * (x + y + z + m)) <
      K * weightedCoefficient α (1 - x) (1 - y) (1 - z) n -
        comparisonCoefficient α (1 + m) (1 - x) (1 - y) (1 - z) n := by
  have hS : 0 < x + y + z := by linarith
  have hsm : 0 < x + y + z + m := by positivity
  have hcmp := coefficient_comparison (by linarith : 1 - x < 1 + m)
    (by linarith : 1 - y < 1 - x) (by linarith : 1 - z < 1 - y)
    (by linarith : 0 < 1 - z) hα n hk (by rw [hstat])
  have hden : 3 * (1 + m) - (1 - x) - (1 - y) - (1 - z) = x + y + z + 3 * m := by ring
  rw [hden] at hcmp
  have hmax := comparison_constant_le_entropy_recip hS hS1 hm.le
  have hJ := hcmp.trans_le (mul_le_mul_of_nonneg_right hmax hk.le)
  have hmul := mul_le_mul_of_nonneg_right hK hk.le
  have hid : 16 / (15 * (x + y + z + m)) *
        weightedCoefficient α (1 - x) (1 - y) (1 - z) n -
      (1 / (x + y + z + m)) * weightedCoefficient α (1 - x) (1 - y) (1 - z) n =
      weightedCoefficient α (1 - x) (1 - y) (1 - z) n / (15 * (x + y + z + m)) := by
    field_simp
    ring
  linarith

/-- The ratio form printed in the paper follows without dropping strictness. -/
theorem coefficient_curvature_ratio_gap {α x y z m K : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (hz : z < 1)
    (hS1 : x + y + z ≤ 1) (hm : 0 < m) (hα : 0 < α) (n : ℕ)
    (hk : 0 < weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hstat : weightedCoefficient α (1 - x) (1 - y) (1 - z) (n + 1) =
      (1 + m) * weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hK : 16 / (15 * (x + y + z + m)) ≤ K) :
    1 / (15 * (x + y + z + m)) < K -
      comparisonCoefficient α (1 + m) (1 - x) (1 - y) (1 - z) n /
        weightedCoefficient α (1 - x) (1 - y) (1 - z) n := by
  have h := div_lt_div_of_pos_right
    (coefficient_curvature_gap hx hxy hyz hz hS1 hm hα n hk hstat hK) hk
  simpa only [sub_div, div_right_comm, div_self (ne_of_gt hk), mul_div_cancel_right₀ _ (ne_of_gt hk)] using h

/-- The stronger bound R/(20S) uses the previously proved mean constraint. -/
theorem coefficient_curvature_twentieth_gap {α x y z m K : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z) (hz : z < 1)
    (hS1 : x + y + z ≤ 1) (hm : 0 < m) (hmS : m ≤ (x + y + z) / 3)
    (hα : 0 < α) (n : ℕ)
    (hk : 0 < weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hstat : weightedCoefficient α (1 - x) (1 - y) (1 - z) (n + 1) =
      (1 + m) * weightedCoefficient α (1 - x) (1 - y) (1 - z) n)
    (hK : 16 / (15 * (x + y + z + m)) ≤ K) :
    1 / (20 * (x + y + z)) < K -
      comparisonCoefficient α (1 + m) (1 - x) (1 - y) (1 - z) n /
        weightedCoefficient α (1 - x) (1 - y) (1 - z) n := by
  have hS : 0 < x + y + z := by linarith
  have hrec : 1 / (20 * (x + y + z)) ≤ 1 / (15 * (x + y + z + m)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact hrec.trans_lt (coefficient_curvature_ratio_gap hx hxy hyz hz hS1 hm hα n hk hstat hK)

end EntropyConstrainedMissingMass
