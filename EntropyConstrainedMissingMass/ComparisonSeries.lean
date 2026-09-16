import EntropyConstrainedMissingMass.CoefficientGeneratingFunctions
import EntropyConstrainedMissingMass.CoefficientComparison

/-! The finite convolution comparison is exactly the formal power-series coefficient in §3. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

theorem coeff_two_linearFactor_homogeneousSeries (α β x y z : ℝ) (n : ℕ) :
    coeff n (linearFactor β * (linearFactor α * homogeneousSeries x y z)) =
      comparisonAuxCoefficient α β x y z n := by
  cases n with
  | zero => simp [coeff_linearFactor_mul_zero]
  | succ n =>
    simp [coeff_linearFactor_mul_succ, coeff_linearFactor_homogeneousSeries,
      comparisonAuxCoefficient, previousWeightedCoefficient, weightedCoefficient, previousHomogeneous3]

/-- The natural coefficient `n` equals the paper's `J` with comparison index `n+1`. -/
theorem comparisonCoefficient_eq_coeff (α β x y z : ℝ) (n : ℕ) :
    comparisonCoefficient α β x y z (n + 1) =
      coeff n (linearFactor α * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2) := by
  have heq : linearFactor α * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2 =
      (linearFactor β * (linearFactor α * homogeneousSeries x y z)) *
        (linearFactor β * homogeneousSeries x y z) := by ring
  rw [heq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_two_linearFactor_homogeneousSeries, coeff_linearFactor_homogeneousSeries,
    comparisonCoefficient, Nat.add_sub_cancel]

/-- A formal-series coefficient with the manuscript's negative-index convention. -/
def comparisonSeriesCoefficient (α β x y z : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => coeff n (linearFactor α * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2)

theorem comparisonSeriesCoefficient_eq (α β x y z : ℝ) (n : ℕ) :
    comparisonSeriesCoefficient α β x y z n = comparisonCoefficient α β x y z n := by
  cases n with
  | zero => simp [comparisonSeriesCoefficient, comparisonCoefficient]
  | succ n => exact (comparisonCoefficient_eq_coeff α β x y z n).symm

/-- Manuscript-facing comparison, including the zero coefficient at negative index. -/
theorem coefficient_comparison_series {α β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (hα : 0 < α)
    (n : ℕ) (hkn : 0 < weightedCoefficient α x y z n)
    (hstep : β * weightedCoefficient α x y z n ≤ weightedCoefficient α x y z (n + 1)) :
    comparisonSeriesCoefficient α β x y z n <
      max (1 / β) (1 / (3 * β - x - y - z)) * weightedCoefficient α x y z n := by
  rw [comparisonSeriesCoefficient_eq]
  exact coefficient_comparison hβx hxy hyz hz hα n hkn hstep

end
end EntropyConstrainedMissingMass
