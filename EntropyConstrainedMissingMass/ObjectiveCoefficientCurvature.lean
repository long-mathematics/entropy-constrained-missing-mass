import EntropyConstrainedMissingMass.RootGeneratingDerivative
import EntropyConstrainedMissingMass.ComparisonSeries

/-! The second objective-variation coefficient, derived by differentiating actual coefficients. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

/-- Extracting the differentiated series gives exactly K k_n − J, including n=0. -/
theorem coeff_curvatureSeries (α β K x y z : ℝ) (n : ℕ) :
    coeff (n + 1) (linearFactor α *
      (C K * X * homogeneousSeries x y z - X ^ 2 * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2)) =
      K * weightedCoefficient α x y z n - comparisonCoefficient α β x y z n := by
  have heq : linearFactor α *
      (C K * X * homogeneousSeries x y z - X ^ 2 * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2) =
      C K * (X * (linearFactor α * homogeneousSeries x y z)) -
        X * (X * (linearFactor α * (linearFactor β) ^ 2 * (homogeneousSeries x y z) ^ 2)) := by ring
  rw [heq, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul,
    coeff_linearFactor_homogeneousSeries]
  cases n with
  | zero => simp [comparisonCoefficient]
  | succ n => rw [coeff_succ_X_mul, comparisonCoefficient_eq_coeff]

namespace TripleGeometry

/-- With β'=−K, differentiation of the stationarity coefficient gives K k_n−J.
All derivative hypotheses concern the actual triple path and its symmetric coordinates. -/
theorem hasDerivAt_stationarityCoefficient {p : ℝ → Triple} {β : ℝ → ℝ} {a m K α : ℝ}
    (hp : DifferentiableAt ℝ p a)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a)
    (hβ : HasDerivAt β (-K) a) (hβa : β a = 1 + m) (n : ℕ) :
    HasDerivAt (fun r =>
      weightedCoefficient α (1 - p r 0) (1 - p r 1) (1 - p r 2) (n + 1) -
        β r * weightedCoefficient α (1 - p r 0) (1 - p r 1) (1 - p r 2) n)
      (K * weightedCoefficient α (1 - p a 0) (1 - p a 1) (1 - p a 2) n -
        comparisonCoefficient α (1 + m) (1 - p a 0) (1 - p a 1) (1 - p a 2) n) a := by
  have hG := hasCoeffDerivAt_complementarySeries hp hS hE hP
  have hB : HasCoeffDerivAt (fun r => linearFactor (β r)) (C K * X) a := by
    have hd := (HasCoeffDerivAt.const 1 a).sub
      ((HasCoeffDerivAt.C hβ).mul (HasCoeffDerivAt.const X a))
    convert hd using 1
    · rfl
    · simp
  have hAG := (HasCoeffDerivAt.const (linearFactor α) a).mul hG
  have hd := hB.mul hAG
  have hseries : HasCoeffDerivAt
      (fun r => linearFactor (β r) * (linearFactor α * complementarySeries (p r)))
      (linearFactor α * (C K * X * complementarySeries (p a) -
        X ^ 2 * (linearFactor (1 + m)) ^ 2 * (complementarySeries (p a)) ^ 2)) a := by
    convert hd using 1
    rw [hβa]
    ring
  have hcoeff := hseries (n + 1)
  dsimp only [complementarySeries] at hcoeff
  rw [coeff_curvatureSeries] at hcoeff
  simpa only [coeff_linearFactor_mul_succ, coeff_linearFactor_homogeneousSeries,
    coeff_homogeneousSeries, weightedCoefficient, previousHomogeneous3] using hcoeff

end TripleGeometry
end
end EntropyConstrainedMissingMass
