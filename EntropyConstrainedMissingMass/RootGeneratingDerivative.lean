import EntropyConstrainedMissingMass.PowerSeriesCalculus
import EntropyConstrainedMissingMass.TripleGeometry

/-! Actual differentiation of the complementary-root generating function at fixed sum. -/

namespace EntropyConstrainedMissingMass.TripleGeometry
noncomputable section
open PowerSeries

def complementarySeries (x : Triple) : PowerSeries ℝ :=
  homogeneousSeries (1 - x 0) (1 - x 1) (1 - x 2)

def denominatorSeries (c : Triple) : PowerSeries ℝ :=
  1 - C (3 - c 0) * X + C (3 - 2 * c 0 + c 1) * X ^ 2 -
    C (1 - c 0 + c 1 - c 2) * X ^ 3

theorem denominatorSeries_eq_product (x : Triple) :
    denominatorSeries (symmetricMap x) =
      linearFactor (1 - x 0) * linearFactor (1 - x 1) * linearFactor (1 - x 2) := by
  have hC2 : (C (2 : ℝ) : PowerSeries ℝ) = 2 := by
    calc
      C (2 : ℝ) = C (1 + 1 : ℝ) := congrArg C (by norm_num)
      _ = 2 := by rw [map_add]; simp; ring
  have hC3 : (C (3 : ℝ) : PowerSeries ℝ) = 3 := by
    calc
      C (3 : ℝ) = C (1 + 1 + 1 : ℝ) := congrArg C (by norm_num)
      _ = 3 := by rw [map_add, map_add]; simp; ring
  simp [denominatorSeries, symmetricMap, linearFactor, map_add, map_sub, map_mul, hC2, hC3]
  ring

theorem denominatorSeries_mul_complementarySeries (x : Triple) :
    denominatorSeries (symmetricMap x) * complementarySeries x = 1 := by
  rw [denominatorSeries_eq_product]
  exact product_linearFactor_mul_homogeneousSeries _ _ _

/-- The denominator's coefficientwise derivative for arbitrary symmetric-coordinate velocities. -/
theorem hasCoeffDerivAt_denominatorSeries {c : ℝ → Triple} {a dS dE dP : ℝ}
    (hS : HasDerivAt (fun r => c r 0) dS a)
    (hE : HasDerivAt (fun r => c r 1) dE a)
    (hP : HasDerivAt (fun r => c r 2) dP a) :
    HasCoeffDerivAt (fun r => denominatorSeries (c r))
      (C dS * X + C (-2 * dS + dE) * X ^ 2 - C (-dS + dE - dP) * X ^ 3) a := by
  have h1 := (HasCoeffDerivAt.C (hS.const_sub 3)).mul (HasCoeffDerivAt.const X a)
  have h2 := (HasCoeffDerivAt.C (((hS.const_mul 2).const_sub 3).add hE)).mul (HasCoeffDerivAt.const (X ^ 2) a)
  have h3 := (HasCoeffDerivAt.C (((hS.const_sub 1).add hE).sub hP)).mul (HasCoeffDerivAt.const (X ^ 3) a)
  have hd := (((HasCoeffDerivAt.const 1 a).sub h1).add h2).sub h3
  convert hd using 1
  · rfl
  · simp only [mul_zero, add_zero, zero_sub, map_neg, neg_mul, neg_neg]

/-- Along a fixed-S path with E'=1 and P'=-m, G'=-w²(1-(1+m)w)G². -/
theorem hasCoeffDerivAt_complementarySeries {p : ℝ → Triple} {a m : ℝ}
    (hp : DifferentiableAt ℝ p a)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a) :
    HasCoeffDerivAt (fun r => complementarySeries (p r))
      (-(X ^ 2 * linearFactor (1 + m)) * (complementarySeries (p a)) ^ 2) a := by
  have hq : DifferentiableAt ℝ (fun r => fun i : Fin 3 => 1 - p r i) a := by
    apply differentiableAt_pi.mpr
    intro i
    exact ((differentiableAt_apply i (p a)).comp a hp).const_sub 1
  obtain ⟨DG, hG⟩ := exists_hasCoeffDerivAt_homogeneousSeries (fun r i => 1 - p r i) hq
  have hQ := hasCoeffDerivAt_denominatorSeries hS hE hP
  have hder : DG = -(X ^ 2 * linearFactor (1 + m)) * (complementarySeries (p a)) ^ 2 := by
    have h := hQ.of_inverse hG (Filter.Eventually.of_forall (fun r => denominatorSeries_mul_complementarySeries (p r)))
    convert h using 1
    simp [complementarySeries, linearFactor, map_add]
    ring
  rw [← hder]
  exact hG

end
end EntropyConstrainedMissingMass.TripleGeometry
