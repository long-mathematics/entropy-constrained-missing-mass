import EntropyConstrainedMissingMass.ObjectiveStationarity
import EntropyConstrainedMissingMass.ObjectiveCoefficientCurvature
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! First and second derivatives of the actual finite-coordinate objective along
paths with the entropy-curve symmetric velocities. -/

namespace EntropyConstrainedMissingMass.TripleGeometry
noncomputable section
open Filter
open scoped Topology

/-- Root velocities forced by the actual symmetric-coordinate path derivatives. -/
theorem root_velocity_of_symmetric_path {p : ℝ → Triple} {a m : ℝ}
    (hp : DifferentiableAt ℝ p a) (h01 : p a 0 < p a 1) (h12 : p a 1 < p a 2)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a) (i : Fin 3) :
    deriv p a i = (-(p a i) - m) / rootDenom (p a) i := by
  have hc := (hasFDerivAt_symmetricMap (p a)).comp_hasDerivAt a hp.hasDerivAt
  have h0 := (hasDerivAt_pi.mp hc 0).unique hS
  have h1 := (hasDerivAt_pi.mp hc 1).unique hE
  have h2 := (hasDerivAt_pi.mp hc 2).unique hP
  have hd := rootDenom_mul_eq_differential (p a) (deriv p a) i
  rw [h0, h1, h2] at hd
  apply (eq_div_iff (rootDenom_ne_zero (p a) h01 h12 i)).mpr
  nlinarith only [hd]

/-- The scalar objective derivative equals the actual root divided-difference expression. -/
theorem hasDerivAt_objective_path_difference {p : ℝ → Triple} {a m : ℝ}
    (hp : DifferentiableAt ℝ p a) (h01 : p a 0 < p a 1) (h12 : p a 1 < p a 2)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a) (t : ℕ) (ht : 1 ≤ t) :
    HasDerivAt (fun r => ∑ i : Fin 3, missingMassTerm t (p r i))
      (-secondDifference (p a) (fun u => u * deriv (missingMassTerm t) u) -
        m * secondDifference (p a) (deriv (missingMassTerm t))) a := by
  have hd (i : Fin 3) : HasDerivAt (fun r => missingMassTerm t (p r i))
      (deriv (missingMassTerm t) (p a i) * ((-(p a i) - m) / rootDenom (p a) i)) a := by
    have hpi := hasDerivAt_pi.mp hp.hasDerivAt i
    rw [root_velocity_of_symmetric_path hp h01 h12 hS hE hP] at hpi
    exact (hasDerivAt_missingMassTerm t ht (p a i)).differentiableAt.hasDerivAt.comp a hpi
  convert HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i) using 1
  unfold secondDifference
  rw [← Finset.sum_neg_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The manuscript's first variation D_t is an actual derivative of the objective path. -/
theorem hasDerivAt_objective_path {p : ℝ → Triple} {a m : ℝ}
    (hp : DifferentiableAt ℝ p a) (h01 : p a 0 < p a 1) (h12 : p a 1 < p a 2)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a) (n : ℕ) :
    HasDerivAt (fun r => ∑ i : Fin 3, missingMassTerm (n + 2) (p r i))
      (((n : ℝ) + 3) *
        (weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - p a 0) (1 - p a 1) (1 - p a 2) (n + 1) -
        (1 + m) * weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - p a 0) (1 - p a 1) (1 - p a 2) n)) a := by
  have hd := hasDerivAt_objective_path_difference hp h01 h12 hS hE hP (n + 2) (by omega)
  rw [neg_secondDifference_mul_objective_deriv (p a) h01 h12,
    secondDifference_objective_deriv (p a) h01 h12] at hd
  convert hd using 1
  ring

theorem hasDerivAt_objective_one_path {p : ℝ → Triple} {a m : ℝ}
    (hp : DifferentiableAt ℝ p a) (h01 : p a 0 < p a 1) (h12 : p a 1 < p a 2)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hP : HasDerivAt (fun r => symmetricMap (p r) 2) (-m) a) :
    HasDerivAt (fun r => ∑ i : Fin 3, missingMassTerm 1 (p r i)) 2 a := by
  simpa only [neg_secondDifference_mul_deriv_one (p a) h01 h12,
    secondDifference_deriv_one (p a) h01 h12, mul_zero, sub_zero] using
    hasDerivAt_objective_path_difference hp h01 h12 hS hE hP 1 (by omega)

/-- Actual second derivative along a locally differentiable path with β'=−K.
The hypotheses are supplied by the entropy-level-curve construction. -/
theorem hasDerivAt_deriv_objective_path {p : ℝ → Triple} {m : ℝ → ℝ} {a K : ℝ}
    (hpath : ∀ᶠ r in 𝓝 a, DifferentiableAt ℝ p r ∧ p r 0 < p r 1 ∧ p r 1 < p r 2 ∧
      HasDerivAt (fun u => symmetricMap (p u) 0) 0 r ∧
      HasDerivAt (fun u => symmetricMap (p u) 1) 1 r ∧
      HasDerivAt (fun u => symmetricMap (p u) 2) (-(m r)) r)
    (hm : HasDerivAt m (-K) a) (n : ℕ) :
    HasDerivAt (deriv (fun r => ∑ i : Fin 3, missingMassTerm (n + 2) (p r i)))
      (((n : ℝ) + 3) *
        (K * weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - p a 0) (1 - p a 1) (1 - p a 2) n -
        comparisonCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3)) (1 + m a)
          (1 - p a 0) (1 - p a 1) (1 - p a 2) n)) a := by
  obtain ⟨hp, h01, h12, hS, hE, hP⟩ := hpath.self_of_nhds
  have hβ : HasDerivAt (fun r => 1 + m r) (-K) a := hm.const_add 1
  have hd := (hasDerivAt_stationarityCoefficient (α := ((n : ℝ) + 2) / ((n : ℝ) + 3)) hp hS hE hP hβ rfl n).const_mul ((n : ℝ) + 3)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hpath] with r hr
  exact (hasDerivAt_objective_path hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2 n).deriv

end
end EntropyConstrainedMissingMass.TripleGeometry
