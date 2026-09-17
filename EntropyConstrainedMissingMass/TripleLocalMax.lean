import EntropyConstrainedMissingMass.EntropyLevelCurve
import EntropyConstrainedMissingMass.OneSidedVariation
import EntropyConstrainedMissingMass.ObjectivePathDerivatives
import EntropyConstrainedMissingMass.ScalarLocalMax
import EntropyConstrainedMissingMass.CurvatureComparison
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Necessary conditions obtained from actual entropy-preserving embedded triples. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

namespace ProbabilityVector

theorem sum_embedded_coord_le_one {ι : Type*} {n : ℕ} (p : ProbabilityVector ι) (e : Fin n ↪ ι) :
    (∑ i, p.coord (e i)) ≤ 1 := by
  classical
  have h := p.summable_coord.sum_le_tsum (Finset.univ.map e) (fun i _ => p.coord_nonneg i)
  simpa only [Finset.sum_map, p.tsum_coord] using h

end ProbabilityVector
namespace TripleGeometry

theorem localMax_entropyCurve {ι : Type*} {t : ℕ} {h : ℝ}
    (p : ProbabilityVector ι) (hp : ProbabilityVector.LocalMaximizer t h p)
    (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2)) :
    IsLocalMax (fun r => ∑ i, missingMassTerm t
      (entropyCurve (fun i => p.coord (e i)) h0 h01 h12 r i)) 0 := by
  let x : Triple := fun i => p.coord (e i)
  let v := entropyCurve x h0 h01 h12
  apply ProbabilityVector.localMax_of_embedded_path p hp e v 0
  · intro i
    exact congrFun (entropyCurve_zero x h0 h01 h12) i
  · intro i
    have ht : Tendsto v (𝓝 0) (𝓝 x) := by
      simpa [v] using (contDiffAt_entropyCurve x h0 h01 h12).continuousAt.tendsto
    exact tendsto_pi_nhds.mp ht i
  · filter_upwards [eventually_entropyCurve_derivatives x h0 h01 h12,
      eventually_entropyCurve_symmetric x h0 h01 h12] with r hr hs
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · exact hr.2.1.le
      · exact (hr.2.1.trans hr.2.2.1).le
      · exact (hr.2.1.trans (hr.2.2.1.trans hr.2.2.2.1)).le
    · have he := congrFun hs 0
      simpa [v, x, symmetricMap, Fin.sum_univ_succ, add_assoc] using he
  · filter_upwards [eventually_entropyCurve_entropy x h0 h01 h12] with r hr
    exact le_of_eq hr

/-- Stationarity is a consequence of actual ℓ¹ local maximality, even with slack entropy. -/
theorem objective_stationary_of_localMax {ι : Type*} {t : ℕ} {h : ℝ}
    (p : ProbabilityVector ι) (hp : ProbabilityVector.LocalMaximizer t h p)
    (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2))
    (ht : 1 ≤ t) :
    -secondDifference (fun i => p.coord (e i)) (fun u => u * deriv (missingMassTerm t) u) -
      Curvature.m (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2)) *
        secondDifference (fun i => p.coord (e i)) (deriv (missingMassTerm t)) = 0 := by
  let x : Triple := fun i => p.coord (e i)
  obtain ⟨hd, _, ho1, ho2, hS, hE, hP⟩ :=
    (eventually_entropyCurve_derivatives x h0 h01 h12).self_of_nhds
  have hdF := hasDerivAt_objective_path_difference hd ho1 ho2 hS hE hP t ht
  have hz := (localMax_entropyCurve p hp e h0 h01 h12).hasDerivAt_eq_zero hdF
  simpa only [entropyCurve_zero] using hz

/-- Strict positivity of the product derivative at an actual local maximum. -/
theorem objective_P_pos_of_localMax {ι : Type*} {t : ℕ} {h : ℝ}
    (p : ProbabilityVector ι) (hp : ProbabilityVector.LocalMaximizer t h p)
    (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2))
    (ht : 2 ≤ t) :
    0 < secondDifference (fun i => p.coord (e i)) (deriv (missingMassTerm t)) := by
  have hsum := p.sum_embedded_coord_le_one e
  simp [Fin.sum_univ_succ] at hsum
  apply objective_P_pos_of_stationary _ h01 h12 (by linarith) t ht
    (Curvature.m (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2)))
  · exact objective_P_nonneg_of_localMax p hp e h0 h01 h12 (by omega)
  · exact objective_stationary_of_localMax p hp e h0 h01 h12 (by omega)

/-- At sample size one a local maximum cannot contain three distinct positive sizes. -/
theorem not_localMax_three_sizes_one {ι : Type*} {h : ℝ}
    (p : ProbabilityVector ι) (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2)) :
    ¬ ProbabilityVector.LocalMaximizer 1 h p := by
  intro hp
  have hs := objective_stationary_of_localMax p hp e h0 h01 h12 (by omega)
  rw [neg_secondDifference_mul_deriv_one _ h01 h12,
    secondDifference_deriv_one _ h01 h12] at hs
  norm_num at hs

/-- The exact second derivative of the objective along the constructed entropy curve. -/
theorem hasDerivAt_deriv_objective_entropyCurve (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) (n : ℕ) :
    HasDerivAt (deriv (fun r => ∑ i, missingMassTerm (n + 2) (entropyCurve x h0 h01 h12 r i)))
      (((n : ℝ) + 3) *
        (Curvature.K (x 0) (x 1) (x 2) *
          weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3)) (1 - x 0) (1 - x 1) (1 - x 2) n -
          comparisonCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
            (1 + Curvature.m (x 0) (x 1) (x 2)) (1 - x 0) (1 - x 1) (1 - x 2) n)) 0 := by
  have hpath := (eventually_entropyCurve_derivatives x h0 h01 h12).mono
    (fun _ hr => And.intro hr.1 hr.2.2)
  simpa only [entropyCurve_zero] using
    hasDerivAt_deriv_objective_path hpath (hasDerivAt_entropyCurve_m x h0 h01 h12) n

/-- The second-order necessary condition follows in the original ℓ¹ feasible set. -/
theorem objective_curvature_nonpos_of_localMax {ι : Type*} {h : ℝ}
    (p : ProbabilityVector ι) (n : ℕ) (hp : ProbabilityVector.LocalMaximizer (n + 2) h p)
    (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2)) :
    Curvature.K (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2)) *
        weightedCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
          (1 - p.coord (e 0)) (1 - p.coord (e 1)) (1 - p.coord (e 2)) n -
      comparisonCoefficient (((n : ℝ) + 2) / ((n : ℝ) + 3))
        (1 + Curvature.m (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2)))
        (1 - p.coord (e 0)) (1 - p.coord (e 1)) (1 - p.coord (e 2)) n ≤ 0 := by
  let x : Triple := fun i => p.coord (e i)
  have hfirst := (eventually_entropyCurve_derivatives x h0 h01 h12).self_of_nhds
  have hd := hasDerivAt_objective_path hfirst.1 hfirst.2.2.1 hfirst.2.2.2.1
    hfirst.2.2.2.2.1 hfirst.2.2.2.2.2.1 hfirst.2.2.2.2.2.2 n
  have hle := second_derivative_nonpos_of_localMax hd.continuousAt
    (localMax_entropyCurve p hp e h0 h01 h12)
  rw [(hasDerivAt_deriv_objective_entropyCurve x h0 h01 h12 n).deriv] at hle
  dsimp [x] at hle
  nlinarith [show (0 : ℝ) < (n : ℝ) + 3 by positivity]

/-- The remaining analytic input is solely the sharp curvature inequality, not a variational premise. -/
theorem not_localMax_three_sizes_of_curvature_bound {ι : Type*} {h : ℝ}
    (p : ProbabilityVector ι) (n : ℕ) (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2))
    (hK : 16 / (15 * (p.coord (e 0) + p.coord (e 1) + p.coord (e 2) +
      Curvature.m (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2)))) ≤
        Curvature.K (p.coord (e 0)) (p.coord (e 1)) (p.coord (e 2))) :
    ¬ ProbabilityVector.LocalMaximizer (n + 2) h p := by
  intro hp
  let x : Triple := fun i => p.coord (e i)
  let α : ℝ := ((n : ℝ) + 2) / ((n : ℝ) + 3)
  let m := Curvature.m (x 0) (x 1) (x 2)
  have hS : x 0 + x 1 + x 2 ≤ 1 := by
    have hh := p.sum_embedded_coord_le_one e
    simpa [x, Fin.sum_univ_succ, add_assoc] using hh
  have hx2 : x 2 < 1 := by dsimp [x] at *; linarith
  have hm : 0 < m := Curvature.m_pos _ _ _ h0 (h0.trans h01) (h0.trans (h01.trans h12))
  have hk : 0 < weightedCoefficient α (1 - x 0) (1 - x 1) (1 - x 2) n := by
    have hr := objective_P_pos_of_localMax p hp e h0 h01 h12 (by omega)
    rw [secondDifference_objective_deriv _ h01 h12] at hr
    exact (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < (n : ℝ) + 3)).mp hr
  have hstat : weightedCoefficient α (1 - x 0) (1 - x 1) (1 - x 2) (n + 1) =
      (1 + m) * weightedCoefficient α (1 - x 0) (1 - x 1) (1 - x 2) n := by
    have hr := objective_stationary_of_localMax p hp e h0 h01 h12 (by omega)
    rw [neg_secondDifference_mul_objective_deriv _ h01 h12,
      secondDifference_objective_deriv _ h01 h12] at hr
    dsimp [α, m, x]
    nlinarith [show (0 : ℝ) < (n : ℝ) + 3 by positivity]
  have hgap := coefficient_curvature_gap h0 h01 h12 hx2 hS hm (show 0 < α by positivity)
    n hk hstat hK
  have hnonpos := objective_curvature_nonpos_of_localMax p n hp e h0 h01 h12
  have hpos : 0 < weightedCoefficient α (1 - x 0) (1 - x 1) (1 - x 2) n /
      (15 * (x 0 + x 1 + x 2 + m)) := div_pos hk (by change 0 < 15 * (p.coord (e 0) + p.coord (e 1) + p.coord (e 2) + m); linarith)
  exact (not_lt_of_ge hnonpos) (hpos.trans hgap)

end TripleGeometry
end
end EntropyConstrainedMissingMass
