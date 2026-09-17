import EntropyConstrainedMissingMass.EmbeddedPerturbation
import EntropyConstrainedMissingMass.EntropyHessian
import EntropyConstrainedMissingMass.DividedDifferences
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The fixed-E, decreasing-P variation is feasible in the original entropy constraint. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

/-- A positive derivative makes nearby points on the left have smaller values. -/
theorem eventually_lt_left_of_hasDerivAt_pos {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : 0 < d) : ∀ᶠ r in 𝓝[<] a, f r < f a := by
  have hs := ((hasDerivAt_iff_tendsto_slope_left_right.mp hf).1).eventually (Ioi_mem_nhds hd)
  filter_upwards [hs, eventually_mem_nhdsWithin] with r hr hra
  rw [slope_def_field] at hr
  have hden : r - a < 0 := sub_neg.mpr hra
  have := (div_pos_iff.mp hr).resolve_left (by intro h; linarith [h.2])
  linarith [this.1]

/-- A left local maximum has nonnegative two-sided derivative. -/
theorem derivative_nonneg_of_localMax_left {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hmax : IsLocalMaxOn f (Iio a) a) : 0 ≤ d := by
  apply ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  filter_upwards [hmax, eventually_mem_nhdsWithin] with r hr hra
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr hr) (sub_nonpos.mpr (le_of_lt hra))

namespace TripleGeometry

/-- Vary the product coordinate while keeping the sum and pair sum fixed. -/
def productPath (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (r : ℝ) : Triple :=
  localRoots x h01 h12 (symmetricMap x + r • ![0, 0, 1])

@[simp] theorem productPath_zero (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    productPath x h01 h12 0 = x := by simp [productPath]

theorem tendsto_productPath (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    Tendsto (productPath x h01 h12) (𝓝 0) (𝓝 x) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa [productPath] using (hasDerivAt_localRoots_P x h01 h12 i).continuousAt.tendsto

theorem eventually_productPath_positive_sum (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in 𝓝 0, (∀ i, 0 < productPath x h01 h12 r i) ∧
      ∑ i, productPath x h01 h12 r i = ∑ i, x i := by
  have hc : Tendsto (fun r : ℝ => symmetricMap x + r • ![0, 0, 1]) (𝓝 0) (𝓝 (symmetricMap x)) := by
    simpa using tendsto_const_nhds.add ((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).smul_const (![0, 0, 1] : Triple))
  filter_upwards [hc.eventually (eventually_localRoots_positive_ordered x h0 h01 h12),
    hc.eventually (eventually_localRoots_right_inverse x h01 h12)] with r hr hi
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · exact hr.1
    · exact hr.1.trans hr.2.1
    · exact hr.1.trans (hr.2.1.trans hr.2.2)
  ·
    have hs := congrFun hi 0
    simpa [symmetricMap, productPath, Fin.sum_univ_succ, add_assoc] using hs

/-- The entropy of the selected coordinates strictly decreases on the left product path. -/
theorem eventually_productPath_entropy_lt (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in 𝓝[<] 0, (∑ i, Real.negMulLog (productPath x h01 h12 r i)) <
      ∑ i, Real.negMulLog (x i) := by
  have h := eventually_lt_left_of_hasDerivAt_pos (hasDerivAt_localEntropy_P x h0 h01 h12)
    (Curvature.I0_pos (x 0) (x 1) (x 2) h0 (h0.trans h01) (h0.trans (h01.trans h12)))
  simpa [localEntropy, tripleEntropy, productPath] using h

/-- The product derivative is nonnegative at an actual entropy-constrained local maximum.
This uses the selected atoms of an arbitrary probability vector, without finite support. -/
theorem objective_P_nonneg_of_localMax {ι : Type*} {t : ℕ} {h : ℝ}
    (p : ProbabilityVector ι) (hp : ProbabilityVector.LocalMaximizer t h p)
    (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2))
    (ht : 1 ≤ t) :
    0 ≤ secondDifference (fun i => p.coord (e i)) (deriv (missingMassTerm t)) := by
  let x : Triple := fun i => p.coord (e i)
  let v : ℝ → Triple := productPath x h01 h12
  have hlim : ∀ i, Tendsto (fun r => v r i) (𝓝[<] 0) (𝓝 (p.coord (e i))) := by
    intro i
    exact ((tendsto_pi_nhds.mp (tendsto_productPath x h01 h12)) i).mono_left nhdsWithin_le_nhds
  have hgood : ∀ᶠ r in 𝓝[<] 0, (∀ i, 0 ≤ v r i) ∧ ∑ i, v r i = ∑ i, p.coord (e i) := by
    filter_upwards [(eventually_productPath_positive_sum x h0 h01 h12).filter_mono nhdsWithin_le_nhds] with r hr
    exact ⟨fun i => (hr.1 i).le, hr.2⟩
  have hent : ∀ᶠ r in 𝓝[<] 0, (∑ i, Real.negMulLog (v r i)) ≤ ∑ i, Real.negMulLog (p.coord (e i)) :=
    (eventually_productPath_entropy_lt x h0 h01 h12).mono (fun _ hr => hr.le)
  have hmax := ProbabilityVector.localMaxOn_of_embedded_path p hp e v 0 (Iio 0)
    (fun i => congrFun (productPath_zero x h01 h12) i) hlim hgood hent
  apply derivative_nonneg_of_localMax_left _ hmax
  exact hasDerivAt_localStatistic_P x h01 h12 _ _
    (fun i => (hasDerivAt_missingMassTerm t ht (x i)).differentiableAt.hasDerivAt)

end TripleGeometry
end
end EntropyConstrainedMissingMass
