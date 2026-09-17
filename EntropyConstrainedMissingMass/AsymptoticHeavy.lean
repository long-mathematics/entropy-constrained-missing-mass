import EntropyConstrainedMissingMass.AsymptoticReciprocalUpper
import Mathlib.Analysis.SpecificLimits.Normed

/-! A uniform lower bound for the global value and eventual exclusion of light maximizers. -/

open Filter Set
open scoped Topology
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The value is bounded below by an explicit positive multiple of 1/log t. -/
theorem asymptotic_value_lower (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, 0 < optimalValue t h ∧ h / (3 * Real.log t) ≤ optimalValue t h := by
  obtain ⟨C, hC, hu⟩ := asymptotic_reciprocal_upper h hh
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hu, hT.eventually_ge_atTop (C + 2), hT.eventually_ge_atTop 1] with t hu hlarge hT1
  have hTp : 0 < Real.log t := by linarith
  have hlog : Real.log (Real.log t) ≤ Real.log t :=
    (Real.log_le_sub_one_of_pos hTp).trans (by linarith)
  have hratio : Real.log (Real.log t) / Real.log t ≤ 1 := (div_le_one hTp).mpr hlog
  have hCbound := mul_le_mul_of_nonneg_left hratio hC.le
  have hupper : h / optimalValue t h ≤ 3 * Real.log t := by
    nlinarith only [hu.2, hCbound, hlarge, hlog]
  refine ⟨hu.1, (div_le_iff₀ (by positivity : 0 < 3 * Real.log t)).mpr ?_⟩
  have hr := (div_le_iff₀ hu.1).mp hupper
  nlinarith only [hr]

/-- A fixed atom's missing-mass contribution decays faster than 1/t, including zero atoms. -/
theorem tendsto_nat_mul_missingMassTerm (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Tendsto (fun t : ℕ => (t : ℝ) * missingMassTerm t u) atTop (𝓝 0) := by
  by_cases hu : u = 0
  · simp only [hu, missingMassTerm, zero_mul, mul_zero]
    exact tendsto_const_nhds
  have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  have hr : ‖1 - u‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have hl := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.tendsto_atTop_zero
  have hc := tendsto_const_nhds.mul hl (a := u)
  convert hc using 1
  · funext t
    unfold missingMassTerm
    ring
  · simp

namespace ProbabilityVector
variable {ι : Type*}

/-- A fixed law on a finite alphabet has objective o(1/t). -/
theorem tendsto_nat_mul_objective_finite [Fintype ι] (p : ProbabilityVector ι) :
    Tendsto (fun t : ℕ => (t : ℝ) * p.objective t) atTop (𝓝 0) := by
  have he (t : ℕ) : (t : ℝ) * p.objective t =
      ∑ i : ι, (t : ℝ) * missingMassTerm t (p.coord i) := by
    rw [objective, tsum_fintype, Finset.mul_sum]
  simp_rw [he]
  convert tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_nat_mul_missingMassTerm (p.coord i) (p.coord_nonneg i) (p.coord_le_one i)) using 1
  simp

end ProbabilityVector

/-- The single fixed light/uniform candidate decays faster than 1/t. -/
theorem tendsto_nat_mul_lightValue (h : ℝ) (hh : 0 < h) :
    Tendsto (fun t : ℕ => (t : ℝ) * lightValue t h) atTop (𝓝 0) := by
  have he := (candidateVector (entropySupportIndex h) (lightRoot h)
    (entropySupportIndex_pos hh.le) (lightRoot_mem hh)).tendsto_nat_mul_objective_finite
  simpa only [objective_candidateVector, lightValue] using he

/-- Eventually the light candidate is strictly suboptimal, so all its ties are excluded too. -/
theorem lightValue_eventually_lt_optimalValue (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, lightValue t h < optimalValue t h := by
  have hsmall := (tendsto_nat_mul_lightValue h hh).eventually_lt_const (by positivity : 0 < h / 3)
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [asymptotic_value_lower h hh, hsmall, hT.eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with t hlow hsmall hlog ht
  have htpos : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogle : Real.log t ≤ (t : ℝ) := (Real.log_le_sub_one_of_pos htpos).trans (by linarith)
  have hv : 0 ≤ lightValue t h := by
    rw [← objective_canonicalLight t hh]
    exact (canonicalLight h hh).objective_nonneg t
  have hmul := mul_le_mul_of_nonneg_right hlogle hv
  have hcomp : lightValue t h < h / (3 * Real.log t) := by
    apply (lt_div_iff₀ (by positivity)).mpr
    nlinarith only [hmul, hsmall]
  exact hcomp.trans_le hlow.2

namespace ProbabilityVector
variable {ι : Type*} [Countable ι] [Infinite ι]

/-- Uniform in the choice of a global maximizer: every one is eventually a heavy candidate. -/
theorem globalMax_eventually_heavy (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, ∀ p : ProbabilityVector ι,
      p ∈ Feasible h → (∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) →
      HeavyCandidateForm h p := by
  filter_upwards [lightValue_eventually_lt_optimalValue h hh, eventually_ge_atTop (1 : ℕ)] with t ht ht1
  intro p hp hmax
  rcases p.candidate_complete_of_globalMax ht1 hh hp hmax with hl | hr
  · have he := optimalValue_eq_of_globalMax p t hp hmax
    have hv := hl.objective_eq_lightValue hh t
    rw [he, hv] at ht
    exact (lt_irrefl _ ht).elim
  · exact hr

end ProbabilityVector
end
end EntropyConstrainedMissingMass
