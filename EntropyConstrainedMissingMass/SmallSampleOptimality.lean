import EntropyConstrainedMissingMass.SmallSampleVariation
import EntropyConstrainedMissingMass.FiniteClassification

/-! Exact light-candidate optimality and uniqueness for sample sizes one and two. -/
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- Every small-sample local maximum has the unique light-candidate form, including binary duplicates. -/
theorem lightCandidateForm_of_localMax_smallSamples [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : t = 1 ∨ t = 2) (hh : 0 < h) (hp : LocalMaximizer t h p) :
    LightCandidateForm h p := by
  rcases p.candidate_complete_of_localMax (by omega) hh hp with hl | hhvy
  · exact hl
  · obtain ⟨m, z, hm, hz, e, _, hzheavy, he, hrep⟩ := hhvy
    by_cases hm2 : 2 ≤ m
    · have hz0 : 0 < z := (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)).trans hzheavy.1
      have hheavy : (1 - z) / (m : ℝ) < z := by
        apply (div_lt_iff₀ (Nat.cast_pos.mpr hm)).mpr
        have hr := (div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mp hzheavy.1
        nlinarith
      rw [hrep] at hp
      exact (not_localMax_heavy_candidate_smallSamples ht hm2 ⟨hz0, hzheavy.2⟩ hheavy e hp).elim
    · have hm1 : m = 1 := by omega
      subst m
      rw [hrep]
      exact binary_heavy_form_is_light (by simpa using hzheavy) (by simpa using he) e

/-- All light representations at the same positive entropy have identical objectives. -/
theorem LightCandidateForm.objective_eq {p q : ProbabilityVector ι} {h : ℝ}
    (hp : LightCandidateForm h p) (hq : LightCandidateForm h q) (hh : 0 < h) (t : ℕ) :
    p.objective t = q.objective t := by
  obtain ⟨a, hk, ha, e, hai, hea, rfl⟩ := hp
  obtain ⟨b, hk', hb, e', hbi, heb, rfl⟩ := hq
  have hab := light_candidate_root_unique hh hai hbi hea heb
  rw [objective_zeroExtend, objective_zeroExtend, objective_candidateVector, objective_candidateVector, hab]

/-- Light candidate representations satisfy the original entropy constraint with equality. -/
theorem LightCandidateForm.feasible {p : ProbabilityVector ι} {h : ℝ}
    (hp : LightCandidateForm h p) : p ∈ Feasible h := by
  obtain ⟨a, hk, ha, e, _, he, rfl⟩ := hp
  change (zeroExtend e (candidateVector _ a hk ha)).entropy ≤ ENNReal.ofReal h
  rw [entropy_zeroExtend, entropy_candidateVector, he]

/-- The complete small-sample uniqueness clause: a probability vector is a global maximum
if and only if it is the unique light candidate up to zero coordinates and reindexing. -/
theorem globalMax_iff_lightCandidateForm_smallSamples [Countable ι] [Infinite ι]
    (p : ProbabilityVector ι) {t : ℕ} {h : ℝ} (ht : t = 1 ∨ t = 2) (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) ↔
      LightCandidateForm h p := by
  constructor
  · rintro ⟨hp, hm⟩
    exact lightCandidateForm_of_localMax_smallSamples p ht hh
      ⟨hp, (show IsMaxOn (fun q : ProbabilityVector ι => q.objective t) (Feasible h) p from hm).isLocalMaxOn⟩
  · intro hp
    obtain ⟨q, hq, hmax⟩ := exists_global_maximizer (ι := ι) t h hh.le
    have hql := lightCandidateForm_of_localMax_smallSamples q ht hh
      ⟨hq, (show IsMaxOn (fun r : ProbabilityVector ι => r.objective t) (Feasible h) q from hmax).isLocalMaxOn⟩
    exact ⟨hp.feasible, fun r hr => by rw [hp.objective_eq hql hh t]; exact hmax r hr⟩

/-- The numerical value clause of the small-sample corollary. -/
theorem optimalValue_eq_lightValue_smallSamples {t : ℕ} {h : ℝ}
    (ht : t = 1 ∨ t = 2) (hh : 0 < h) :
    optimalValue t h = lightValue t h := by
  obtain ⟨p, _, hp, hm⟩ := exists_global_maximizer_countable t h hh.le
  rw [optimalValue_eq_of_globalMax p t hp hm]
  exact (lightCandidateForm_of_localMax_smallSamples p ht hh
    ⟨hp, (show IsMaxOn (fun q : ProbabilityVector ℕ => q.objective t) (Feasible h) p from hm).isLocalMaxOn⟩).objective_eq_lightValue hh t

end
end EntropyConstrainedMissingMass.ProbabilityVector
