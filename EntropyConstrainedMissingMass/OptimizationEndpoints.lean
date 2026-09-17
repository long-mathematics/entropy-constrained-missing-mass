import EntropyConstrainedMissingMass.FiniteAlphabetClassification

/-! Explicit optimization wrappers for the degenerate entropy/alphabet endpoints. -/
namespace EntropyConstrainedMissingMass
noncomputable section

/-- On any alphabet, all feasible zero-entropy laws are exactly the point-mass maxima. -/
theorem ProbabilityVector.globalMax_zero_iff {ι : Type*} (p : ProbabilityVector ι)
    {t : ℕ} (ht : 1 ≤ t) :
    (p ∈ Feasible 0 ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible 0 → q.objective t ≤ p.objective t) ↔
      ∃ i, p.coord i = 1 ∧ ∀ j, j ≠ i → p.coord j = 0 := by
  rw [← p.entropy_eq_zero_iff]
  constructor
  · exact fun hp => p.feasible_zero_iff.mp hp.1
  · intro he
    refine ⟨p.feasible_zero_iff.mpr he, fun q hq => ?_⟩
    rw [p.objective_eq_zero_of_entropy_eq_zero (by omega) he,
      q.objective_eq_zero_of_entropy_eq_zero (by omega) (q.feasible_zero_iff.mp hq)]

theorem optimalValue_zero_entropy {t : ℕ} (ht : 1 ≤ t) : optimalValue t 0 = 0 := by
  let p := ProbabilityVector.pointMass (0 : ℕ)
  have hp : p.entropy = 0 := ProbabilityVector.entropy_pointMass _
  have hm := (p.globalMax_zero_iff ht).mpr (p.entropy_eq_zero_iff.mp hp)
  rw [optimalValue_eq_of_globalMax p t hm.1 hm.2,
    p.objective_eq_zero_of_entropy_eq_zero (by omega) hp]

/-- Every probability law on a singleton alphabet is a point mass and maximizes. -/
theorem ProbabilityVector.globalMax_subsingleton {ι : Type*} [Subsingleton ι]
    (p : ProbabilityVector ι) {t : ℕ} (ht : 1 ≤ t) (h : ℝ) :
    (∃ i, p.coord i = 1 ∧ ∀ j, j ≠ i → p.coord j = 0) ∧
    p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  refine ⟨p.entropy_eq_zero_iff.mp p.entropy_eq_zero_of_subsingleton, ?_, ?_⟩
  · change p.entropy ≤ ENNReal.ofReal h
    rw [p.entropy_eq_zero_of_subsingleton]
    exact zero_le
  · intro q _
    rw [p.objective_eq_zero_of_entropy_eq_zero (by omega) p.entropy_eq_zero_of_subsingleton,
      q.objective_eq_zero_of_entropy_eq_zero (by omega) q.entropy_eq_zero_of_subsingleton]

end
end EntropyConstrainedMissingMass
