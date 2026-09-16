import EntropyConstrainedMissingMass.EntropySeries

/-! Equal finite entropy forbids strict domination at every positive sample size. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι κ : Type*}

/-- The sign-change consequence used in the crossing proofs. -/
theorem exists_objective_lt_of_equal_entropy (p : ProbabilityVector ι) (q : ProbabilityVector κ)
    (hp : p.entropy ≠ ⊤) (heq : p.entropy = q.entropy)
    (hstrict : ∃ n : ℕ, q.objective (n + 1) < p.objective (n + 1)) :
    ∃ n : ℕ, p.objective (n + 1) < q.objective (n + 1) := by
  by_contra h
  push Not at h
  obtain ⟨n, hn⟩ := hstrict
  have hs := p.hasSum_objective_sub_div_zero q hp heq
  have hpos := hs.summable.tsum_pos
    (fun k => div_nonneg (sub_nonneg.mpr (h k)) (by positivity)) n
    (div_pos (sub_pos.mpr hn) (by positivity))
  rw [hs.tsum_eq] at hpos
  exact (lt_irrefl 0) hpos

/-- If all positive-integer objectives are weakly ordered, equal entropy forces equality at each. -/
theorem objective_eq_of_equal_entropy_of_le (p : ProbabilityVector ι) (q : ProbabilityVector κ)
    (hp : p.entropy ≠ ⊤) (heq : p.entropy = q.entropy)
    (hle : ∀ n : ℕ, p.objective (n + 1) ≤ q.objective (n + 1)) (n : ℕ) :
    p.objective (n + 1) = q.objective (n + 1) := by
  apply le_antisymm (hle n)
  by_contra h
  have hstrict := lt_of_not_ge h
  obtain ⟨k, hk⟩ := q.exists_objective_lt_of_equal_entropy p (heq ▸ hp) heq.symm ⟨n, hstrict⟩
  exact (not_lt_of_ge (hle k)) hk

end EntropyConstrainedMissingMass.ProbabilityVector
