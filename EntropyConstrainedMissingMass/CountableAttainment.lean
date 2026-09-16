import EntropyConstrainedMissingMass.Truncation
import EntropyConstrainedMissingMass.FiniteAttainment
import Mathlib.Basic.Denumerable

/-! A true global maximum for countable distributions.
Finite tail coarsenings are sorted without changing their objectives; their limits show that a
maximum on the compact sorted entropy sublevel dominates every unsorted countable distribution. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector

/-- Every nonnegative entropy budget admits a sorted feasible distribution. -/
theorem sortedFeasible_nonempty (h : ℝ) : (SortedFeasible h).Nonempty := by
  let q : ProbabilityVector (Fin 1) := pointMass 0
  refine ⟨sortedNat q, antitone_sortedNat q, ?_⟩
  simp only [entropy_sortedNat, q, entropy_pointMass]
  exact zero_le

/-- The sorted compact entropy sublevel has a true maximum of the missing-mass objective. -/
theorem exists_sorted_maximizer (t : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ∃ p : ProbabilityVector ℕ, p ∈ SortedFeasible h ∧
      ∀ q : ProbabilityVector ℕ, q ∈ SortedFeasible h → q.objective t ≤ p.objective t := by
  exact (isCompact_sortedFeasible hh).exists_isMaxOn (sortedFeasible_nonempty h)
    (continuous_objective t).continuousOn

/-- A maximum among sorted distributions is already a maximum among all countable distributions.
This uses only finite sorting and finite coarsening approximation, not infinite rearrangement. -/
theorem isMaxOn_feasible_of_sorted (t : ℕ) (h : ℝ) (p : ProbabilityVector ℕ)
    (hp : ∀ q : ProbabilityVector ℕ, q ∈ SortedFeasible h → q.objective t ≤ p.objective t) :
    ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  intro q hq
  apply le_of_tendsto (q.tendsto_objective_truncate t)
  apply Filter.Eventually.of_forall
  intro N
  have hs : sortedNat (q.truncate N) ∈ SortedFeasible h := by
    refine ⟨antitone_sortedNat _, ?_⟩
    rw [entropy_sortedNat]
    exact q.feasible_truncate hq N
  simpa only [objective_sortedNat] using hp (sortedNat (q.truncate N)) hs

/-- Countable-alphabet attainment in the manuscript's original feasible set and ℓ¹ topology.
The maximum can be chosen decreasing; no finite-support premise is imposed. -/
theorem exists_global_maximizer_countable (t : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ∃ p : ProbabilityVector ℕ, Antitone p.coord ∧ p ∈ Feasible h ∧
      ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  obtain ⟨p, hp, hmax⟩ := exists_sorted_maximizer t h hh
  exact ⟨p, hp.1, hp.2, isMaxOn_feasible_of_sorted t h p hmax⟩

/-- Attainment for every nonempty countable alphabet, covering finite and infinite cases. -/
theorem exists_global_maximizer {ι : Type*} [Countable ι] [Nonempty ι]
    (t : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ∃ p : ProbabilityVector ι, p ∈ Feasible h ∧
      ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  classical
  rcases finite_or_infinite ι with hfinite | hinfinite
  · let : Finite ι := hfinite
    let : Fintype ι := Fintype.ofFinite ι
    exact exists_global_maximizer_finite t h hh
  · let : Infinite ι := hinfinite
    let e : ℕ ≃ ι := Classical.choice inferInstance
    obtain ⟨p, _, hp, hmax⟩ := exists_global_maximizer_countable t h hh
    refine ⟨reindex e p, ?_, ?_⟩
    · change (reindex e p).entropy ≤ ENNReal.ofReal h
      simpa only [entropy_reindex] using (show p.entropy ≤ ENNReal.ofReal h from hp)
    · intro q hq
      have hq' : reindex e.symm q ∈ Feasible h := by
        change (reindex e.symm q).entropy ≤ ENNReal.ofReal h
        simpa only [entropy_reindex] using (show q.entropy ≤ ENNReal.ofReal h from hq)
      simpa only [objective_reindex] using hmax (reindex e.symm q) hq'

end EntropyConstrainedMissingMass.ProbabilityVector
