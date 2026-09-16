import EntropyConstrainedMissingMass.Probability
import Mathlib.Tactic.Linarith

/-! Finite-support implications and the zero-entropy boundary case.
The support conclusions in this module are conditional on a finite set of sizes;
the local-maximizer theorem establishing that condition is a separate obligation. -/

namespace EntropyConstrainedMissingMass
namespace ProbabilityVector
variable {ι : Type*}

/-- Every positive size occurs only finitely often, even on an infinite alphabet. -/
theorem finite_fiber (p : ProbabilityVector ι) {a : ℝ} (ha : 0 < a) :
    Set.Finite {i | p.coord i = a} := by
  apply Set.finite_coe_iff.mp
  apply Finite.of_summable_const ha
  have hs := p.summable_coord.subtype (fun i => p.coord i = a)
  exact hs.congr (fun i => i.property)

/-- A finite set of positive sizes implies finite support, with no assumption on the alphabet. -/
theorem finite_support_of_finite_sizes (p : ProbabilityVector ι) {s : Set ℝ}
    (hs : s.Finite) (hpos : ∀ a ∈ s, 0 < a)
    (hcovers : ∀ i, p.coord i ≠ 0 → p.coord i ∈ s) :
    (Function.support p.coord).Finite := by
  have hu := hs.biUnion (fun a ha => p.finite_fiber (hpos a ha))
  apply hu.subset
  intro i hi
  exact Set.mem_iUnion₂.mpr ⟨p.coord i, hcovers i hi, rfl⟩

theorem finite_support_of_two_sizes (p : ProbabilityVector ι) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (h : ∀ i, p.coord i = 0 ∨ p.coord i = a ∨ p.coord i = b) :
    (Function.support p.coord).Finite := by
  apply ((p.finite_fiber ha).union (p.finite_fiber hb)).subset
  intro i hi
  rcases h i with hz | hsize
  · exact (hi hz).elim
  · exact hsize

theorem exists_coord_pos (p : ProbabilityVector ι) : ∃ i, 0 < p.coord i := by
  by_contra h
  push Not at h
  have hz : p.coord = 0 := funext (fun i => le_antisymm (h i) (p.coord_nonneg i))
  have hm := p.tsum_coord
  rw [hz] at hm
  simp at hm

/-- A unit coordinate forces all other coordinates to be zero. -/
theorem coord_eq_zero_of_coord_eq_one (p : ProbabilityVector ι) {i j : ι}
    (hi : p.coord i = 1) (hji : j ≠ i) : p.coord j = 0 := by
  classical
  have hsum := p.summable_coord.sum_le_tsum ({i, j} : Finset ι)
    (fun k _ => p.coord_nonneg k)
  rw [p.tsum_coord] at hsum
  have hij : i ≠ j := Ne.symm hji
  simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hij),
    Finset.sum_singleton, hi] at hsum
  exact le_antisymm (by linarith) (p.coord_nonneg j)

/-- This is the precise point-mass characterization, including unused coordinates. -/
theorem entropy_eq_zero_iff (p : ProbabilityVector ι) :
    p.entropy = 0 ↔ ∃ i, p.coord i = 1 ∧ ∀ j, j ≠ i → p.coord j = 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := p.exists_coord_pos
    have he : ENNReal.ofReal (Real.negMulLog (p.coord i)) = 0 :=
      ENNReal.tsum_eq_zero.mp h i
    have he' := ENNReal.ofReal_eq_zero.mp he
    have hi1 : p.coord i = 1 := by
      by_contra hn
      have hlt : p.coord i < 1 := lt_of_le_of_ne (p.coord_le_one i) hn
      have hp : 0 < Real.negMulLog (p.coord i) :=
        mul_pos_of_neg_of_neg (neg_neg_of_pos hi) (Real.log_neg hi hlt)
      exact (not_lt_of_ge he') hp
    exact ⟨i, hi1, fun j hj => p.coord_eq_zero_of_coord_eq_one hi1 hj⟩
  · rintro ⟨i, hi, hz⟩
    apply ENNReal.tsum_eq_zero.mpr
    intro j
    by_cases hji : j = i
    · simp [hji, hi]
    · simp [hz j hji]

theorem objective_eq_zero_of_entropy_eq_zero (p : ProbabilityVector ι) {t : ℕ}
    (ht : 1 ≤ t) (h : p.entropy = 0) : p.objective t = 0 := by
  obtain ⟨i, hi, hz⟩ := p.entropy_eq_zero_iff.mp h
  unfold objective
  calc
    (∑' j, missingMassTerm t (p.coord j)) = ∑' _ : ι, (0 : ℝ) := by
      apply tsum_congr
      intro j
      by_cases hji : j = i
      · simp [missingMassTerm, hji, hi, Nat.ne_zero_of_lt ht]
      · simp [missingMassTerm, hz j hji]
    _ = 0 := by simp

theorem feasible_zero_iff (p : ProbabilityVector ι) :
    p ∈ (Feasible 0 : Set (ProbabilityVector ι)) ↔ p.entropy = 0 := by
  simp [Feasible]

theorem entropy_eq_zero_of_subsingleton [Subsingleton ι] (p : ProbabilityVector ι) :
    p.entropy = 0 := by
  obtain ⟨i, _⟩ := p.exists_coord_pos
  have hi : p.coord i = 1 := by
    rw [← p.tsum_coord, tsum_eq_single i]
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  exact p.entropy_eq_zero_iff.mpr
    ⟨i, hi, fun j hj => (hj (Subsingleton.elim j i)).elim⟩

end ProbabilityVector
end EntropyConstrainedMissingMass
