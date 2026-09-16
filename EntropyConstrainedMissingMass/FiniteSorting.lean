import EntropyConstrainedMissingMass.Reindex
import Mathlib.Data.Fin.Tuple.Sort

/-! Finite distributions can be sorted and placed in a countable alphabet without
changing either entropy or objective. No assertion about infinite sorting is assumed. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector

/-- Sort the finite masses in decreasing order. -/
noncomputable def sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    ProbabilityVector (Fin n) := by
  classical
  exact reindex (Tuple.sort (α := ℝᵒᵈ) (fun i => (p.coord i : ℝᵒᵈ))).symm p

@[simp] theorem coord_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) (i : Fin n) :
    (sortedFinite p).coord i = p.coord (Tuple.sort (α := ℝᵒᵈ) (fun j => (p.coord j : ℝᵒᵈ)) i) := by
  classical
  simp [sortedFinite]

theorem antitone_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    Antitone (sortedFinite p).coord := by
  classical
  intro i j hij
  simp only [coord_sortedFinite]
  exact Tuple.monotone_sort (α := ℝᵒᵈ) (fun i => (p.coord i : ℝᵒᵈ)) hij

@[simp] theorem entropy_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) :
    (sortedFinite p).entropy = p.entropy := entropy_reindex _ _

@[simp] theorem objective_sortedFinite {n : ℕ} (p : ProbabilityVector (Fin n)) (t : ℕ) :
    (sortedFinite p).objective t = p.objective t := objective_reindex _ _ _

/-- Append zero atoms after the sorted finite distribution. -/
noncomputable def sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) : ProbabilityVector ℕ :=
  zeroExtend ⟨Fin.val, Fin.val_injective⟩ (sortedFinite p)

@[simp] theorem coord_sortedNat_lt {n : ℕ} (p : ProbabilityVector (Fin n)) (i : ℕ) (hi : i < n) :
    (sortedNat p).coord i = (sortedFinite p).coord ⟨i, hi⟩ :=
  coord_zeroExtend_apply (⟨Fin.val, Fin.val_injective⟩ : Fin n ↪ ℕ) (sortedFinite p) ⟨i, hi⟩

@[simp] theorem coord_sortedNat_ge {n : ℕ} (p : ProbabilityVector (Fin n)) (i : ℕ) (hi : n ≤ i) :
    (sortedNat p).coord i = 0 := by
  apply coord_zeroExtend_of_not_mem_range
  rintro ⟨j, rfl⟩
  exact (Nat.not_lt_of_ge hi) j.isLt

theorem antitone_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) :
    Antitone (sortedNat p).coord := by
  intro i j hij
  by_cases hj : j < n
  · have hi := lt_of_le_of_lt hij hj
    rw [coord_sortedNat_lt p i hi, coord_sortedNat_lt p j hj]
    exact antitone_sortedFinite p hij
  · rw [coord_sortedNat_ge p j (Nat.le_of_not_gt hj)]
    exact (sortedNat p).coord_nonneg i

@[simp] theorem entropy_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) :
    (sortedNat p).entropy = p.entropy := by simp [sortedNat]

@[simp] theorem objective_sortedNat {n : ℕ} (p : ProbabilityVector (Fin n)) (t : ℕ) :
    (sortedNat p).objective t = p.objective t := by simp [sortedNat]

end EntropyConstrainedMissingMass.ProbabilityVector
