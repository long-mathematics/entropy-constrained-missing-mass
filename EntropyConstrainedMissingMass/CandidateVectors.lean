import EntropyConstrainedMissingMass.Probability
import EntropyConstrainedMissingMass.BranchEntropy
import EntropyConstrainedMissingMass.CertificateBounds
import EntropyConstrainedMissingMass.Reindex
import Mathlib.Data.Fin.Tuple.Basic

/-! Genuine probability vectors realizing the manuscript's one-exceptional-atom branches. -/

namespace EntropyConstrainedMissingMass

noncomputable section

open scoped ENNReal
open Set

/-- The distinguished coordinate is zero; all other coordinates have equal mass. -/
def candidateCoord (m : ℕ) (z : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases z (fun _ => (1 - z) / (m : ℝ))

@[simp] theorem candidateCoord_zero (m : ℕ) (z : ℝ) : candidateCoord m z 0 = z := rfl

@[simp] theorem candidateCoord_succ (m : ℕ) (z : ℝ) (i : Fin m) :
    candidateCoord m z i.succ = (1 - z) / (m : ℝ) := rfl

theorem sum_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    ∑ i, candidateCoord m z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  ring

theorem candidateCoord_nonneg {m : ℕ} {z : ℝ} (hz : z ∈ Icc 0 1)
    (i : Fin (m + 1)) : 0 ≤ candidateCoord m z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.1
  · exact div_nonneg (sub_nonneg.mpr hz.2) (Nat.cast_nonneg _)

theorem hasSum_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    HasSum (candidateCoord m z) 1 := by
  simpa only [sum_candidateCoord hm] using hasSum_fintype (candidateCoord m z)

/-- The finite candidate law with one exceptional mass and `m` repeated masses. -/
def candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) :
    ProbabilityVector (Fin (m + 1)) :=
  ProbabilityVector.ofHasSum (candidateCoord m z) (candidateCoord_nonneg hz)
    (hasSum_candidateCoord hm z)

@[simp] theorem coord_candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) : (candidateVector m z hm hz).coord = candidateCoord m z := rfl

theorem sum_negMulLog_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    (∑ i, Real.negMulLog (candidateCoord m z i)) = branchEntropy m z := by
  rw [Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.negMulLog, branchEntropy]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  ring

theorem entropy_candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (candidateVector m z hm hz).entropy = ENNReal.ofReal (branchEntropy m z) := by
  have hp : (candidateVector m z hm hz).entropy ≠ ⊤ :=
    (ProbabilityVector.entropy_ne_top_iff _).2 (hasSum_fintype _).summable
  rw [ProbabilityVector.entropy_eq_ofReal_tsum _ hp, coord_candidateVector,
    tsum_fintype, sum_negMulLog_candidateCoord hm]

theorem objective_candidateVector (m t : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (candidateVector m z hm hz).objective t = branchObjective m t z := by
  rw [ProbabilityVector.objective, coord_candidateVector, tsum_fintype, Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, missingMassTerm, branchObjective]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

/-- The uniform meeting point has `m+1` identical coordinates. -/
theorem candidateCoord_uniform {m : ℕ} (hm : 0 < m) (i : Fin (m + 1)) :
    candidateCoord m (1 / ((m : ℝ) + 1)) i = 1 / ((m : ℝ) + 1) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [candidateCoord_succ]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem candidateCoord_pos {m : ℕ} (hm : 0 < m) {z : ℝ} (hz : z ∈ Ioo 0 1)
    (i : Fin (m + 1)) : 0 < candidateCoord m z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.1
  · exact div_pos (sub_pos.mpr hz.2) (Nat.cast_pos.mpr hm)

/-- Matching the real branch entropy really does satisfy the extended entropy constraint. -/
theorem candidateVector_feasible {m : ℕ} {z h : ℝ} (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (he : branchEntropy m z ≤ h) :
    candidateVector m z hm hz ∈ ProbabilityVector.Feasible h := by
  change (candidateVector m z hm hz).entropy ≤ ENNReal.ofReal h
  rw [entropy_candidateVector]
  exact ENNReal.ofReal_le_ofReal he

/-- The finite candidate's index set is the initial segment of the countable alphabet. -/
def candidateIndexEmbedding (m : ℕ) : Fin (m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

/-- The same candidate as a genuine countably indexed probability vector. -/
def natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) :
    ProbabilityVector ℕ :=
  ProbabilityVector.zeroExtend (candidateIndexEmbedding m) (candidateVector m z hm hz)

@[simp] theorem coord_natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (i : Fin (m + 1)) :
    (natCandidateVector m z hm hz).coord i.val = candidateCoord m z i :=
  ProbabilityVector.coord_zeroExtend_apply _ _ i

theorem coord_natCandidateVector_eq_zero (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (n : ℕ) (hn : m + 1 ≤ n) :
    (natCandidateVector m z hm hz).coord n = 0 := by
  apply ProbabilityVector.coord_zeroExtend_of_not_mem_range
  rintro ⟨i, hi⟩
  have hi' : i.val = n := hi
  exact Nat.not_lt_of_ge hn (hi' ▸ i.isLt)

@[simp] theorem entropy_natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (natCandidateVector m z hm hz).entropy = ENNReal.ofReal (branchEntropy m z) := by
  rw [natCandidateVector, ProbabilityVector.entropy_zeroExtend, entropy_candidateVector]

@[simp] theorem objective_natCandidateVector (m t : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (natCandidateVector m z hm hz).objective t = branchObjective m t z := by
  rw [natCandidateVector, ProbabilityVector.objective_zeroExtend, objective_candidateVector]

theorem natCandidateVector_finite_support (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) : (Function.support (natCandidateVector m z hm hz).coord).Finite := by
  apply (Set.finite_range (candidateIndexEmbedding m)).subset
  intro n hn
  by_contra hnot
  exact hn (ProbabilityVector.coord_zeroExtend_of_not_mem_range _ _ n hnot)

theorem natCandidateVector_feasible {m : ℕ} {z h : ℝ} (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (he : branchEntropy m z ≤ h) :
    natCandidateVector m z hm hz ∈ ProbabilityVector.Feasible h := by
  change (natCandidateVector m z hm hz).entropy ≤ ENNReal.ofReal h
  rw [entropy_natCandidateVector]
  exact ENNReal.ofReal_le_ofReal he

end

end EntropyConstrainedMissingMass
