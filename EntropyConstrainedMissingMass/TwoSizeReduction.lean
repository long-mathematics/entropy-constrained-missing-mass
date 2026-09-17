import EntropyConstrainedMissingMass.AtomSplitting
import EntropyConstrainedMissingMass.Support
import EntropyConstrainedMissingMass.TripleLocalMax

/-! Extracting the two positive sizes from exclusion of ordered embedded triples. -/
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- Any ordered triple of coordinate values gives an embedding of three distinct atoms. -/
theorem exists_embedding_of_coord_lt (p : ProbabilityVector ι) {i j k : ι}
    (hij : p.coord i < p.coord j) (hjk : p.coord j < p.coord k) :
    ∃ e : Fin 3 ↪ ι, e 0 = i ∧ e 1 = j ∧ e 2 = k := by
  have hi : i ≠ j := fun h => by simp [h] at hij
  have hj : j ≠ k := fun h => by simp [h] at hjk
  have hk : i ≠ k := fun h => by have ht := hij.trans hjk; simp [h] at ht
  refine ⟨⟨![i, j, k], ?_⟩, rfl, rfl, rfl⟩
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- The no-three-values conclusion is exactly an at-most-two-positive-sizes representation. -/
theorem exists_two_sizes_of_no_ordered_triple (p : ProbabilityVector ι)
    (hno : ∀ e : Fin 3 ↪ ι, 0 < p.coord (e 0) → p.coord (e 0) < p.coord (e 1) →
      p.coord (e 1) < p.coord (e 2) → False) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p.coord i = 0 ∨ p.coord i = a ∨ p.coord i = b := by
  classical
  have hthree {i j k : ι} (hi : 0 < p.coord i) (hij : p.coord i < p.coord j)
      (hjk : p.coord j < p.coord k) : False := by
    obtain ⟨e, he0, he1, he2⟩ := p.exists_embedding_of_coord_lt hij hjk
    exact hno e (by simpa [he0] using hi) (by simpa [he0, he1] using hij)
      (by simpa [he1, he2] using hjk)
  obtain ⟨i, hi⟩ := p.exists_coord_pos
  by_cases hj : ∃ j, 0 < p.coord j ∧ p.coord j ≠ p.coord i
  · obtain ⟨j, hj, hji⟩ := hj
    refine ⟨p.coord i, p.coord j, hi, hj, fun k => ?_⟩
    by_cases hk : p.coord k = 0
    · exact Or.inl hk
    by_cases hki : p.coord k = p.coord i
    · exact Or.inr (Or.inl hki)
    by_cases hkj : p.coord k = p.coord j
    · exact Or.inr (Or.inr hkj)
    exfalso
    have hkpos := lt_of_le_of_ne (p.coord_nonneg k) (Ne.symm hk)
    rcases lt_or_gt_of_ne hji with hji | hij
    · rcases lt_or_gt_of_ne hki with hki | hik
      · rcases lt_or_gt_of_ne hkj with hkj | hjk
        · exact hthree hkpos hkj hji
        · exact hthree hj hjk hki
      · exact hthree hj hji hik
    · rcases lt_or_gt_of_ne hkj with hkj | hjk
      · rcases lt_or_gt_of_ne hki with hki | hik
        · exact hthree hkpos hki hij
        · exact hthree hi hik hkj
      · exact hthree hi hij hjk
  · refine ⟨p.coord i, p.coord i, hi, hi, fun k => ?_⟩
    by_cases hk : p.coord k = 0
    · exact Or.inl hk
    have hkpos := lt_of_le_of_ne (p.coord_nonneg k) (Ne.symm hk)
    exact Or.inr (Or.inl (not_ne_iff.mp (fun hki => hj ⟨k, hkpos, hki⟩)))

theorem finite_support_of_no_ordered_triple (p : ProbabilityVector ι)
    (hno : ∀ e : Fin 3 ↪ ι, 0 < p.coord (e 0) → p.coord (e 0) < p.coord (e 1) →
      p.coord (e 1) < p.coord (e 2) → False) : (Function.support p.coord).Finite := by
  obtain ⟨a, b, ha, hb, hc⟩ := p.exists_two_sizes_of_no_ordered_triple hno
  exact p.finite_support_of_two_sizes ha hb hc

theorem two_sizes_of_localMax_one {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer 1 h p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p.coord i = 0 ∨ p.coord i = a ∨ p.coord i = b := by
  apply p.exists_two_sizes_of_no_ordered_triple
  intro e h0 h01 h12
  exact TripleGeometry.not_localMax_three_sizes_one p e h0 h01 h12 hp

theorem finite_support_of_localMax_one {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer 1 h p) : (Function.support p.coord).Finite := by
  obtain ⟨a, b, ha, hb, hc⟩ := p.two_sizes_of_localMax_one hp
  exact p.finite_support_of_two_sizes ha hb hc

/-- Countably infinite is a special case: any infinite alphabet saturates at t=1. -/
theorem entropy_saturation_of_localMax_one [Infinite ι] {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer 1 h p) : p.entropy = ENNReal.ofReal h :=
  p.entropy_saturation_of_finite_support (by omega) hp (p.finite_support_of_localMax_one hp)

end
end EntropyConstrainedMissingMass.ProbabilityVector
