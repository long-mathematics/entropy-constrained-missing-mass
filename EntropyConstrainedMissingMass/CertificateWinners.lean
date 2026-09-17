import EntropyConstrainedMissingMass.FiniteClassification

/-! Strict finite comparison certificates imply exact optimizer uniqueness. -/
namespace EntropyConstrainedMissingMass
open Set
noncomputable section

/-- A specified heavy branch, without choosing its embedding or discarding zero coordinates. -/
def ProbabilityVector.HeavyCandidateAt {ι : Type*} (h : ℝ) (m : ℕ) (p : ProbabilityVector ι) : Prop :=
  ∃ (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) (e : Fin (m+1) ↪ ι),
    z ∈ Ioo (1/((m : ℝ)+1)) 1 ∧ branchEntropy m z = h ∧
      p = ProbabilityVector.zeroExtend e (candidateVector m z hm hz)

theorem ProbabilityVector.HeavyCandidateAt.objective_eq {ι : Type*} {h : ℝ} {m t : ℕ}
    {p : ProbabilityVector ι} (hp : p.HeavyCandidateAt h m) (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) : p.objective t = heavyCandidateValue t h m := by
  obtain ⟨z,hm0,hz,e,hroot,he,rfl⟩ := hp
  rw [ProbabilityVector.objective_zeroExtend,objective_candidateVector,
    ← heavyRoot_eq_of_spec hh (heavy_domain_of_index hm) hroot he]
  rfl

theorem ProbabilityVector.HeavyCandidateAt.feasible {ι : Type*} {h : ℝ} {m : ℕ}
    {p : ProbabilityVector ι} (hp : p.HeavyCandidateAt h m) : p ∈ ProbabilityVector.Feasible h := by
  obtain ⟨z,hm0,hz,e,_,he,rfl⟩ := hp
  simp only [ProbabilityVector.Feasible, Set.mem_ofPred_eq, ProbabilityVector.entropy_zeroExtend,
    entropy_candidateVector,he,le_refl]

theorem optimalValue_eq_light_of_comparisons {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h)
    (hw : ∀ m, entropySupportIndex h ≤ m → m ≤ candidateCutoff t h →
      heavyCandidateValue t h m ≤ lightValue t h) : optimalValue t h = lightValue t h := by
  classical
  rw [optimalValue_eq_finiteCandidateMaximum ht hh]
  apply le_antisymm _ (lightValue_le_finiteCandidateMaximum t h)
  apply Finset.max'_le
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · rfl
  · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hv
    exact hw m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

theorem optimalValue_eq_heavy_of_comparisons {t m : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hM : m ≤ candidateCutoff t h)
    (hl : lightValue t h ≤ heavyCandidateValue t h m)
    (hw : ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h →
      heavyCandidateValue t h j ≤ heavyCandidateValue t h m) :
    optimalValue t h = heavyCandidateValue t h m := by
  classical
  rw [optimalValue_eq_finiteCandidateMaximum ht hh]
  apply le_antisymm _ (heavyValue_le_finiteCandidateMaximum t h m hm hM)
  apply Finset.max'_le
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact hl
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact hw j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

theorem ProbabilityVector.globalMax_iff_light_of_strict_comparisons {ι : Type*} [Countable ι] [Infinite ι]
    (p : ProbabilityVector ι) {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h)
    (hw : ∀ m, entropySupportIndex h ≤ m → m ≤ candidateCutoff t h →
      heavyCandidateValue t h m < lightValue t h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) ↔
      LightCandidateForm h p := by
  have hv := optimalValue_eq_light_of_comparisons ht hh (fun m hm hM => (hw m hm hM).le)
  constructor
  · rintro ⟨hp,hmax⟩
    rcases p.candidate_complete_at_cutoff ht hh hp hmax with hl | hc
    · exact hl
    · obtain ⟨m,z,hm,hz,e,hk,hM,hr,he,hrep⟩ := hc
      have heq := (show p.HeavyCandidateAt h m from ⟨z,hm,hz,e,hr,he,hrep⟩).objective_eq hh hk (t := t)
      have hglobal := optimalValue_eq_of_globalMax p t hp hmax
      rw [hv,heq] at hglobal
      exact ((hw m hk hM).ne hglobal.symm).elim
  · intro hp
    refine ⟨feasible_lightCandidateForm hp,fun q hq => ?_⟩
    rw [hp.objective_eq_lightValue hh,← hv]
    exact objective_le_optimalValue q t hq

theorem ProbabilityVector.globalMax_iff_heavy_of_strict_comparisons {ι : Type*} [Countable ι] [Infinite ι]
    (p : ProbabilityVector ι) {t m : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hM : m ≤ candidateCutoff t h)
    (hl : lightValue t h < heavyCandidateValue t h m)
    (hw : ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h → j ≠ m →
      heavyCandidateValue t h j < heavyCandidateValue t h m) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) ↔
      p.HeavyCandidateAt h m := by
  have hv := optimalValue_eq_heavy_of_comparisons ht hh hm hM hl.le
    (fun j hj hjM => by
      by_cases he : j = m
      · subst j; rfl
      · exact (hw j hj hjM he).le)
  constructor
  · rintro ⟨hp,hmax⟩
    have hglobal := optimalValue_eq_of_globalMax p t hp hmax
    rw [hv] at hglobal
    rcases p.candidate_complete_at_cutoff ht hh hp hmax with hlight | hc
    · rw [hlight.objective_eq_lightValue hh] at hglobal
      exact (hl.ne hglobal.symm).elim
    · obtain ⟨j,z,hj,hz,e,hk,hjM,hr,he,hrep⟩ := hc
      have hform : p.HeavyCandidateAt h j := ⟨z,hj,hz,e,hr,he,hrep⟩
      have heq := hform.objective_eq hh hk (t := t)
      rw [heq] at hglobal
      have hjm : j = m := by
        by_contra hn
        exact (hw j hk hjM hn).ne hglobal.symm
      simpa only [hjm] using hform
  · intro hp
    refine ⟨hp.feasible,fun q hq => ?_⟩
    rw [hp.objective_eq hh hm,← hv]
    exact objective_le_optimalValue q t hq

/-- A winner of the truncated heavy list bounds the entire infinite heavy family. -/
theorem heavyCandidateValue_le_of_finite_comparisons {t m : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hh : 0 < h)
    (hw : ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h →
      heavyCandidateValue t h j ≤ heavyCandidateValue t h m)
    (j : ℕ) (hj : entropySupportIndex h ≤ j) :
    heavyCandidateValue t h j ≤ heavyCandidateValue t h m := by
  by_cases hjM : j ≤ candidateCutoff t h
  · exact hw j hj hjM
  · have hlt := branchObjective_lt_at_cutoff hh t ht
      (heavy_domain_of_index (index_le_candidateCutoff t h))
      (sample_entropy_le_candidateCutoff t h) (Nat.cast_lt.mpr (lt_of_not_ge hjM))
    exact hlt.le.trans (hw _ (index_le_candidateCutoff t h) le_rfl)

/-- The maximum over all heavy multiplicities is certified by finitely many comparisons. -/
theorem heavy_sup_eq_of_comparisons {t m : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hw : ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h →
      heavyCandidateValue t h j ≤ heavyCandidateValue t h m) :
    sSup ((heavyCandidateValue t h) '' Ici (entropySupportIndex h)) = heavyCandidateValue t h m := by
  have hall := heavyCandidateValue_le_of_finite_comparisons ht hh hw
  apply le_antisymm
  · apply csSup_le
    · exact ⟨heavyCandidateValue t h m,m,hm,rfl⟩
    · rintro _ ⟨j,hj,rfl⟩
      exact hall j hj
  · apply le_csSup
    · refine ⟨heavyCandidateValue t h m, ?_⟩
      rintro _ ⟨j,hj,rfl⟩
      exact hall j hj
    · exact ⟨m,hm,rfl⟩

end
end EntropyConstrainedMissingMass
