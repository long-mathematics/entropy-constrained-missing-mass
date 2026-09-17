import EntropyConstrainedMissingMass.CandidateCompleteness

/-! Distinction of the nonuniform light and heavy shapes beyond binary support. -/
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
open Set
variable {ι : Type*}

/-- In a light representation, every atom is at most the repeated size, and every
positive atom unequal to that size is its unique exceptional coordinate. -/
theorem LightCandidateForm.coordinate_structure {p : ProbabilityVector ι} {h : ℝ}
    (hp : LightCandidateForm h p) :
    ∃ (y : ℝ) (i : ι), 0 < y ∧ (∀ j, p.coord j ≤ y) ∧
      (∀ j, 0 < p.coord j → p.coord j ≠ y → j = i) := by
  classical
  obtain ⟨a,hk,ha,e,hal,_,rfl⟩ := hp
  let y := (1-a)/(entropySupportIndex h : ℝ)
  have hk0 : 0 < (entropySupportIndex h : ℝ) := Nat.cast_pos.mpr hk
  have ha1 : a < 1 := hal.2.trans_le ((div_le_one (by linarith [hk0])).mpr (by linarith [hk0]))
  have hy : 0 < y := div_pos (sub_pos.mpr ha1) hk0
  have hay : a < y := by
    apply (lt_div_iff₀ hk0).mpr
    have hal' := (lt_div_iff₀ (by positivity : (0 : ℝ) < (entropySupportIndex h : ℝ)+1)).mp hal.2
    nlinarith
  refine ⟨y,e 0,hy,?_,?_⟩
  · intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨b,rfl⟩ := hj
      rw [coord_zeroExtend_apply]
      change candidateCoord _ a b ≤ y
      refine Fin.cases hay.le (fun _ => le_rfl) b
    · rw [coord_zeroExtend_of_not_mem_range _ _ _ hj]
      exact hy.le
  · intro j hj hne
    have hjr : j ∈ Set.range e := by
      by_contra hn
      rw [coord_zeroExtend_of_not_mem_range _ _ _ hn] at hj
      exact (lt_irrefl _ hj)
    obtain ⟨b,rfl⟩ := hjr
    rw [coord_zeroExtend_apply] at hne
    change candidateCoord _ a b ≠ y at hne
    revert hne
    refine Fin.cases (by intro _; rfl) (fun b => ?_) b
    intro hn
    exact (hn rfl).elim

/-- A heavy law with at least two light atoms cannot also be a light candidate.
The statement allows arbitrary entropy and arbitrary zero-coordinate embeddings. -/
theorem not_lightCandidateForm_heavy {h z : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hz : z ∈ Ioo (0 : ℝ) 1) (hheavy : (1-z)/(m : ℝ) < z)
    (e : Fin (m+1) ↪ ι) :
    ¬ LightCandidateForm h (zeroExtend e (candidateVector m z (by omega) ⟨hz.1.le,hz.2.le⟩)) := by
  intro hl
  obtain ⟨y,i,hy,hbound,hunique⟩ := hl.coordinate_structure
  let a : Fin (m+1) := ⟨1,by omega⟩
  let b : Fin (m+1) := ⟨2,by omega⟩
  have hq : 0 < (1-z)/(m : ℝ) := div_pos (sub_pos.mpr hz.2) (by positivity)
  have ha : (zeroExtend e (candidateVector m z (by omega) ⟨hz.1.le,hz.2.le⟩)).coord (e a) = (1-z)/(m : ℝ) := by
    rw [coord_zeroExtend_apply]
    rfl
  have hb : (zeroExtend e (candidateVector m z (by omega) ⟨hz.1.le,hz.2.le⟩)).coord (e b) = (1-z)/(m : ℝ) := by
    rw [coord_zeroExtend_apply]
    rfl
  have hzle := hbound (e 0)
  rw [coord_zeroExtend_apply] at hzle
  change z ≤ y at hzle
  have hne : (1-z)/(m : ℝ) ≠ y := ne_of_lt (hheavy.trans_le hzle)
  have hea := hunique (e a) (by rwa [ha]) (by rwa [ha])
  have heb := hunique (e b) (by rwa [hb]) (by rwa [hb])
  have he := congrArg Fin.val (e.injective (hea.trans heb.symm))
  norm_num [a,b] at he

end
end EntropyConstrainedMissingMass.ProbabilityVector
