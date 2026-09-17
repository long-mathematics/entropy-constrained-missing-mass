import EntropyConstrainedMissingMass.MainTheorem
import EntropyConstrainedMissingMass.RepeatedFourVariation
import EntropyConstrainedMissingMass.CandidateVectors

/-! The actual one-exceptional-atom representation, with an explicit finite embedding. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- All positive coordinates have the same size. -/
def UniformOnSupport (p : ProbabilityVector ι) : Prop :=
  ∀ i j, 0 < p.coord i → 0 < p.coord j → p.coord i = p.coord j

theorem not_uniformOnSupport_iff (p : ProbabilityVector ι) :
    ¬ p.UniformOnSupport ↔ ∃ i j, 0 < p.coord i ∧ 0 < p.coord j ∧ p.coord i ≠ p.coord j := by
  classical
  simp only [UniformOnSupport, not_forall]
  constructor
  · rintro ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, hi, hj, hij⟩
  · rintro ⟨i, j, hi, hj, hij⟩
    exact ⟨i, j, hi, hj, hij⟩

/-- Two sizes and exclusion of two distinct repeated sizes give an exceptional index. -/
theorem exists_exceptional_index_of_localMax (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hn : ¬ p.UniformOnSupport) :
    ∃ i : ι, ∃ q : ℝ, 0 < p.coord i ∧ 0 < q ∧ p.coord i ≠ q ∧
      (∃ j, j ≠ i ∧ p.coord j = q) ∧
      ∀ k, k ≠ i → p.coord k = 0 ∨ p.coord k = q := by
  classical
  obtain ⟨i, j, hi, hj, hij⟩ := (p.not_uniformOnSupport_iff).mp hn
  obtain ⟨a, b, ha, hb, hab⟩ := p.two_sizes_of_localMax ht hp
  have hvalues (k : ι) : p.coord k = 0 ∨ p.coord k = p.coord i ∨ p.coord k = p.coord j := by
    rcases hab i with hi0 | hia | hib
    · exact (ne_of_gt hi hi0).elim
    · rcases hab j with hj0 | hja | hjb
      · exact (ne_of_gt hj hj0).elim
      · exact (hij (hia.trans hja.symm)).elim
      · simpa only [hia, hjb] using hab k
    · rcases hab j with hj0 | hja | hjb
      · exact (ne_of_gt hj hj0).elim
      · rcases hab k with hk | hk | hk
        · exact Or.inl hk
        · exact Or.inr (Or.inr (hk.trans hja.symm))
        · exact Or.inr (Or.inl (hk.trans hib.symm))
      · exact (hij (hib.trans hjb.symm)).elim
  have hidx : i ≠ j := fun he => hij (congrArg p.coord he)
  by_cases hrepeat : ∃ k, k ≠ i ∧ p.coord k = p.coord i
  · obtain ⟨k, hki, hkv⟩ := hrepeat
    refine ⟨j, p.coord i, hj, hi, hij.symm, ⟨i, hidx, rfl⟩, ?_⟩
    intro l hlj
    rcases hvalues l with hl | hl | hl
    · exact Or.inl hl
    · exact Or.inr hl
    · exact (hij (p.repeated_positive_sizes_eq ht hp i k j l hki.symm hlj.symm
        hkv hl hi hj)).elim
  · refine ⟨i, p.coord j, hi, hj, hij, ⟨j, hidx.symm, rfl⟩, ?_⟩
    intro k hki
    rcases hvalues k with hk | hk | hk
    · exact Or.inl hk
    · exact (hrepeat ⟨k, hki, hk⟩).elim
    · exact Or.inr hk

/-- Enumerating an exceptional atom and the rest of the finite support gives exact equality
of probability vectors, including all zero coordinates outside the embedding. -/
theorem exceptional_form_of_index (p : ProbabilityVector ι)
    (hfin : (Function.support p.coord).Finite) (i : ι) (q : ℝ)
    (hi : 0 < p.coord i) (hq : 0 < q) (hiq : p.coord i ≠ q)
    (hj : ∃ j, j ≠ i ∧ p.coord j = q)
    (hrest : ∀ k, k ≠ i → p.coord k = 0 ∨ p.coord k = q) :
    ∃ (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Set.Ioo 0 1)
      (e : Fin (m + 1) ↪ ι),
      z ≠ (1 - z) / (m : ℝ) ∧
      p = zeroExtend e (candidateVector m z hm ⟨le_of_lt hz.1, le_of_lt hz.2⟩) := by
  classical
  let R := {k : ι // p.coord k ≠ 0 ∧ k ≠ i}
  have hR : Set.Finite {k : ι | p.coord k ≠ 0 ∧ k ≠ i} :=
    hfin.subset (fun _ hk => hk.1)
  let : Fintype R := hR.fintype
  let m := Fintype.card R
  let er : Fin m ≃ R := (Fintype.equivFin R).symm
  have hRcoord (k : R) : p.coord k = q := (hrest k k.property.2).resolve_left k.property.1
  have hm : 0 < m := by
    obtain ⟨j, hji, hjq⟩ := hj
    have : Nonempty R := ⟨⟨j, by rw [hjq]; exact ⟨ne_of_gt hq, hji⟩⟩⟩
    exact Fintype.card_pos_iff.mpr this
  let e : Fin (m + 1) ↪ ι := ⟨Fin.cases i (fun k => (er k).val), by
    intro u v
    refine Fin.cases ?_ (fun a => ?_) u
    · refine Fin.cases ?_ (fun b => ?_) v
      · intro _; rfl
      · intro huv; exact ((er b).property.2 huv.symm).elim
    · refine Fin.cases ?_ (fun b => ?_) v
      · intro huv; exact ((er a).property.2 huv).elim
      · intro huv; exact congrArg Fin.succ (er.injective (Subtype.ext huv))⟩
  have he0 : e 0 = i := rfl
  have hes (k : Fin m) : p.coord (e k.succ) = q := hRcoord (er k)
  have hsupp : Function.support p.coord ⊆ Set.range e := by
    intro k hk
    by_cases hki : k = i
    · exact ⟨0, he0.trans hki.symm⟩
    · exact ⟨(er.symm ⟨k, hk, hki⟩).succ, by
        change (er (er.symm ⟨k, hk, hki⟩)).val = k
        simp only [Equiv.apply_symm_apply]⟩
  have hsum : p.coord i + (m : ℝ) * q = 1 := by
    have he := e.injective.tsum_eq hsupp
    rw [p.tsum_coord, tsum_fintype, Fin.sum_univ_succ] at he
    simpa only [he0, hes, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using he
  have hz : p.coord i ∈ Set.Ioo 0 1 := ⟨hi, by
    have hmq : 0 < (m : ℝ) * q := mul_pos (Nat.cast_pos.mpr hm) hq
    linarith⟩
  have hqeq : q = (1 - p.coord i) / (m : ℝ) := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))).mpr
    nlinarith only [hsum]
  refine ⟨m, p.coord i, hm, hz, e, by simpa only [← hqeq] using hiq, ?_⟩
  apply Subtype.ext
  apply lp.ext
  funext k
  change p.coord k = (zeroExtend e (candidateVector m (p.coord i) hm
    ⟨le_of_lt hz.1, le_of_lt hz.2⟩)).coord k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    rw [coord_zeroExtend_apply]
    change p.coord (e j) = candidateCoord m (p.coord i) j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact (hes j).trans hqeq
  · rw [coord_zeroExtend_of_not_mem_range _ _ _ hk]
    by_contra hne
    exact hk (hsupp hne)

/-- The manuscript's one-exceptional-atom theorem for genuine local maximizers. -/
theorem exceptional_form_of_localMax (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hn : ¬ p.UniformOnSupport) :
    ∃ (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Set.Ioo 0 1)
      (e : Fin (m + 1) ↪ ι),
      z ≠ (1 - z) / (m : ℝ) ∧
      p = zeroExtend e (candidateVector m z hm ⟨le_of_lt hz.1, le_of_lt hz.2⟩) := by
  obtain ⟨i, q, hi, hq, hiq, hj, hrest⟩ := p.exists_exceptional_index_of_localMax ht hp hn
  exact p.exceptional_form_of_index (p.finite_support_of_localMax ht hp) i q hi hq hiq hj hrest

end
end EntropyConstrainedMissingMass.ProbabilityVector
