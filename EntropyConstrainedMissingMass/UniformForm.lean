import EntropyConstrainedMissingMass.ExceptionalForm

/-! Uniform finite-support laws and the zero exceptional-coordinate entropy endpoint. -/

set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- A uniform finite-support law on an infinite alphabet is the endpoint candidate `p_n(0)`.
The embedding includes one unused coordinate for the zero exceptional atom. -/
theorem uniform_form_of_finite_support [Infinite ι] (p : ProbabilityVector ι)
    (hfin : (Function.support p.coord).Finite) (hu : p.UniformOnSupport) :
    ∃ (n : ℕ) (hn : 0 < n) (e : Fin (n + 1) ↪ ι),
      p = zeroExtend e (candidateVector n 0 hn (by constructor <;> norm_num)) := by
  classical
  let R := {k : ι // p.coord k ≠ 0}
  let : Fintype R := hfin.fintype
  let n := Fintype.card R
  let er : Fin n ≃ R := (Fintype.equivFin R).symm
  obtain ⟨j, hj⟩ := p.exists_coord_pos
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨⟨j, ne_of_gt hj⟩⟩
  have hval (k : R) : p.coord k = p.coord j :=
    hu k j (lt_of_le_of_ne (p.coord_nonneg k) k.property.symm) hj
  let es : Fin n ↪ ι := er.toEmbedding.trans (Function.Embedding.subtype (fun k => p.coord k ≠ 0))
  have hsum : (n : ℝ) * p.coord j = 1 := by
    have hsupp : Function.support p.coord ⊆ Set.range es := by
      intro k hk
      exact ⟨er.symm ⟨k, hk⟩, by change (er (er.symm ⟨k, hk⟩)).val = k; simp⟩
    have he := es.injective.tsum_eq hsupp
    rw [p.tsum_coord, tsum_fintype] at he
    have hconst : (fun k : Fin n => p.coord (es k)) = fun _ => p.coord j := by
      funext k; exact hval (er k)
    rw [hconst] at he
    simpa using he
  have hc : p.coord j = 1 / (n : ℝ) := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).mpr
    nlinarith only [hsum]
  obtain ⟨i, hi⟩ := hfin.exists_notMem
  have hi0 : p.coord i = 0 := by simpa only [Function.mem_support, not_not] using hi
  let e : Fin (n + 1) ↪ ι := ⟨Fin.cases i (fun k => (er k).val), by
    intro u v
    refine Fin.cases ?_ (fun a => ?_) u
    · refine Fin.cases ?_ (fun b => ?_) v
      · intro _; rfl
      · intro he
        change i = (er b).val at he
        exact ((er b).property (by rw [← he]; exact hi0)).elim
    · refine Fin.cases ?_ (fun b => ?_) v
      · intro he
        change (er a).val = i at he
        exact ((er a).property (by rw [he]; exact hi0)).elim
      · intro he; exact congrArg Fin.succ (er.injective (Subtype.ext he))⟩
  refine ⟨n, hn, e, ?_⟩
  apply Subtype.ext
  apply lp.ext
  funext k
  change p.coord k = (zeroExtend e (candidateVector n 0 hn _)).coord k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hk
    rw [coord_zeroExtend_apply]
    change p.coord (e a) = candidateCoord n 0 a
    refine Fin.cases ?_ (fun b => ?_) a
    · exact hi0
    · change p.coord (er b).val = (1 - 0) / (n : ℝ)
      simpa only [sub_zero] using (hval (er b)).trans hc
  · rw [coord_zeroExtend_of_not_mem_range _ _ _ hk]
    by_contra hne
    apply hk
    exact ⟨(er.symm ⟨k, hne⟩).succ, by change (er (er.symm ⟨k, hne⟩)).val = k; simp⟩

/-- The entropy of the uniform endpoint is exactly log of its positive support size. -/
theorem uniform_form_entropy [Infinite ι] (p : ProbabilityVector ι)
    (hfin : (Function.support p.coord).Finite) (hu : p.UniformOnSupport) :
    ∃ (n : ℕ) (hn : 0 < n) (e : Fin (n + 1) ↪ ι),
      p = zeroExtend e (candidateVector n 0 hn (by constructor <;> norm_num)) ∧
      p.entropy = ENNReal.ofReal (Real.log n) := by
  obtain ⟨n, hn, e, he⟩ := p.uniform_form_of_finite_support hfin hu
  refine ⟨n, hn, e, he, ?_⟩
  rw [he, entropy_zeroExtend, entropy_candidateVector, branchEntropy_zero]

end
end EntropyConstrainedMissingMass.ProbabilityVector
