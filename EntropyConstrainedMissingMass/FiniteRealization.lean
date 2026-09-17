import EntropyConstrainedMissingMass.FiniteAlphabetClassification

/-! Exact equivalence between fitting positive support and realization on a fixed
finite alphabet, including zero-coordinate endpoint representations. -/
open Set
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- The atoms of a finite law can be placed in the original alphabet, with only
zero coordinates inserted. Thus this describes realization up to relabeling. -/
def FiniteRealizable (N : ℕ) (p : ProbabilityVector ι) : Prop :=
  ∃ (q : ProbabilityVector (Fin N)) (e : Fin N ↪ ι), p = zeroExtend e q

/-- A distribution on an infinite alphabet is realizable on exactly `N` available
symbols iff it has finite positive support of cardinality at most `N`.
Padding uses zero coordinates, so support of cardinality exactly `N` is allowed. -/
theorem finiteRealizable_iff [Infinite ι] (N : ℕ) (p : ProbabilityVector ι) :
    FiniteRealizable N p ↔
      (Function.support p.coord).Finite ∧ (Function.support p.coord).ncard ≤ N := by
  classical
  constructor
  · rintro ⟨q,e,rfl⟩
    have hsub : Function.support (zeroExtend e q).coord ⊆ Set.range e := by
      intro i hi
      by_contra hn
      exact hi (coord_zeroExtend_of_not_mem_range _ _ _ hn)
    refine ⟨(Set.finite_range e).subset hsub, ?_⟩
    have hc := Set.ncard_le_ncard hsub (Set.finite_range e)
    simpa only [Set.ncard_range_of_injective e.injective, Nat.card_fin] using hc
  · rintro ⟨hf,hcard⟩
    obtain ⟨i,hi⟩ := p.exists_coord_pos
    have hnon : (Function.support p.coord).Nonempty := ⟨i,hi.ne'⟩
    have hN : 0 < N := ((Set.ncard_pos hf).mpr hnon).trans_le hcard
    obtain ⟨s,hsub,_,hsize⟩ := Set.infinite_univ.exists_superset_ncard_eq
      (Set.subset_univ _) hf hcard
    have hs : s.Finite := Set.finite_of_ncard_ne_zero (hsize.trans_ne hN.ne')
    let := hs.fintype
    let r : s ≃ Fin N := Fintype.equivFinOfCardEq (by rw [Set.fintypeCard_eq_ncard]; exact hsize)
    let q := reindex r (restrictSupport p s hsub)
    let e : Fin N ↪ ι := r.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ s))
    refine ⟨q,e,?_⟩
    have he : r.toEmbedding.trans e = Function.Embedding.subtype (· ∈ s) := by
      ext j
      simp only [e,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply,
        Function.Embedding.subtype_apply]
    change p = zeroExtend e (reindex r (restrictSupport p s hsub))
    rw [zeroExtend_reindex,he,zeroExtend_restrictSupport]

/-- Realization preserves the actual entropy and every integer missing-mass
objective, rather than just an abstract multiset of coordinate values. -/
theorem FiniteRealizable.exists_preserving {N : ℕ} {p : ProbabilityVector ι}
    (hp : FiniteRealizable N p) :
    ∃ (q : ProbabilityVector (Fin N)) (e : Fin N ↪ ι),
      p = zeroExtend e q ∧ q.entropy = p.entropy ∧ ∀ t, q.objective t = p.objective t := by
  obtain ⟨q,e,rfl⟩ := hp
  exact ⟨q,e,rfl,(entropy_zeroExtend e q).symm,fun t => (objective_zeroExtend e q t).symm⟩

/-- Zero insertion preserves the number of positive coordinates exactly. -/
theorem support_zeroExtend_eq_image {κ : Type*} (e : ι ↪ κ) (p : ProbabilityVector ι) :
    Function.support (zeroExtend e p).coord = e '' Function.support p.coord := by
  ext j
  constructor
  · intro hj
    by_cases hmem : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hmem
      exact ⟨i,by simpa only [Function.mem_support,coord_zeroExtend_apply] using hj,rfl⟩
    · exact False.elim (hj (coord_zeroExtend_of_not_mem_range e p j hmem))
  · rintro ⟨i,hi,rfl⟩
    simpa only [Function.mem_support,coord_zeroExtend_apply] using hi

@[simp] theorem support_zeroExtend_ncard {κ : Type*} (e : ι ↪ κ) (p : ProbabilityVector ι) :
    (Function.support (zeroExtend e p).coord).ncard = (Function.support p.coord).ncard := by
  rw [support_zeroExtend_eq_image,Set.ncard_image_of_injective _ e.injective]

theorem candidateVector_support_ncard {m : ℕ} (hm : 0 < m) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    (Function.support (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩).coord).ncard = m+1 := by
  have he : Function.support (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩).coord = Set.univ := by
    ext i
    simp only [Set.mem_univ,iff_true,Function.mem_support]
    exact (candidateCoord_pos hm hz i).ne'
  rw [he,Set.ncard_univ,Nat.card_fin]

/-- At the entropy endpoint the exceptional zero contributes no support atom. -/
theorem candidateVector_zero_support_ncard {m : ℕ} (hm : 0 < m) :
    (Function.support (candidateVector m 0 hm ⟨le_rfl,zero_le_one⟩).coord).ncard = m := by
  have he : Function.support (candidateVector m 0 hm ⟨le_rfl,zero_le_one⟩).coord =
      Set.range (Fin.succ : Fin m → Fin (m+1)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (0 : ℝ) ≠ 0 ↔ ∃ j : Fin m, j.succ = 0
      simp
    · constructor
      · intro _; exact ⟨j,rfl⟩
      · intro _
        exact (div_pos (by norm_num : (0 : ℝ) < 1-0) (Nat.cast_pos.mpr hm)).ne'
  rw [he,Set.ncard_range_of_injective (Fin.succ_injective m),Nat.card_fin]

/-- The interior one-exceptional law fits exactly when `m+1 ≤ N`. -/
theorem finiteRealizable_candidate_iff [Infinite ι] {m N : ℕ} (hm : 0 < m)
    {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) (e : Fin (m+1) ↪ ι) :
    FiniteRealizable N (zeroExtend e (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩)) ↔ m+1 ≤ N := by
  rw [finiteRealizable_iff,support_zeroExtend_ncard,candidateVector_support_ncard hm hz]
  have hf : (Function.support (zeroExtend e (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩)).coord).Finite := by
    rw [support_zeroExtend_eq_image]
    exact (Set.toFinite _).image e
  exact and_iff_right hf

/-- The light endpoint fits even on `N=m`, despite its representation having
`m+1` coordinates. This explicitly handles the manuscript's zero deletion. -/
theorem finiteRealizable_zero_candidate_iff [Infinite ι] {m N : ℕ} (hm : 0 < m)
    (e : Fin (m+1) ↪ ι) :
    FiniteRealizable N (zeroExtend e (candidateVector m 0 hm ⟨le_rfl,zero_le_one⟩)) ↔ m ≤ N := by
  rw [finiteRealizable_iff,support_zeroExtend_ncard,candidateVector_zero_support_ncard hm]
  have hf : (Function.support (zeroExtend e (candidateVector m 0 hm ⟨le_rfl,zero_le_one⟩)).coord).Finite := by
    rw [support_zeroExtend_eq_image]
    exact (Set.toFinite _).image e
  exact and_iff_right hf

end
end EntropyConstrainedMissingMass.ProbabilityVector
