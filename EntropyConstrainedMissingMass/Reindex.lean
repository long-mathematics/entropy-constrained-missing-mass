import EntropyConstrainedMissingMass.Probability

/-! Relabeling and inserting zero atoms preserve distributions, entropy, missing mass,
and the manuscript's ℓ¹ metric. These constructions do not assume finite support. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι κ : Type*}

/-- Insert zero atoms outside an arbitrary injection of the original index type. -/
noncomputable def zeroExtend (e : ι ↪ κ) (p : ProbabilityVector ι) : ProbabilityVector κ :=
  ofHasSum (Function.extend e p.coord 0)
    (by
      intro j
      classical
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply]
        exact p.coord_nonneg i
      · simp [Function.extend_apply' _ _ _ hj])
    ((hasSum_extend_zero e.injective).mpr p.hasSum_coord)

@[simp] theorem coord_zeroExtend_apply (e : ι ↪ κ) (p : ProbabilityVector ι) (i : ι) :
    (zeroExtend e p).coord (e i) = p.coord i := by
  exact e.injective.extend_apply p.coord 0 i

@[simp] theorem coord_zeroExtend_of_not_mem_range (e : ι ↪ κ) (p : ProbabilityVector ι)
    (j : κ) (hj : j ∉ Set.range e) : (zeroExtend e p).coord j = 0 := by
  exact Function.extend_apply' _ _ _ hj

/-- Any atomwise statistic vanishing at zero has invariant sum under zero insertion. -/
theorem tsum_zeroExtend {A : Type*} [AddCommMonoid A] [TopologicalSpace A] [T2Space A]
    (e : ι ↪ κ) (p : ProbabilityVector ι) (f : ℝ → A) (hf : f 0 = 0) :
    (∑' j, f ((zeroExtend e p).coord j)) = ∑' i, f (p.coord i) := by
  have hs : Function.support (fun j => f ((zeroExtend e p).coord j)) ⊆ Set.range e := by
    intro j hj
    by_contra hn
    exact hj (by dsimp; rw [coord_zeroExtend_of_not_mem_range e p j hn, hf])
  rw [← e.injective.tsum_eq hs]
  simp only [coord_zeroExtend_apply]

@[simp] theorem entropy_zeroExtend (e : ι ↪ κ) (p : ProbabilityVector ι) :
    (zeroExtend e p).entropy = p.entropy := by
  exact tsum_zeroExtend e p (fun x => ENNReal.ofReal (Real.negMulLog x)) (by simp)

@[simp] theorem objective_zeroExtend (e : ι ↪ κ) (p : ProbabilityVector ι) (t : ℕ) :
    (zeroExtend e p).objective t = p.objective t := by
  exact tsum_zeroExtend e p (missingMassTerm t) (by simp [missingMassTerm])

/-- Zero insertion preserves the full ℓ¹ distance, not just atomwise convergence. -/
@[simp] theorem dist_zeroExtend (e : ι ↪ κ) (p q : ProbabilityVector ι) :
    dist (zeroExtend e p) (zeroExtend e q) = dist p q := by
  rw [dist_eq_tsum, dist_eq_tsum]
  have hs : Function.support (fun j => |(zeroExtend e p).coord j - (zeroExtend e q).coord j|)
      ⊆ Set.range e := by
    intro j hj
    by_contra hn
    exact hj (by simp [coord_zeroExtend_of_not_mem_range e p j hn,
      coord_zeroExtend_of_not_mem_range e q j hn])
  rw [← e.injective.tsum_eq hs]
  simp only [coord_zeroExtend_apply]

theorem isometry_zeroExtend (e : ι ↪ κ) : Isometry (zeroExtend e) :=
  Isometry.of_dist_eq (dist_zeroExtend e)

/-- Relabel atoms through an equivalence. -/
noncomputable def reindex (e : ι ≃ κ) (p : ProbabilityVector ι) : ProbabilityVector κ :=
  zeroExtend e.toEmbedding p

@[simp] theorem coord_reindex (e : ι ≃ κ) (p : ProbabilityVector ι) (j : κ) :
    (reindex e p).coord j = p.coord (e.symm j) := by
  obtain ⟨i, rfl⟩ := e.surjective j
  change (zeroExtend e.toEmbedding p).coord (e.toEmbedding i) = p.coord (e.symm (e i))
  rw [coord_zeroExtend_apply, e.symm_apply_apply]

@[simp] theorem entropy_reindex (e : ι ≃ κ) (p : ProbabilityVector ι) :
    (reindex e p).entropy = p.entropy := entropy_zeroExtend e.toEmbedding p

@[simp] theorem objective_reindex (e : ι ≃ κ) (p : ProbabilityVector ι) (t : ℕ) :
    (reindex e p).objective t = p.objective t := objective_zeroExtend e.toEmbedding p t

theorem isometry_reindex (e : ι ≃ κ) : Isometry (reindex e) :=
  isometry_zeroExtend e.toEmbedding

/-- Delete coordinates outside a set containing every nonzero atom. -/
noncomputable def restrictSupport (p : ProbabilityVector ι) (s : Set ι)
    (hs : Function.support p.coord ⊆ s) : ProbabilityVector s :=
  ofHasSum (fun i => p.coord i) (fun i => p.coord_nonneg i)
    ((hasSum_subtype_iff_of_support_subset hs).mpr p.hasSum_coord)

@[simp] theorem coord_restrictSupport (p : ProbabilityVector ι) (s : Set ι)
    (hs : Function.support p.coord ⊆ s) (i : s) :
    (restrictSupport p s hs).coord i = p.coord i := rfl

/-- Restoring the deleted zero coordinates recovers the original probability vector. -/
@[simp] theorem zeroExtend_restrictSupport (p : ProbabilityVector ι) (s : Set ι)
    (hs : Function.support p.coord ⊆ s) :
    zeroExtend (Function.Embedding.subtype (· ∈ s)) (restrictSupport p s hs) = p := by
  apply Subtype.ext
  apply lp.ext
  funext i
  change (zeroExtend (Function.Embedding.subtype (· ∈ s)) (restrictSupport p s hs)).coord i = p.coord i
  by_cases hi : i ∈ s
  · exact coord_zeroExtend_apply (Function.Embedding.subtype (· ∈ s)) (restrictSupport p s hs) ⟨i, hi⟩
  · have hnot : i ∉ Set.range (Function.Embedding.subtype (· ∈ s)) := by simpa using hi
    rw [coord_zeroExtend_of_not_mem_range _ _ _ hnot]
    exact (not_ne_iff.mp (fun hn => hi (hs hn))).symm

@[simp] theorem entropy_restrictSupport (p : ProbabilityVector ι) (s : Set ι)
    (hs : Function.support p.coord ⊆ s) :
    (restrictSupport p s hs).entropy = p.entropy := by
  rw [← entropy_zeroExtend (Function.Embedding.subtype (· ∈ s)), zeroExtend_restrictSupport]

@[simp] theorem objective_restrictSupport (p : ProbabilityVector ι) (s : Set ι)
    (hs : Function.support p.coord ⊆ s) (t : ℕ) :
    (restrictSupport p s hs).objective t = p.objective t := by
  rw [← objective_zeroExtend (Function.Embedding.subtype (· ∈ s)), zeroExtend_restrictSupport]

end EntropyConstrainedMissingMass.ProbabilityVector
