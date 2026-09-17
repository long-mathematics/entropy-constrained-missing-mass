import EntropyConstrainedMissingMass.FinitePerturbation

/-! Finite embedded coordinate paths as actual perturbations of arbitrary probability vectors. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
open Filter
open scoped Topology
variable {ι : Type*} {n : ℕ}
local instance : DecidableEq ι := Classical.decEq ι

/-- Replace coordinates along any finite embedding, preserving their total mass. -/
def replaceEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i)) : ProbabilityVector ι :=
  p.replaceFinite (Finset.univ.map e) (Function.extend e v p.coord)
    (by
      intro j hj
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
      rw [e.injective.extend_apply]
      exact hv i)
    (by simpa only [Finset.sum_map, e.injective.extend_apply] using hsum)

@[simp] theorem coord_replaceEmbedded_apply (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i)) (i : Fin n) :
    (p.replaceEmbedded e v hv hsum).coord (e i) = v i := by
  simp [replaceEmbedded, e.injective.extend_apply]

theorem coord_replaceEmbedded_off (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i))
    (j : ι) (hj : j ∉ Set.range e) : (p.replaceEmbedded e v hv hsum).coord j = p.coord j := by
  have hn : j ∉ Finset.univ.map e := by simpa using hj
  simp [replaceEmbedded, hn]

theorem dist_replaceEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i)) :
    dist (p.replaceEmbedded e v hv hsum) p = ∑ i, |v i - p.coord (e i)| := by
  rw [replaceEmbedded, dist_replaceFinite, Finset.sum_map]
  simp only [e.injective.extend_apply]

theorem objective_replaceEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i)) (t : ℕ) :
    (p.replaceEmbedded e v hv hsum).objective t = p.objective t +
      (∑ i, missingMassTerm t (v i)) - ∑ i, missingMassTerm t (p.coord (e i)) := by
  rw [replaceEmbedded, objective_replaceFinite, Finset.sum_map]
  simp only [e.injective.extend_apply, Finset.sum_sub_distrib]
  ring

theorem entropy_replaceEmbedded_ne_top (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i))
    (hp : p.entropy ≠ ⊤) : (p.replaceEmbedded e v hv hsum).entropy ≠ ⊤ :=
  entropy_replaceFinite_ne_top p _ _ _ _ hp

theorem entropy_toReal_replaceEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i))
    (hp : p.entropy ≠ ⊤) :
    (p.replaceEmbedded e v hv hsum).entropy.toReal = p.entropy.toReal +
      (∑ i, Real.negMulLog (v i)) - ∑ i, Real.negMulLog (p.coord (e i)) := by
  rw [replaceEmbedded, entropy_toReal_replaceFinite _ _ _ _ _ hp, Finset.sum_map]
  simp only [e.injective.extend_apply, Finset.sum_sub_distrib]
  ring

/-- A total path constructor; inadmissible input vectors return the original probability vector. -/
def perturbEmbedded (p : ProbabilityVector ι) (e : Fin n ↪ ι) (v : Fin n → ℝ) : ProbabilityVector ι :=
  if hv : (∀ i, 0 ≤ v i) ∧ ∑ i, v i = ∑ i, p.coord (e i) then p.replaceEmbedded e v hv.1 hv.2 else p

theorem perturbEmbedded_eq (p : ProbabilityVector ι) (e : Fin n ↪ ι) (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i = ∑ i, p.coord (e i)) :
    p.perturbEmbedded e v = p.replaceEmbedded e v hv hsum := by simp [perturbEmbedded, hv, hsum]

theorem dist_perturbEmbedded_le (p : ProbabilityVector ι) (e : Fin n ↪ ι) (v : Fin n → ℝ) :
    dist (p.perturbEmbedded e v) p ≤ ∑ i, |v i - p.coord (e i)| := by
  unfold perturbEmbedded
  split_ifs with hv
  · rw [dist_replaceEmbedded]
  · simpa using Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (v i - p.coord (e i)))

theorem tendsto_perturbEmbedded {α : Type*} {l : Filter α} (p : ProbabilityVector ι)
    (e : Fin n ↪ ι) (v : α → Fin n → ℝ)
    (hv : ∀ i, Tendsto (fun r => v r i) l (𝓝 (p.coord (e i)))) :
    Tendsto (fun r => p.perturbEmbedded e (v r)) l (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun r => dist_perturbEmbedded_le p e (v r))
  have hs := tendsto_finsetSum Finset.univ
    (fun i _ => ((hv i).sub (tendsto_const_nhds (x := p.coord (e i)))).abs)
  simpa using hs

/-- Genuine ℓ¹ local maximality restricted to any parameter set. -/
theorem localMaxOn_of_embedded_path {α : Type*} [TopologicalSpace α] {t : ℕ} {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer t h p) (e : Fin n ↪ ι) (v : α → Fin n → ℝ) (a : α) (s : Set α)
    (hbase : ∀ i, v a i = p.coord (e i))
    (hlim : ∀ i, Tendsto (fun r => v r i) (𝓝[s] a) (𝓝 (p.coord (e i))))
    (hgood : ∀ᶠ r in 𝓝[s] a, (∀ i, 0 ≤ v r i) ∧ ∑ i, v r i = ∑ i, p.coord (e i))
    (hent : ∀ᶠ r in 𝓝[s] a, (∑ i, Real.negMulLog (v r i)) ≤ ∑ i, Real.negMulLog (p.coord (e i))) :
    IsLocalMaxOn (fun r => ∑ i, missingMassTerm t (v r i)) s a := by
  have hfin := finite_entropy_of_feasible hp.1
  have hfeas : ∀ᶠ r in 𝓝[s] a, p.perturbEmbedded e (v r) ∈ Feasible h := by
    filter_upwards [hgood, hent] with r hg he
    rw [perturbEmbedded_eq p e (v r) hg.1 hg.2]
    change (p.replaceEmbedded e (v r) hg.1 hg.2).entropy ≤ ENNReal.ofReal h
    apply le_trans _ (show p.entropy ≤ ENNReal.ofReal h from hp.1)
    apply (ENNReal.toReal_le_toReal (entropy_replaceEmbedded_ne_top p e (v r) hg.1 hg.2 hfin) hfin).mp
    rw [entropy_toReal_replaceEmbedded _ _ _ _ _ hfin]
    linarith
  have ht : Tendsto (fun r => p.perturbEmbedded e (v r)) (𝓝[s] a) (𝓝[Feasible h] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_perturbEmbedded p e v hlim, hfeas⟩
  have hmax := ht.eventually hp.2
  filter_upwards [hmax, hgood] with r hr hg
  rw [perturbEmbedded_eq p e (v r) hg.1 hg.2, objective_replaceEmbedded] at hr
  simp only [hbase]
  linarith


/-- Genuine ℓ¹ local maximality implies local maximality along every feasible finite path. -/
theorem localMax_of_embedded_path {t : ℕ} {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer t h p) (e : Fin n ↪ ι) (v : ℝ → Fin n → ℝ) (a : ℝ)
    (hbase : ∀ i, v a i = p.coord (e i))
    (hlim : ∀ i, Tendsto (fun r => v r i) (𝓝 a) (𝓝 (p.coord (e i))))
    (hgood : ∀ᶠ r in 𝓝 a, (∀ i, 0 ≤ v r i) ∧ ∑ i, v r i = ∑ i, p.coord (e i))
    (hent : ∀ᶠ r in 𝓝 a, (∑ i, Real.negMulLog (v r i)) ≤ ∑ i, Real.negMulLog (p.coord (e i))) :
    IsLocalMax (fun r => ∑ i, missingMassTerm t (v r i)) a := by
  have hfin := finite_entropy_of_feasible hp.1
  have hfeas : ∀ᶠ r in 𝓝 a, p.perturbEmbedded e (v r) ∈ Feasible h := by
    filter_upwards [hgood, hent] with r hg he
    rw [perturbEmbedded_eq p e (v r) hg.1 hg.2]
    change (p.replaceEmbedded e (v r) hg.1 hg.2).entropy ≤ ENNReal.ofReal h
    apply le_trans _ (show p.entropy ≤ ENNReal.ofReal h from hp.1)
    apply (ENNReal.toReal_le_toReal (entropy_replaceEmbedded_ne_top p e (v r) hg.1 hg.2 hfin) hfin).mp
    rw [entropy_toReal_replaceEmbedded _ _ _ _ _ hfin]
    linarith
  have ht : Tendsto (fun r => p.perturbEmbedded e (v r)) (𝓝 a) (𝓝[Feasible h] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_perturbEmbedded p e v hlim, hfeas⟩
  have hmax := ht.eventually hp.2
  filter_upwards [hmax, hgood] with r hr hg
  rw [perturbEmbedded_eq p e (v r) hg.1 hg.2, objective_replaceEmbedded] at hr
  simp only [hbase]
  linarith

/-- The actual finite-dimensional constrained problem inherited by any embedded coordinates. -/
theorem localMaxOn_embedded_coordinates {t : ℕ} {h : ℝ} (p : ProbabilityVector ι)
    (hp : LocalMaximizer t h p) (e : Fin n ↪ ι) :
    IsLocalMaxOn (fun v : Fin n → ℝ => ∑ i, missingMassTerm t (v i))
      {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = ∑ i, p.coord (e i)) ∧
        (∑ i, Real.negMulLog (v i)) ≤ ∑ i, Real.negMulLog (p.coord (e i))}
      (fun i => p.coord (e i)) := by
  apply localMaxOn_of_embedded_path p hp e id (fun i => p.coord (e i)) _ (fun _ => rfl)
  · intro i
    exact (continuous_apply i).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact ⟨hv.1, hv.2.1⟩
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact hv.2.2

end
end EntropyConstrainedMissingMass.ProbabilityVector
