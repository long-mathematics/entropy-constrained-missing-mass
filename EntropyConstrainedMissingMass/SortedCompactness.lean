import EntropyConstrainedMissingMass.SortedTail
import EntropyConstrainedMissingMass.EntropyTopology
import Mathlib.Topology.Sequences

/-! Compactness of sorted, entropy-bounded probability sequences in the genuine ℓ¹ metric. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.ProbabilityVector

variable {ι : Type*}

/-- Probability vectors form a closed subset of ℓ¹. -/
theorem isClosed_probability_lp :
    IsClosed {p : lp (fun _ : ι => ℝ) 1 | (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1} := by
  apply IsClosed.inter
  · convert isClosed_iInter (fun i => isClosed_le (continuous_const (y := (0 : ℝ)))
        (lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous) using 1
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  · exact isClosed_eq (lp.tsumCLM ℝ ι ℝ).continuous continuous_const

noncomputable instance completeSpace : CompleteSpace (ProbabilityVector ι) := by
  exact @IsClosed.completeSpace_coe (lp (fun _ : ι => ℝ) 1) _ _ _ isClosed_probability_lp

/-- A finite prefix and the two nonnegative tails bound ℓ¹ distance. -/
theorem dist_le_prefix_add_tails (p q : ProbabilityVector ℕ) (N : ℕ) :
    dist p q ≤ (∑ i ∈ Finset.range N, |p.coord i - q.coord i|) +
      (∑' i : {n : ℕ // N ≤ n}, p.coord i) + (∑' i : {n : ℕ // N ≤ n}, q.coord i) := by
  have hs := (p.summable_coord.sub q.summable_coord).abs
  have hsplit := hs.sum_add_tsum_compl (s := Finset.range N)
  have htail : (∑' i : {n : ℕ // N ≤ n}, |p.coord i - q.coord i|) ≤
      (∑' i : {n : ℕ // N ≤ n}, p.coord i) + (∑' i : {n : ℕ // N ≤ n}, q.coord i) := by
    have hadd := (p.summable_coord.subtype (N ≤ ·)).tsum_add (q.summable_coord.subtype (N ≤ ·))
    simp only [Function.comp_def] at hadd
    rw [← hadd]
    apply (hs.subtype (N ≤ ·)).tsum_le_tsum _
      ((p.summable_coord.subtype (N ≤ ·)).add (q.summable_coord.subtype (N ≤ ·)))
    intro i
    dsimp only [Function.comp_def]
    exact abs_sub_le_iff.mpr ⟨by linarith [q.coord_nonneg i], by linarith [p.coord_nonneg i]⟩
  have hsplit' : (∑ i ∈ Finset.range N, |p.coord i - q.coord i|) +
      (∑' i : {n : ℕ // N ≤ n}, |p.coord i - q.coord i|) = dist p q := by
    have hset : (↑(Finset.range N) : Set ℕ)ᶜ = {n | N ≤ n} := by ext n; simp
    rw [hset] at hsplit
    exact hsplit.trans (dist_eq_tsum p q).symm
  linarith

/-- Coordinate convergence plus a uniform entropy bound yields an ℓ¹-Cauchy sequence. -/
theorem cauchySeq_of_sorted_coordinate_tendsto {h : ℝ} (hh : 0 ≤ h)
    (u : ℕ → ProbabilityVector ℕ) (hu : ∀ k, Antitone (u k).coord ∧ (u k).entropy ≤ ENNReal.ofReal h)
    (f : ℕ → ℝ) (hf : ∀ i, Filter.Tendsto (fun k => (u k).coord i) Filter.atTop (nhds (f i))) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, _, hN⟩ := uniform_sorted_tail hh (show 0 < ε / 4 by positivity)
  have hhead : Filter.Tendsto (fun k => ∑ i ∈ Finset.range N, |(u k).coord i - f i|)
      Filter.atTop (nhds 0) := by
    have ht := tendsto_finsetSum (Finset.range N) (fun i _ => ((hf i).sub_const (f i)).abs)
    simpa using ht
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hhead.eventually_lt_const (show 0 < ε / 4 by positivity))
  refine ⟨K, ?_⟩
  intro k hk l hl
  have hprefix : (∑ i ∈ Finset.range N, |(u k).coord i - (u l).coord i|) ≤
      (∑ i ∈ Finset.range N, |(u k).coord i - f i|) +
      (∑ i ∈ Finset.range N, |(u l).coord i - f i|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      |(u k).coord i - (u l).coord i| ≤ |(u k).coord i - f i| + |f i - (u l).coord i| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (f i)]
  have htailk := hN N le_rfl (u k) (hu k).1 (hu k).2
  have htaill := hN N le_rfl (u l) (hu l).1 (hu l).2
  simp only [abs_of_nonneg ((u k).coord_nonneg _)] at htailk
  simp only [abs_of_nonneg ((u l).coord_nonneg _)] at htaill
  have hd := dist_le_prefix_add_tails (u k) (u l) N
  linarith [hK k hk, hK l hl]

/-- The sorted entropy sublevel, in ℓ¹ probability-vector space. -/
def SortedFeasible (h : ℝ) : Set (ProbabilityVector ℕ) :=
  {p | Antitone p.coord ∧ p.entropy ≤ ENNReal.ofReal h}

theorem isClosed_sorted : IsClosed {p : ProbabilityVector ℕ | Antitone p.coord} := by
  have heq : {p : ProbabilityVector ℕ | Antitone p.coord} =
      ⋂ i : ℕ, ⋂ j : ℕ, ⋂ (_ : i ≤ j), {p | p.coord j ≤ p.coord i} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [heq]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le (continuous_coord _) (continuous_coord _)

theorem isClosed_sortedFeasible (h : ℝ) : IsClosed (SortedFeasible h) :=
  isClosed_sorted.inter (isClosed_feasible h)

/-- Sorted probability vectors with bounded entropy are compact in ℓ¹. -/
theorem isCompact_sortedFeasible {h : ℝ} (hh : 0 ≤ h) : IsCompact (SortedFeasible h) := by
  apply IsSeqCompact.isCompact
  intro u hu
  have hc : IsCompact {f : ℕ → ℝ | ∀ i, f i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨f, _, φ, hφ, hf⟩ := hc.tendsto_subseq (x := fun k => (u k).coord)
    (fun k i => ⟨(u k).coord_nonneg i, (u k).coord_le_one i⟩)
  have hcu : CauchySeq (u ∘ φ) := cauchySeq_of_sorted_coordinate_tendsto hh (u ∘ φ)
    (fun k => hu (φ k)) f (fun i => (continuous_apply i).tendsto f |>.comp hf)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcu
  exact ⟨p, (isClosed_sortedFeasible h).mem_of_tendsto hp (Filter.Eventually.of_forall (fun k => hu (φ k))),
    φ, hφ, hp⟩

end EntropyConstrainedMissingMass.ProbabilityVector
