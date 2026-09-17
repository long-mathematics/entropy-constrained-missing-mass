import EntropyConstrainedMissingMass.CandidateCompleteness
import EntropyConstrainedMissingMass.HeavyCutoff
import EntropyConstrainedMissingMass.CountableAttainment
import Mathlib.Data.Set.Card

/-! Exact finite classification, including all tied maximizers and support bounds. -/

open Set
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The unique entropy-matched light root, with an arbitrary value off the positive-entropy domain. -/
def lightRoot (h : ℝ) : ℝ := by
  classical
  exact if he : ∃ a, a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ)+1)) ∧
    branchEntropy (entropySupportIndex h) a = h then he.choose else 0

theorem lightRoot_spec {h : ℝ} (hh : 0 < h) :
    lightRoot h ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ)+1)) ∧
      branchEntropy (entropySupportIndex h) (lightRoot h) = h := by
  have he := (existsUnique_light_candidate_parameter hh).exists
  simp only [lightRoot, dite_eq_left he]
  exact he.choose_spec

theorem lightRoot_mem {h : ℝ} (hh : 0 < h) : lightRoot h ∈ Icc (0 : ℝ) 1 := by
  have hs := lightRoot_spec hh
  refine ⟨hs.1.1, hs.1.2.le.trans ?_⟩
  apply (div_le_one (by positivity)).mpr
  linarith [(Nat.cast_nonneg (entropySupportIndex h) : (0 : ℝ) ≤ (entropySupportIndex h : ℝ))]

/-- The finite cutoff in the manuscript. -/
def candidateCutoff (t : ℕ) (h : ℝ) : ℕ := max (entropySupportIndex h) ⌈(t : ℝ)*h+1⌉₊

theorem index_le_candidateCutoff (t : ℕ) (h : ℝ) : entropySupportIndex h ≤ candidateCutoff t h :=
  le_max_left _ _

theorem sample_entropy_le_candidateCutoff (t : ℕ) (h : ℝ) :
    (t : ℝ)*h+1 ≤ (candidateCutoff t h : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem heavy_domain_of_index {h : ℝ} {m : ℕ} (hm : entropySupportIndex h ≤ m) :
    Real.exp h-1 < (m : ℝ) := by
  have hk := Nat.lt_floor_add_one (Real.exp h)
  have hc : (entropySupportIndex h : ℝ) ≤ m := Nat.cast_le.mpr hm
  change Real.exp h < (entropySupportIndex h : ℝ)+1 at hk
  linarith

/-- Canonical light and heavy comparison values. -/
def lightValue (t : ℕ) (h : ℝ) : ℝ := branchObjective (entropySupportIndex h) t (lightRoot h)

def heavyCandidateValue (t : ℕ) (h : ℝ) (m : ℕ) : ℝ := branchObjective m t (heavyRoot h m)

def canonicalLight (h : ℝ) (hh : 0 < h) : ProbabilityVector ℕ :=
  natCandidateVector (entropySupportIndex h) (lightRoot h) (entropySupportIndex_pos hh.le) (lightRoot_mem hh)

def canonicalHeavy (h : ℝ) (hh : 0 < h) (m : ℕ) (hm : entropySupportIndex h ≤ m) : ProbabilityVector ℕ :=
  natCandidateVector m (heavyRoot h m) (lt_of_lt_of_le (entropySupportIndex_pos hh.le) hm)
    ⟨(heavy_parameters_pos hh (heavy_domain_of_index hm)).2.1.le.trans
      (heavy_parameters_pos hh (heavy_domain_of_index hm)).2.2.1.le,
      (heavyRoot_spec hh (heavy_domain_of_index hm)).1.2.le⟩

theorem canonicalLight_feasible {h : ℝ} (hh : 0 < h) : canonicalLight h hh ∈ ProbabilityVector.Feasible h :=
  natCandidateVector_feasible _ _ (lightRoot_spec hh).2.le

theorem canonicalHeavy_feasible {h : ℝ} (hh : 0 < h) (m : ℕ) (hm : entropySupportIndex h ≤ m) :
    canonicalHeavy h hh m hm ∈ ProbabilityVector.Feasible h :=
  natCandidateVector_feasible _ _ (heavyRoot_spec hh (heavy_domain_of_index hm)).2.le

@[simp] theorem objective_canonicalLight (t : ℕ) {h : ℝ} (hh : 0 < h) :
    (canonicalLight h hh).objective t = lightValue t h := objective_natCandidateVector _ _ _ _ _

@[simp] theorem objective_canonicalHeavy (t : ℕ) {h : ℝ} (hh : 0 < h)
    (m : ℕ) (hm : entropySupportIndex h ≤ m) :
    (canonicalHeavy h hh m hm).objective t = heavyCandidateValue t h m := objective_natCandidateVector _ _ _ _ _

/-- The genuine global value: supremum over all countably indexed feasible probability laws. -/
def optimalValue (t : ℕ) (h : ℝ) : ℝ :=
  sSup ((fun p : ProbabilityVector ℕ => p.objective t) '' ProbabilityVector.Feasible h)

private theorem objective_image_bddAbove (t : ℕ) (h : ℝ) :
    BddAbove ((fun p : ProbabilityVector ℕ => p.objective t) '' ProbabilityVector.Feasible h) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨p,_,rfl⟩
  exact p.objective_le_one t

theorem objective_le_optimalValue {ι : Type*} [Countable ι] (p : ProbabilityVector ι)
    (t : ℕ) {h : ℝ} (hp : p ∈ ProbabilityVector.Feasible h) : p.objective t ≤ optimalValue t h := by
  obtain ⟨f,hf⟩ := Countable.exists_injective_nat ι
  let e : ι ↪ ℕ := ⟨f,hf⟩
  apply le_csSup (objective_image_bddAbove t h)
  refine ⟨ProbabilityVector.zeroExtend e p, ?_, ?_⟩
  · simpa only [ProbabilityVector.Feasible, Set.mem_ofPred_eq, ProbabilityVector.entropy_zeroExtend] using hp
  · exact ProbabilityVector.objective_zeroExtend _ _ _

theorem optimalValue_eq_of_globalMax {ι : Type*} [Countable ι] [Infinite ι]
    (p : ProbabilityVector ι) (t : ℕ) {h : ℝ} (hp : p ∈ ProbabilityVector.Feasible h)
    (hmax : ∀ q : ProbabilityVector ι, q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t) :
    optimalValue t h = p.objective t := by
  apply le_antisymm _ (objective_le_optimalValue p t hp)
  apply csSup_le
  · refine ⟨(ProbabilityVector.pointMass (0 : ℕ)).objective t, ProbabilityVector.pointMass 0, ?_, rfl⟩
    simp [ProbabilityVector.Feasible, ProbabilityVector.entropy_pointMass]
  · rintro _ ⟨q,hq,rfl⟩
    let e := Infinite.natEmbedding ι
    have hqe : ProbabilityVector.zeroExtend e q ∈ ProbabilityVector.Feasible h := by
      simpa only [ProbabilityVector.Feasible, Set.mem_ofPred_eq, ProbabilityVector.entropy_zeroExtend] using hq
    simpa only [ProbabilityVector.objective_zeroExtend] using hmax (ProbabilityVector.zeroExtend e q) hqe

/-- The finite list, with its light entry and all heavy entries from `k` through `M`. -/
def finiteCandidateValues (t : ℕ) (h : ℝ) : Finset ℝ := by
  classical
  exact insert (lightValue t h) ((Finset.Icc (entropySupportIndex h) (candidateCutoff t h)).image
    (heavyCandidateValue t h))

theorem finiteCandidateValues_nonempty (t : ℕ) (h : ℝ) : (finiteCandidateValues t h).Nonempty := by
  classical
  exact ⟨lightValue t h, Finset.mem_insert_self _ _⟩

def finiteCandidateMaximum (t : ℕ) (h : ℝ) : ℝ :=
  (finiteCandidateValues t h).max' (finiteCandidateValues_nonempty t h)

theorem lightValue_le_finiteCandidateMaximum (t : ℕ) (h : ℝ) :
    lightValue t h ≤ finiteCandidateMaximum t h := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem heavyValue_le_finiteCandidateMaximum (t : ℕ) (h : ℝ) (m : ℕ)
    (hm : entropySupportIndex h ≤ m) (hmM : m ≤ candidateCutoff t h) :
    heavyCandidateValue t h m ≤ finiteCandidateMaximum t h := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m,Finset.mem_Icc.mpr ⟨hm,hmM⟩,rfl⟩)

namespace ProbabilityVector
variable {ι : Type*}

/-- The truncated heavy family as actual probability vectors, retaining every embedding. -/
def CutoffHeavyCandidateForm (t : ℕ) (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  ∃ (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) (e : Fin (m+1) ↪ ι),
    entropySupportIndex h ≤ m ∧ m ≤ candidateCutoff t h ∧
    z ∈ Ioo (1 / ((m : ℝ)+1)) 1 ∧ branchEntropy m z = h ∧
    p = zeroExtend e (candidateVector m z hm hz)

theorem feasible_lightCandidateForm {h : ℝ} {p : ProbabilityVector ι} (hp : LightCandidateForm h p) :
    p ∈ Feasible h := by
  obtain ⟨a,hk,ha,e,_,he,rfl⟩ := hp
  simp only [Feasible, Set.mem_ofPred_eq, entropy_zeroExtend, entropy_candidateVector, he, le_refl]

theorem LightCandidateForm.objective_eq_lightValue {h : ℝ} {p : ProbabilityVector ι}
    (hp : LightCandidateForm h p) (hh : 0 < h) (t : ℕ) : p.objective t = lightValue t h := by
  obtain ⟨a,hk,ha,e,hroot,he,rfl⟩ := hp
  rw [objective_zeroExtend, objective_candidateVector]
  have haeq := light_candidate_root_unique hh hroot (lightRoot_spec hh).1 he (lightRoot_spec hh).2
  rw [haeq]
  rfl

theorem CutoffHeavyCandidateForm.feasible {t : ℕ} {h : ℝ} {p : ProbabilityVector ι}
    (hp : CutoffHeavyCandidateForm t h p) : p ∈ Feasible h := by
  obtain ⟨m,z,hm,hz,e,_,_,_,he,rfl⟩ := hp
  simp only [Feasible, Set.mem_ofPred_eq, entropy_zeroExtend, entropy_candidateVector, he, le_refl]

theorem CutoffHeavyCandidateForm.objective_le {t : ℕ} {h : ℝ} {p : ProbabilityVector ι}
    (hp : CutoffHeavyCandidateForm t h p) (hh : 0 < h) :
    p.objective t ≤ finiteCandidateMaximum t h := by
  obtain ⟨m,z,hm,hz,e,hk,hM,hroot,he,rfl⟩ := hp
  rw [objective_zeroExtend, objective_candidateVector,
    ← heavyRoot_eq_of_spec hh (heavy_domain_of_index hk) hroot he]
  exact heavyValue_le_finiteCandidateMaximum t h m hk hM

/-- No global maximizer can use a heavy multiplicity beyond the cutoff. -/
theorem candidate_complete_at_cutoff [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : p ∈ Feasible h)
    (hmax : ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) :
    LightCandidateForm h p ∨ CutoffHeavyCandidateForm t h p := by
  rcases p.candidate_complete_of_globalMax ht hh hp hmax with hl | hhvy
  · exact Or.inl hl
  · obtain ⟨m,z,hm,hz,e,hk,hroot,he,hrep⟩ := hhvy
    have hM : m ≤ candidateCutoff t h := by
      by_contra hnot
      have hj : (candidateCutoff t h : ℝ) < m := Nat.cast_lt.mpr (lt_of_not_ge hnot)
      have hMdom := heavy_domain_of_index (index_le_candidateCutoff t h)
      have hlt := branchObjective_lt_at_cutoff hh t ht hMdom
        (sample_entropy_le_candidateCutoff t h) hj
      rw [heavyRoot_eq_of_spec hh (heavy_domain_of_index hk) hroot he] at hlt
      let q := zeroExtend (Infinite.natEmbedding ι)
        (canonicalHeavy h hh (candidateCutoff t h) (index_le_candidateCutoff t h))
      have hq : q ∈ Feasible h := by
        simpa only [q, Feasible, Set.mem_ofPred_eq, entropy_zeroExtend] using
          canonicalHeavy_feasible hh (candidateCutoff t h) (index_le_candidateCutoff t h)
      have hle := hmax q hq
      simp only [hrep, q, objective_zeroExtend, objective_candidateVector,
        objective_canonicalHeavy, heavyCandidateValue] at hle
      exact (not_lt_of_ge hle) hlt
    exact Or.inr ⟨m,z,hm,hz,e,hk,hM,hroot,he,hrep⟩

end ProbabilityVector

/-- Manuscript finite maximum formula, with every tied entry retained in the list. -/
theorem optimalValue_eq_finiteCandidateMaximum {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) :
    optimalValue t h = finiteCandidateMaximum t h := by
  classical
  apply le_antisymm
  · obtain ⟨p,_,hp,hmax⟩ := ProbabilityVector.exists_global_maximizer_countable t h hh.le
    rw [optimalValue_eq_of_globalMax p t hp hmax]
    rcases p.candidate_complete_at_cutoff ht hh hp hmax with hl | hv
    · rw [hl.objective_eq_lightValue hh]
      exact lightValue_le_finiteCandidateMaximum t h
    · exact hv.objective_le hh
  · apply Finset.max'_le
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [← objective_canonicalLight t hh]
      exact objective_le_optimalValue _ t (canonicalLight_feasible hh)
    · obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hv
      have hkm := (Finset.mem_Icc.mp hm).1
      rw [← objective_canonicalHeavy t hh m hkm]
      exact objective_le_optimalValue _ t (canonicalHeavy_feasible hh m hkm)

namespace ProbabilityVector
variable {ι : Type*}

/-- Exact equality classification on any countably infinite alphabet. No uniqueness
is imposed: every candidate attaining the finite maximum is a global maximizer. -/
theorem globalMax_iff_finite_candidate [Countable ι] [Infinite ι]
    (p : ProbabilityVector ι) {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) ↔
    (LightCandidateForm h p ∨ CutoffHeavyCandidateForm t h p) ∧
      p.objective t = finiteCandidateMaximum t h := by
  constructor
  · rintro ⟨hp,hmax⟩
    refine ⟨p.candidate_complete_at_cutoff ht hh hp hmax, ?_⟩
    exact (optimalValue_eq_of_globalMax p t hp hmax).symm.trans
      (optimalValue_eq_finiteCandidateMaximum ht hh)
  · rintro ⟨hc,he⟩
    refine ⟨hc.elim feasible_lightCandidateForm (fun hp => hp.feasible), ?_⟩
    intro q hq
    rw [he, ← optimalValue_eq_finiteCandidateMaximum ht hh]
    exact objective_le_optimalValue q t hq

private theorem support_zeroExtend_card_le {n : ℕ} (e : Fin n ↪ ι) (q : ProbabilityVector (Fin n)) :
    (Function.support (zeroExtend e q).coord).Finite ∧
      (Function.support (zeroExtend e q).coord).ncard ≤ n := by
  have hsub : Function.support (zeroExtend e q).coord ⊆ Set.range e := by
    intro i hi
    by_contra hn
    exact hi (coord_zeroExtend_of_not_mem_range _ _ _ hn)
  refine ⟨(Set.finite_range e).subset hsub, ?_⟩
  have hc := Set.ncard_le_ncard hsub (Set.finite_range e)
  simpa only [Set.ncard_range_of_injective e.injective, Nat.card_fin] using hc

/-- The finite comparison theorem bounds the number of positive coordinates of
every maximizer, independently of its chosen embedding or zero coordinates. -/
theorem support_card_le_candidateCutoff [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : p ∈ Feasible h)
    (hmax : ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) :
    (Function.support p.coord).Finite ∧ (Function.support p.coord).ncard ≤ candidateCutoff t h+1 := by
  rcases p.candidate_complete_at_cutoff ht hh hp hmax with hl | hv
  · obtain ⟨a,hk,ha,e,_,_,rfl⟩ := hl
    obtain ⟨hf,hcard⟩ := support_zeroExtend_card_le e (candidateVector _ a hk ha)
    exact ⟨hf,hcard.trans (Nat.add_le_add_right (index_le_candidateCutoff t h) 1)⟩
  · obtain ⟨m,z,hm,hz,e,_,hmM,_,_,rfl⟩ := hv
    obtain ⟨hf,hcard⟩ := support_zeroExtend_card_le e (candidateVector m z hm hz)
    exact ⟨hf,hcard.trans (Nat.add_le_add_right hmM 1)⟩

end ProbabilityVector
end
end EntropyConstrainedMissingMass
