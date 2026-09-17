import EntropyConstrainedMissingMass.UniformForm

/-! Completeness of the entropy-matched light and heavy candidates before truncation. -/

set_option backward.isDefEq.respectTransparency false
open Set
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The real branch entropy is nonnegative for every genuine candidate law. -/
theorem branchEntropy_nat_nonneg {m : ℕ} (hm : 0 < m) {z : ℝ} (hz : z ∈ Icc 0 1) :
    0 ≤ branchEntropy m z := by
  rw [← sum_negMulLog_candidateCoord hm]
  exact Finset.sum_nonneg (fun i _ => (candidateVector m z hm hz).entropy_term_nonneg i)

/-- The light interval identifies its multiplicity with floor(exp h). -/
theorem light_entropy_index {m : ℕ} (hm : 0 < m) {z h : ℝ}
    (hz : z ∈ Ico 0 (1 / ((m : ℝ) + 1))) (he : branchEntropy m z = h) :
    entropySupportIndex h = m := by
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlo : Real.log m ≤ h := by
    rw [← he, ← branchEntropy_zero]
    exact (strictMonoOn_branchEntropy hmreal).monotoneOn
      ⟨le_refl 0, by positivity⟩ ⟨hz.1, hz.2.le⟩ hz.1
  have hhi : h < Real.log ((m : ℝ) + 1) := by
    rw [← he, ← branchEntropy_uniform hmreal]
    exact strictMonoOn_branchEntropy hmreal ⟨hz.1, hz.2.le⟩
      ⟨by positivity, le_refl _⟩ hz.2
  exact (Nat.floor_eq_iff (Real.exp_pos h).le).mpr
    ⟨(Real.log_le_iff_le_exp hmreal).mp hlo,
      (Real.lt_log_iff_exp_lt (by positivity)).mp hhi⟩

/-- Every interior heavy entropy root has multiplicity at least floor(exp h). -/
theorem heavy_entropy_index {m : ℕ} (hm : 0 < m) {z h : ℝ}
    (hz : z ∈ Ioo (1 / ((m : ℝ) + 1)) 1) (he : branchEntropy m z = h) :
    entropySupportIndex h ≤ m := by
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hhi : h < Real.log ((m : ℝ) + 1) := by
    rw [← he, ← branchEntropy_uniform hmreal]
    exact strictAntiOn_branchEntropy hmreal ⟨le_refl _, by
      apply (div_le_one (by positivity)).mpr; linarith⟩ ⟨hz.1.le, hz.2.le⟩ hz.1
  apply Nat.le_of_lt_succ
  apply (Nat.floor_lt' (Nat.succ_ne_zero m)).mpr
  simpa only [Nat.cast_succ] using
    (Real.lt_log_iff_exp_lt (by positivity : 0 < (m : ℝ) + 1)).mp hhi

/-- The light parameter remains unique when the uniform endpoint is included. -/
theorem light_candidate_root_unique {h a b : ℝ} (hh : 0 < h)
    (ha : a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)))
    (hb : b ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)))
    (hea : branchEntropy (entropySupportIndex h) a = h)
    (heb : branchEntropy (entropySupportIndex h) b = h) : a = b :=
  (strictMonoOn_branchEntropy (Nat.cast_pos.mpr (entropySupportIndex_pos hh.le))).injOn
    ⟨ha.1, ha.2.le⟩ ⟨hb.1, hb.2.le⟩ (hea.trans heb.symm)

/-- Each heavy multiplicity has a unique entropy-matched parameter. -/
theorem heavy_candidate_root_unique {m : ℕ} (hm : 0 < m) {h z w : ℝ}
    (hz : z ∈ Ioo (1 / ((m : ℝ) + 1)) 1) (hw : w ∈ Ioo (1 / ((m : ℝ) + 1)) 1)
    (hez : branchEntropy m z = h) (hew : branchEntropy m w = h) : z = w :=
  (strictAntiOn_branchEntropy (Nat.cast_pos.mpr hm)).injOn
    ⟨hz.1.le, hz.2.le⟩ ⟨hw.1.le, hw.2.le⟩ (hez.trans hew.symm)

/-- Integer entropy endpoints are represented by zero exceptional mass, not discarded. -/
theorem light_candidate_zero_iff {h a : ℝ} (hh : 0 < h)
    (ha : a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)))
    (he : branchEntropy (entropySupportIndex h) a = h) :
    a = 0 ↔ h = Real.log (entropySupportIndex h) := by
  have hi := (light_entropy_eq_log_iff
    (Nat.cast_pos.mpr (entropySupportIndex_pos hh.le)) ⟨ha.1, ha.2.le⟩).symm
  simpa only [he] using hi

/-- Swapping the two atoms exchanges the light and heavy binary parametrizations. -/
theorem binary_candidate_swap (z : ℝ) (hz : z ∈ Icc 0 1) :
    candidateVector 1 z (by decide) hz =
      ProbabilityVector.reindex (Equiv.swap (0 : Fin 2) 1)
        (candidateVector 1 (1 - z) (by decide) ⟨by linarith [hz.2], by linarith [hz.1]⟩) := by
  apply Subtype.ext
  apply lp.ext
  funext i
  change (candidateVector 1 z (by decide) hz).coord i =
    (ProbabilityVector.reindex (Equiv.swap (0 : Fin 2) 1) _).coord i
  rw [ProbabilityVector.coord_reindex]
  fin_cases i
  · change z = candidateCoord 1 (1 - z) (Fin.succ (0 : Fin 1))
    rw [candidateCoord_succ]
    norm_num
  · change candidateCoord 1 z (Fin.succ (0 : Fin 1)) = 1 - z
    rw [candidateCoord_succ]
    norm_num

/-- Binary branch entropy is unchanged by exchanging its atoms. -/
theorem binary_branchEntropy_symmetry (z : ℝ) : branchEntropy 1 (1 - z) = branchEntropy 1 z := by
  simp only [branchEntropy, div_one]
  rw [show 1 - (1 - z) = z by ring]
  ring

/-- For 0<h<log 2 the unique heavy binary root is exactly one minus the light root. -/
theorem binary_entropy_root_duplicate {h a z : ℝ} (hh : 0 < h) (hh2 : h < Real.log 2)
    (ha : a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)))
    (hea : branchEntropy (entropySupportIndex h) a = h)
    (hz : z ∈ Ioo (1 / ((1 : ℝ) + 1)) 1) (hez : branchEntropy 1 z = h) :
    entropySupportIndex h = 1 ∧ z = 1 - a := by
  have hk : entropySupportIndex h = 1 := by
    apply (Nat.floor_eq_iff (Real.exp_pos h).le).mpr
    constructor
    · simpa using (Real.one_le_exp_iff.mpr hh.le)
    · norm_num only [Nat.cast_one]
      convert (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)).mp hh2 using 1
  rw [hk] at ha hea
  have ha0 : 0 < a := by
    apply lt_of_le_of_ne ha.1
    intro hzero
    have : h = 0 := by simpa [← hzero, branchEntropy_zero] using hea.symm
    linarith
  refine ⟨hk, heavy_candidate_root_unique (m := 1) (by decide) (by simpa using hz) ?_
    (by simpa using hez) ?_⟩
  · norm_num at ha ⊢
    constructor <;> linarith [ha.2]
  · norm_num only [Nat.cast_one] at hea ⊢
    rw [binary_branchEntropy_symmetry]
    exact hea

namespace ProbabilityVector
variable {ι : Type*}

/-- The unique light root, represented as an actual law with optional zero exceptional atom. -/
def LightCandidateForm (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  ∃ (a : ℝ) (hk : 0 < entropySupportIndex h) (ha : a ∈ Icc 0 1)
    (e : Fin (entropySupportIndex h + 1) ↪ ι),
    a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)) ∧
    branchEntropy (entropySupportIndex h) a = h ∧
    p = zeroExtend e (candidateVector (entropySupportIndex h) a hk ha)

/-- An entropy-matched heavy root with multiplicity at least the entropy support index. -/
def HeavyCandidateForm (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  ∃ (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) (e : Fin (m + 1) ↪ ι),
    entropySupportIndex h ≤ m ∧ z ∈ Ioo (1 / ((m : ℝ) + 1)) 1 ∧
    branchEntropy m z = h ∧ p = zeroExtend e (candidateVector m z hm hz)

/-- Relabeling the finite law composes with its embedding into the alphabet. -/
theorem zeroExtend_reindex {κ γ : Type*} (e : κ ↪ ι) (r : γ ≃ κ)
    (q : ProbabilityVector γ) :
    zeroExtend e (reindex r q) = zeroExtend (r.toEmbedding.trans e) q := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext j
  change (zeroExtend e (reindex r q)).coord j = (zeroExtend (r.toEmbedding.trans e) q).coord j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [coord_zeroExtend_apply, coord_reindex]
    have he : (r.toEmbedding.trans e) (r.symm i) = e i := by simp
    rw [← he, coord_zeroExtend_apply]
  · rw [coord_zeroExtend_of_not_mem_range _ _ _ hj,
      coord_zeroExtend_of_not_mem_range _ _ _ (by
        rintro ⟨i, hi⟩; exact hj ⟨r i, hi⟩)]

/-- The heavy binary candidate is also the light candidate after swapping its atoms. -/
theorem binary_heavy_form_is_light {h z : ℝ}
    (hz : z ∈ Ioo (1 / ((1 : ℝ) + 1)) 1) (he : branchEntropy 1 z = h)
    (e : Fin 2 ↪ ι) :
    LightCandidateForm h (zeroExtend e (candidateVector 1 z (by decide)
      ⟨by linarith [hz.1], hz.2.le⟩)) := by
  have ha : 1 - z ∈ Ico 0 (1 / ((1 : ℝ) + 1)) := by
    constructor <;> linarith [hz.1, hz.2]
  have hae : branchEntropy 1 (1 - z) = h := (binary_branchEntropy_symmetry z).trans he
  have hk := light_entropy_index (m := 1) (z := 1 - z) (h := h) (by decide)
    (by simpa using ha) (by simpa using hae)
  unfold LightCandidateForm
  rw [hk]
  refine ⟨1 - z, by decide, ⟨by linarith [hz.2], by linarith [hz.1]⟩,
    (Equiv.swap (0 : Fin 2) 1).toEmbedding.trans e, by simpa using ha, by simpa using hae, ?_⟩
  rw [binary_candidate_swap, zeroExtend_reindex]

/-- Exact candidate completeness for local maximizers on an infinite alphabet. -/
theorem candidate_complete_of_localMax [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : LocalMaximizer t h p) :
    LightCandidateForm h p ∨ HeavyCandidateForm h p := by
  classical
  have he : p.entropy = ENNReal.ofReal h := p.entropy_saturation_of_localMax ht hp
  by_cases hu : p.UniformOnSupport
  · obtain ⟨n, hn, e, hrep, hent⟩ := p.uniform_form_entropy
      (p.finite_support_of_localMax ht hp) hu
    have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlog : Real.log (n : ℝ) = h :=
      (ENNReal.ofReal_eq_ofReal_iff hlogpos hh.le).mp (hent.symm.trans he)
    have hk : entropySupportIndex h = n := by
      unfold entropySupportIndex
      rw [← hlog, Real.exp_log (Nat.cast_pos.mpr hn)]
      exact Nat.floor_natCast n
    left
    unfold LightCandidateForm
    rw [hk]
    refine ⟨0, hn, by constructor <;> norm_num, e, ⟨le_refl 0, by positivity⟩, ?_, hrep⟩
    simpa only [branchEntropy_zero] using hlog
  · obtain ⟨m, z, hm, hz, e, hneq, hrep⟩ := p.exceptional_form_of_localMax ht hp hu
    have hzc : z ∈ Icc 0 1 := ⟨hz.1.le, hz.2.le⟩
    have hbranch : branchEntropy m z = h := by
      rw [hrep, entropy_zeroExtend, entropy_candidateVector] at he
      exact (ENNReal.ofReal_eq_ofReal_iff (branchEntropy_nat_nonneg hm hzc) hh.le).mp he
    have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hunif : z ≠ 1 / ((m : ℝ) + 1) := by
      intro heq
      apply hneq
      rw [heq]
      field_simp
      ring
    rcases lt_or_gt_of_ne hunif with hl | hhvy
    · have hk := light_entropy_index hm ⟨hz.1.le, hl⟩ hbranch
      left
      unfold LightCandidateForm
      rw [hk]
      exact ⟨z, hm, hzc, e, ⟨hz.1.le, hl⟩, hbranch, hrep⟩
    · right
      exact ⟨m, z, hm, hzc, e, heavy_entropy_index hm ⟨hhvy, hz.2⟩ hbranch,
        ⟨hhvy, hz.2⟩, hbranch, hrep⟩

/-- Global maximizers inherit the same complete list; all zero coordinates are preserved. -/
theorem candidate_complete_of_globalMax [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : p ∈ Feasible h)
    (hmax : ∀ (q : ProbabilityVector ι), q ∈ Feasible h → q.objective t ≤ p.objective t) :
    LightCandidateForm h p ∨ HeavyCandidateForm h p := by
  apply p.candidate_complete_of_localMax ht hh
  exact ⟨hp, (show IsMaxOn (fun q : ProbabilityVector ι => q.objective t) (Feasible h) p from
    hmax).isLocalMaxOn⟩

end ProbabilityVector
end
end EntropyConstrainedMissingMass
