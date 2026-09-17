import EntropyConstrainedMissingMass.FiniteAlphabetCandidates

/-! Appendix C: the exact finite-alphabet candidate list and its equality classification.
The saturated-list filter asks for realization on the actual alphabet. This retains
zero-coordinate endpoint representations precisely when their positive support fits. -/
open Set
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass
noncomputable section

namespace ProbabilityVector

def SaturatedFiniteCandidateForm {N : ℕ} (t : ℕ) (h : ℝ) (p : ProbabilityVector (Fin N)) : Prop :=
  LightCandidateForm h p.finiteToNat ∨ CutoffHeavyCandidateForm t h p.finiteToNat

def StationaryFiniteCandidateForm {m : ℕ} (hm : 0 < m) (t : ℕ) (h : ℝ)
    (p : ProbabilityVector (Fin (m+1))) : Prop :=
  ∃ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (e : Fin (m+1) ↪ Fin (m+1)),
    z ∈ finiteStationaryRoots m t h ∧
    p = zeroExtend e (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩)

theorem SaturatedFiniteCandidateForm.feasible {N t : ℕ} {h : ℝ} {p : ProbabilityVector (Fin N)}
    (hp : SaturatedFiniteCandidateForm t h p) : p ∈ Feasible h := by
  have hf : p.finiteToNat ∈ Feasible h := hp.elim feasible_lightCandidateForm (fun he => he.feasible)
  simpa only [Feasible,Set.mem_ofPred_eq,entropy_finiteToNat] using hf

theorem SaturatedFiniteCandidateForm.value_mem {N t : ℕ} {h : ℝ} {p : ProbabilityVector (Fin N)}
    (hp : SaturatedFiniteCandidateForm t h p) (hh : 0 < h) : p.objective t ∈ finiteCandidateValues t h := by
  classical
  rw [← objective_finiteToNat p t]
  rcases hp with hl | hv
  · rw [hl.objective_eq_lightValue hh]
    exact Finset.mem_insert_self _ _
  · obtain ⟨m,z,hm,hz,e,hk,hM,hroot,he,hrep⟩ := hv
    rw [hrep,objective_zeroExtend,objective_candidateVector,
      ← heavyRoot_eq_of_spec hh (heavy_domain_of_index hk) hroot he]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m,Finset.mem_Icc.mpr ⟨hk,hM⟩,rfl⟩)

theorem StationaryFiniteCandidateForm.feasible {m t : ℕ} {hm : 0 < m} {h : ℝ}
    {p : ProbabilityVector (Fin (m+1))} (hp : StationaryFiniteCandidateForm hm t h p) (ht : 1 ≤ t) :
    p ∈ Feasible h := by
  obtain ⟨z,hz,e,hroot,rfl⟩ := hp
  have hb := ((mem_finiteStationaryRoots hm ht h z).mp hroot).2.1
  change (zeroExtend e (candidateVector m z hm _)).entropy ≤ ENNReal.ofReal h
  rw [entropy_zeroExtend,entropy_candidateVector]
  exact ENNReal.ofReal_le_ofReal hb

/-- Every finite-alphabet maximum belongs to one of the two actual candidate families. -/
theorem finite_alphabet_candidate_complete {m t : ℕ} (hm : 0 < m) (p : ProbabilityVector (Fin (m+1)))
    {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : p ∈ Feasible h)
    (hmax : ∀ q : ProbabilityVector (Fin (m+1)), q ∈ Feasible h → q.objective t ≤ p.objective t) :
    SaturatedFiniteCandidateForm t h p ∨ StationaryFiniteCandidateForm hm t h p := by
  have hlocal : LocalMaximizer t h p := ⟨hp,(show IsMaxOn (fun q => q.objective t) (Feasible h) p from hmax).isLocalMaxOn⟩
  rcases lt_or_eq_of_le (show p.entropy ≤ ENNReal.ofReal h from hp) with hslack | he
  · exact Or.inr (p.finite_candidate_complete_slack hm ht hlocal hslack)
  · exact Or.inl (p.finite_candidate_complete_saturated ht hh hlocal he hmax)

end ProbabilityVector

/-- Saturated entries retained exactly when an actual law on `N` symbols realizes
that entry's candidate form. This is the support-fitting restriction, allowing zeros. -/
def saturatedFiniteValues (N t : ℕ) (h : ℝ) : Finset ℝ := by
  classical
  exact (finiteCandidateValues t h).filter (fun v => ∃ p : ProbabilityVector (Fin N),
    p.SaturatedFiniteCandidateForm t h ∧ p.objective t = v)

/-- The full finite list: fitting saturated candidates plus feasible interior roots
of the stationary polynomial for the full alphabet of `m+1` symbols. -/
def finiteAlphabetValueList (m t : ℕ) (h : ℝ) : Finset ℝ := by
  classical
  exact saturatedFiniteValues (m+1) t h ∪ (finiteStationaryRoots m t h).image (branchObjective m t)

theorem objective_mem_finiteAlphabetValueList {m t : ℕ} (hm : 0 < m)
    (p : ProbabilityVector (Fin (m+1))) {h : ℝ} (hh : 0 < h)
    (hc : p.SaturatedFiniteCandidateForm t h ∨ p.StationaryFiniteCandidateForm hm t h) :
    p.objective t ∈ finiteAlphabetValueList m t h := by
  classical
  rcases hc with hs | hi
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs.value_mem hh,⟨p,hs,rfl⟩⟩)
  · obtain ⟨z,hz,e,hr,rfl⟩ := hi
    rw [ProbabilityVector.objective_zeroExtend,objective_candidateVector]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hr,rfl⟩)

theorem exists_feasible_of_mem_finiteAlphabetValueList {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t)
    (h v : ℝ) (hv : v ∈ finiteAlphabetValueList m t h) :
    ∃ p : ProbabilityVector (Fin (m+1)), p ∈ ProbabilityVector.Feasible h ∧ p.objective t = v := by
  classical
  rcases Finset.mem_union.mp hv with hs | hi
  · obtain ⟨_,p,hp,he⟩ := Finset.mem_filter.mp hs
    exact ⟨p,hp.feasible,he⟩
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hi
    have hr := (mem_finiteStationaryRoots hm ht h z).mp hz
    refine ⟨candidateVector m z hm ⟨hr.1.1.le,hr.1.2.le⟩,?_,objective_candidateVector _ _ _ _ _⟩
    change (candidateVector m z hm _).entropy ≤ ENNReal.ofReal h
    rw [entropy_candidateVector]
    exact ENNReal.ofReal_le_ofReal hr.2.1

theorem finiteAlphabetValueList_nonempty {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t) {h : ℝ} (hh : 0 < h) :
    (finiteAlphabetValueList m t h).Nonempty := by
  obtain ⟨p,hp,hmax⟩ := ProbabilityVector.exists_global_maximizer_finite (ι := Fin (m+1)) t h hh.le
  exact ⟨p.objective t, objective_mem_finiteAlphabetValueList hm p hh
    (p.finite_alphabet_candidate_complete hm ht hh hp hmax)⟩

/-- Maximum over the original finite-alphabet feasible set. -/
def finiteAlphabetOptimalValue (N t : ℕ) (h : ℝ) : ℝ :=
  sSup ((fun p : ProbabilityVector (Fin N) => p.objective t) '' ProbabilityVector.Feasible h)

theorem finiteAlphabetOptimalValue_eq_of_globalMax {N t : ℕ} {h : ℝ}
    (p : ProbabilityVector (Fin N)) (hp : p ∈ ProbabilityVector.Feasible h)
    (hmax : ∀ q : ProbabilityVector (Fin N), q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t) :
    finiteAlphabetOptimalValue N t h = p.objective t := by
  apply le_antisymm
  · exact csSup_le ⟨p.objective t,p,hp,rfl⟩ (by rintro _ ⟨q,hq,rfl⟩; exact hmax q hq)
  · apply le_csSup
    · refine ⟨1,?_⟩
      rintro _ ⟨q,_,rfl⟩
      exact q.objective_le_one t
    · exact ⟨p,hp,rfl⟩

/-- Appendix C's exact largest-value formula on an alphabet of `m+1≥2` symbols. -/
theorem finiteAlphabetOptimalValue_eq_max {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t) {h : ℝ} (hh : 0 < h) :
    finiteAlphabetOptimalValue (m+1) t h =
      (finiteAlphabetValueList m t h).max' (finiteAlphabetValueList_nonempty hm ht hh) := by
  obtain ⟨p,hp,hmax⟩ := ProbabilityVector.exists_global_maximizer_finite (ι := Fin (m+1)) t h hh.le
  rw [finiteAlphabetOptimalValue_eq_of_globalMax p hp hmax]
  apply le_antisymm
  · exact Finset.le_max' _ _ (objective_mem_finiteAlphabetValueList hm p hh
      (p.finite_alphabet_candidate_complete hm ht hh hp hmax))
  · apply Finset.max'_le
    intro v hv
    obtain ⟨q,hq,he⟩ := exists_feasible_of_mem_finiteAlphabetValueList hm ht h v hv
    rw [← he]
    exact hmax q hq

/-- Exact optimizer classification, retaining every tie and every permutation. -/
theorem finiteAlphabet_globalMax_iff {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t) {h : ℝ} (hh : 0 < h)
    (p : ProbabilityVector (Fin (m+1))) :
    (p ∈ ProbabilityVector.Feasible h ∧ ∀ q : ProbabilityVector (Fin (m+1)),
      q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t) ↔
    (p.SaturatedFiniteCandidateForm t h ∨ p.StationaryFiniteCandidateForm hm t h) ∧
      p.objective t = (finiteAlphabetValueList m t h).max' (finiteAlphabetValueList_nonempty hm ht hh) := by
  constructor
  · rintro ⟨hp,hmax⟩
    exact ⟨p.finite_alphabet_candidate_complete hm ht hh hp hmax,
      (finiteAlphabetOptimalValue_eq_of_globalMax p hp hmax).symm.trans (finiteAlphabetOptimalValue_eq_max hm ht hh)⟩
  · rintro ⟨hc,he⟩
    refine ⟨hc.elim (fun hs => hs.feasible) (fun hi => hi.feasible ht),?_⟩
    intro q hq
    rw [he, ← finiteAlphabetOptimalValue_eq_max hm ht hh]
    apply le_csSup
    · refine ⟨1,?_⟩
      rintro _ ⟨r,_,rfl⟩
      exact r.objective_le_one t
    · exact ⟨q,hq,rfl⟩

/-- The full-support uniform law is included as the stationary root `1/N`. -/
theorem uniform_mem_finiteStationaryRoots {m t : ℕ} (hm : 0 < m) (ht : 1 ≤ t)
    {h : ℝ} (hh : Real.log ((m : ℝ)+1) ≤ h) :
    1/((m : ℝ)+1) ∈ finiteStationaryRoots m t h := by
  apply (mem_finiteStationaryRoots hm ht h _).mpr
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  refine ⟨⟨by positivity,(div_lt_one (by positivity)).mpr (by linarith)⟩,?_,?_⟩
  · simpa only [branchEntropy_uniform hmreal] using hh
  · have he : (1-1/((m : ℝ)+1))/(m : ℝ) = 1/((m : ℝ)+1) := by field_simp; ring
    rw [he]

/-- The zero-entropy endpoint consists exactly of point masses, and all are maxima. -/
theorem finiteAlphabet_globalMax_zero_iff {N t : ℕ} (ht : 1 ≤ t) (p : ProbabilityVector (Fin N)) :
    (p ∈ ProbabilityVector.Feasible 0 ∧ ∀ q : ProbabilityVector (Fin N),
      q ∈ ProbabilityVector.Feasible 0 → q.objective t ≤ p.objective t) ↔
    ∃ i, p.coord i = 1 ∧ ∀ j, j ≠ i → p.coord j = 0 := by
  rw [← p.entropy_eq_zero_iff]
  constructor
  · intro hp
    exact p.feasible_zero_iff.mp hp.1
  · intro he
    refine ⟨p.feasible_zero_iff.mpr he,?_⟩
    intro q hq
    rw [p.objective_eq_zero_of_entropy_eq_zero (by omega) he,
      q.objective_eq_zero_of_entropy_eq_zero (by omega) (q.feasible_zero_iff.mp hq)]

/-- The original finite optimization value is zero at entropy budget zero. -/
theorem finiteAlphabetOptimalValue_zero {N t : ℕ} (hN : 0 < N) (ht : 1 ≤ t) :
    finiteAlphabetOptimalValue N t 0 = 0 := by
  let p := ProbabilityVector.pointMass (⟨0,hN⟩ : Fin N)
  have hp := ProbabilityVector.pointMass_feasible (⟨0,hN⟩ : Fin N) 0
  have he : p.entropy = 0 := ProbabilityVector.entropy_pointMass _
  have hmax : ∀ q : ProbabilityVector (Fin N), q ∈ ProbabilityVector.Feasible 0 →
      q.objective t ≤ p.objective t := by
    intro q hq
    rw [p.objective_eq_zero_of_entropy_eq_zero (by omega) he,
      q.objective_eq_zero_of_entropy_eq_zero (by omega) (q.feasible_zero_iff.mp hq)]
  rw [finiteAlphabetOptimalValue_eq_of_globalMax p hp hmax,
    p.objective_eq_zero_of_entropy_eq_zero (by omega) he]

/-- A one-symbol alphabet has value zero at every entropy budget. -/
theorem finiteAlphabetOptimalValue_one {t : ℕ} (ht : 1 ≤ t) (h : ℝ) :
    finiteAlphabetOptimalValue 1 t h = 0 := by
  let p := ProbabilityVector.pointMass (0 : Fin 1)
  have hp := ProbabilityVector.pointMass_feasible (0 : Fin 1) h
  have hmax : ∀ q : ProbabilityVector (Fin 1), q ∈ ProbabilityVector.Feasible h →
      q.objective t ≤ p.objective t := by
    intro q _
    rw [p.objective_eq_zero_of_entropy_eq_zero (by omega) p.entropy_eq_zero_of_subsingleton,
      q.objective_eq_zero_of_entropy_eq_zero (by omega) q.entropy_eq_zero_of_subsingleton]
  rw [finiteAlphabetOptimalValue_eq_of_globalMax p hp hmax,
    p.objective_eq_zero_of_entropy_eq_zero (by omega) p.entropy_eq_zero_of_subsingleton]

end
end EntropyConstrainedMissingMass
