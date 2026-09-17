import EntropyConstrainedMissingMass.CrossingEndpoints

/-! Finite phase intervals, including endpoint ties, for the candidate family. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

namespace ProbabilityVector
def GlobalMaximizer {ι : Type*} (t : ℕ) (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  p ∈ Feasible h ∧ ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t
end ProbabilityVector

theorem finiteCandidateMaximum_le_iff (t : ℕ) (h v : ℝ) :
    finiteCandidateMaximum t h ≤ v ↔ lightValue t h ≤ v ∧
      ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h → heavyCandidateValue t h j ≤ v := by
  classical
  simp only [finiteCandidateMaximum, Finset.max'_le_iff, finiteCandidateValues,
    Finset.mem_insert, Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro hh
    refine ⟨hh _ (Or.inl rfl), fun j hj hcut => hh _ (Or.inr ⟨j, ⟨hj, hcut⟩, rfl⟩)⟩
  · rintro ⟨hl, hh⟩ v (rfl | ⟨j, hj, rfl⟩)
    · exact hl
    · exact hh j hj.1 hj.2

theorem canonicalHeavy_globalMax_iff_comparisons {h : ℝ} {m t : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (ht : 1 ≤ t) :
    ProbabilityVector.GlobalMaximizer t h (canonicalHeavy h hh m hm) ↔
      lightRealValue h t ≤ heavyValue h t m ∧
      ∀ j, entropySupportIndex h ≤ j → heavyValue h t j ≤ heavyValue h t m := by
  have hconv (j : ℕ) (hj : entropySupportIndex h ≤ j) :
      (canonicalHeavy h hh j hj).objective t = heavyValue h t j := by
    rw [objective_canonicalHeavy, heavyValue_integer_eq hh (heavy_domain_of_index hj)]
    rfl
  have hlconv : (canonicalLight h hh).objective t = lightRealValue h t := by
    rw [objective_canonicalLight, lightRealValue_nat]
  constructor
  · rintro ⟨_, hmglob⟩
    refine ⟨?_, fun j hj => ?_⟩
    · simpa only [hconv m hm, hlconv] using hmglob (canonicalLight h hh) (canonicalLight_feasible hh)
    · simpa only [hconv j hj, hconv m hm] using hmglob (canonicalHeavy h hh j hj) (canonicalHeavy_feasible hh j hj)
  · rintro ⟨hl, hv⟩
    refine ⟨canonicalHeavy_feasible hh m hm, fun q hq => ?_⟩
    rw [hconv m hm]
    apply (objective_le_optimalValue q t hq).trans
    rw [optimalValue_eq_finiteCandidateMaximum ht hh]
    apply (finiteCandidateMaximum_le_iff _ _ _).mpr
    refine ⟨by simpa only [lightRealValue_nat] using hl, fun j hj _ => ?_⟩
    simpa only [heavyValue_integer_eq hh (heavy_domain_of_index hj), heavyCandidateValue] using hv j hj

/-- Winning heavy multiplicities cannot decrease when the sample size increases. -/
theorem winning_heavy_multiplicity_mono {h : ℝ} {t₁ t₂ i j : ℕ}
    (hh : 0 < h) (hi : entropySupportIndex h ≤ i) (hj : entropySupportIndex h ≤ j)
    (ht₁ : 1 ≤ t₁) (ht : t₁ < t₂)
    (hwin₁ : ProbabilityVector.GlobalMaximizer t₁ h (canonicalHeavy h hh i hi))
    (hwin₂ : ProbabilityVector.GlobalMaximizer t₂ h (canonicalHeavy h hh j hj)) : i ≤ j := by
  by_contra hji
  have hji' : j < i := Nat.lt_of_not_ge hji
  have hw₁ := ((canonicalHeavy_globalMax_iff_comparisons hh hi ht₁).mp hwin₁).2 j hj
  have hw₂ := ((canonicalHeavy_globalMax_iff_comparisons hh hj (by omega)).mp hwin₂).2 i hi
  have hs₁ : (0 : ℝ) < t₁ := by exact_mod_cast (show 0 < t₁ by omega)
  have hlt := heavy_comparison_persists (s₂ := (t₂ : ℝ)) hh (heavy_domain_of_index hj) hji' hs₁
    (by exact_mod_cast ht) hw₁
  exact not_lt_of_ge hw₂ hlt

/-- The finite comparison cutoff attached to the adjacent heavy-heavy crossing. -/
def phaseCutoff (h : ℝ) (m : ℕ) : ℕ := max (m + 1) ⌈h * heavyCrossing h m (m + 1) + 1⌉₊

theorem phaseCutoff_ge_succ (h : ℝ) (m : ℕ) : m + 1 ≤ phaseCutoff h m := le_max_left _ _

theorem phaseCutoff_ge_sample_entropy {h s : ℝ} {m : ℕ} (hh : 0 ≤ h)
    (hs : s ≤ heavyCrossing h m (m + 1)) : s * h + 1 ≤ (phaseCutoff h m : ℝ) := by
  calc
    s * h + 1 ≤ h * heavyCrossing h m (m + 1) + 1 := by nlinarith
    _ ≤ (⌈h * heavyCrossing h m (m + 1) + 1⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (phaseCutoff h m : ℝ) := Nat.cast_le.mpr (le_max_right _ _)

/-- All larger heavy competitors reduce to the source's finite range through `R_m`. -/
theorem heavy_all_comparisons_iff_finite {h s : ℝ} {m : ℕ} (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hs : 1 ≤ s) :
    (∀ j, entropySupportIndex h ≤ j → heavyValue h s j ≤ heavyValue h s m) ↔
      (∀ j, entropySupportIndex h ≤ j → j < m → heavyCrossing h j m ≤ s) ∧
      (∀ j, m < j → j ≤ phaseCutoff h m → s ≤ heavyCrossing h m j) := by
  have hs0 : 0 < s := by linarith
  have hdom := heavy_domain_of_index hm
  constructor
  · intro hall
    exact ⟨fun j hj hjm => (heavy_comparison_iff hh (heavy_domain_of_index hj) hjm hs0).1.mp (hall j hj),
      fun j hmj _ => (heavy_reverse_comparison_iff hh hdom hmj hs0).mp (hall j (hm.trans hmj.le))⟩
  · rintro ⟨hl, hu⟩
    have hmR : m < phaseCutoff h m := lt_of_lt_of_le (Nat.lt_succ_self m) (phaseCutoff_ge_succ h m)
    have hRdom := heavy_domain_of_index (hm.trans hmR.le)
    have hT : s ≤ heavyCrossing h m (m + 1) := hu (m + 1) (by omega) (phaseCutoff_ge_succ h m)
    have hcut := phaseCutoff_ge_sample_entropy hh.le hT
    have hR : heavyValue h s (phaseCutoff h m) ≤ heavyValue h s m :=
      (heavy_reverse_comparison_iff hh hdom hmR hs0).mpr (hu _ hmR le_rfl)
    intro j hj
    rcases lt_trichotomy j m with hjm | rfl | hmj
    · exact (heavy_comparison_iff hh (heavy_domain_of_index hj) hjm hs0).1.mpr (hl j hj hjm)
    · exact le_rfl
    · by_cases hjR : j ≤ phaseCutoff h m
      · exact (heavy_reverse_comparison_iff hh hdom hmj hs0).mpr (hu j hmj hjR)
      · have hRj : (phaseCutoff h m : ℝ) < j := by exact_mod_cast Nat.lt_of_not_ge hjR
        exact ((strictAntiOn_heavyValue hh hs hRdom hcut)
          (show (phaseCutoff h m : ℝ) ∈ Ici (phaseCutoff h m : ℝ) from le_refl (phaseCutoff h m : ℝ))
          (show (j : ℝ) ∈ Ici (phaseCutoff h m : ℝ) from hRj.le) hRj).le.trans hR

def phaseLowerValues (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hm2 : 2 ≤ m) : Finset ℝ := by
  classical
  exact insert (lightCrossingInterval h m hh hm hm2).lower
    ((Finset.Ico (entropySupportIndex h) m).image (fun j => heavyCrossing h j m))

def phaseUpperValues (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hm2 : 2 ≤ m) : Finset (WithTop ℝ) := by
  classical
  exact insert (lightCrossingInterval h m hh hm hm2).upper
    ((Finset.Icc (m + 1) (phaseCutoff h m)).image (fun j => (heavyCrossing h m j : WithTop ℝ)))

theorem phaseLowerValues_nonempty (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hm2 : 2 ≤ m) : (phaseLowerValues h m hh hm hm2).Nonempty := by
  classical
  exact ⟨_, Finset.mem_insert_self _ _⟩

theorem phaseUpperValues_nonempty (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hm2 : 2 ≤ m) : (phaseUpperValues h m hh hm hm2).Nonempty := by
  classical
  exact ⟨_, Finset.mem_insert_self _ _⟩

def phaseLower (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) : ℝ :=
  (phaseLowerValues h m hh hm hm2).max' (phaseLowerValues_nonempty h m hh hm hm2)

def phaseUpper (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) : WithTop ℝ :=
  (phaseUpperValues h m hh hm hm2).min' (phaseUpperValues_nonempty h m hh hm hm2)

theorem phaseLower_le_iff {h s : ℝ} {m : ℕ} (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    phaseLower h m hh hm hm2 ≤ s ↔ (lightCrossingInterval h m hh hm hm2).lower ≤ s ∧
      ∀ j, entropySupportIndex h ≤ j → j < m → heavyCrossing h j m ≤ s := by
  classical
  simp only [phaseLower, Finset.max'_le_iff, phaseLowerValues, Finset.mem_insert,
    Finset.mem_image, Finset.mem_Ico]
  constructor
  · intro hh
    exact ⟨hh _ (Or.inl rfl), fun j hj hjm => hh _ (Or.inr ⟨j, ⟨hj, hjm⟩, rfl⟩)⟩
  · rintro ⟨hl, hh⟩ v (rfl | ⟨j, hj, rfl⟩)
    · exact hl
    · exact hh j hj.1 hj.2

theorem le_phaseUpper_iff {h s : ℝ} {m : ℕ} (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    (s : WithTop ℝ) ≤ phaseUpper h m hh hm hm2 ↔
      (s : WithTop ℝ) ≤ (lightCrossingInterval h m hh hm hm2).upper ∧
      ∀ j, m < j → j ≤ phaseCutoff h m → s ≤ heavyCrossing h m j := by
  classical
  simp only [phaseUpper, Finset.le_min'_iff, phaseUpperValues, Finset.mem_insert,
    Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro hh
    exact ⟨hh _ (Or.inl rfl), fun j hj hjR => WithTop.coe_le_coe.mp
      (hh _ (Or.inr ⟨j, ⟨by omega, hjR⟩, rfl⟩))⟩
  · rintro ⟨hu, hh⟩ v (rfl | ⟨j, hj, rfl⟩)
    · exact hu
    · exact WithTop.coe_le_coe.mpr (hh j (by omega) hj.2)

theorem phaseUpper_le_adjacent_crossing {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    phaseUpper h m hh hm hm2 ≤ (heavyCrossing h m (m + 1) : WithTop ℝ) := by
  classical
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨m + 1, Finset.mem_Icc.mpr ⟨le_rfl, phaseCutoff_ge_succ h m⟩, rfl⟩)

theorem phaseUpper_ne_top {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) : phaseUpper h m hh hm hm2 ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (phaseUpper_le_adjacent_crossing hh hm hm2)

/-- The manuscript's closed heavy winning interval. Both endpoint ties are retained. -/
theorem heavy_globalMax_iff_phase_interval {h : ℝ} {m t : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) (ht : 1 ≤ t) :
    ProbabilityVector.GlobalMaximizer t h (canonicalHeavy h hh m hm) ↔
      phaseLower h m hh hm hm2 ≤ t ∧ ((t : ℝ) : WithTop ℝ) ≤ phaseUpper h m hh hm hm2 := by
  have hs : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  rw [canonicalHeavy_globalMax_iff_comparisons hh hm ht,
    (lightCrossingInterval h m hh hm hm2).compare _ hs,
    heavy_all_comparisons_iff_finite hh hm (by exact_mod_cast ht),
    phaseLower_le_iff hh hm hm2, le_phaseUpper_iff hh hm hm2]
  tauto

theorem heavy_never_wins_of_reversed_endpoints {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (hrev : phaseUpper h m hh hm hm2 < (phaseLower h m hh hm hm2 : WithTop ℝ)) :
    ∀ t : ℕ, 1 ≤ t → ¬ ProbabilityVector.GlobalMaximizer t h (canonicalHeavy h hh m hm) := by
  intro t ht hw
  obtain ⟨hl, hu⟩ := (heavy_globalMax_iff_phase_interval hh hm hm2 ht).mp hw
  exact not_lt_of_ge ((WithTop.coe_le_coe.mpr hl).trans hu) hrev

theorem canonicalLight_globalMax_iff_finite_comparisons {h : ℝ} {t : ℕ}
    (hh : 0 < h) (ht : 1 ≤ t) :
    ProbabilityVector.GlobalMaximizer t h (canonicalLight h hh) ↔
      ∀ j, entropySupportIndex h ≤ j → j ≤ candidateCutoff t h →
        heavyValue h t j ≤ lightRealValue h t := by
  constructor
  · rintro ⟨_, hw⟩ j hj _
    have h := hw (canonicalHeavy h hh j hj) (canonicalHeavy_feasible hh j hj)
    rw [objective_canonicalHeavy, objective_canonicalLight] at h
    simpa only [heavyValue_integer_eq hh (heavy_domain_of_index hj), heavyCandidateValue,
      lightRealValue_nat] using h
  · intro hv
    refine ⟨canonicalLight_feasible hh, fun q hq => ?_⟩
    rw [objective_canonicalLight]
    apply (objective_le_optimalValue q t hq).trans
    rw [optimalValue_eq_finiteCandidateMaximum ht hh]
    apply (finiteCandidateMaximum_le_iff _ _ _).mpr
    exact ⟨le_rfl, fun j hj hcut => by simpa only [heavyValue_integer_eq hh (heavy_domain_of_index hj),
      heavyCandidateValue, lightRealValue_nat] using hv j hj hcut⟩

/-- The finite union of open intervals on which a nonduplicate heavy candidate beats the baseline. -/
def lightLosingIntervals (t : ℕ) (h : ℝ) (hh : 0 < h) : Set ℝ :=
  {s | ∃ (m : ℕ) (hm : entropySupportIndex h ≤ m) (_hM : m ≤ candidateCutoff t h) (hm2 : 2 ≤ m),
    (lightCrossingInterval h m hh hm hm2).lower < s ∧
      (s : WithTop ℝ) < (lightCrossingInterval h m hh hm hm2).upper}

/-- The light candidate wins exactly outside the finite union of open crossing intervals.
Open intervals exclude all endpoint ties, so every tied baseline maximum remains included. -/
theorem light_globalMax_iff_phase_intervals {h : ℝ} {t : ℕ}
    (hh : 0 < h) (ht : 1 ≤ t) :
    ProbabilityVector.GlobalMaximizer t h (canonicalLight h hh) ↔
      (t : ℝ) ∉ lightLosingIntervals t h hh := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  rw [canonicalLight_globalMax_iff_finite_comparisons hh ht]
  constructor
  · intro hv ⟨m, hm, hM, hm2, hwin⟩
    have hgt := (lightCrossingInterval h m hh hm hm2).strict_compare _ ht0 |>.mpr hwin
    exact not_lt_of_ge (hv m hm hM) hgt
  · intro hnot j hj hcut
    by_cases hj2 : 2 ≤ j
    · by_contra hlt
      have hgt : lightRealValue h t < heavyValue h t j := lt_of_not_ge hlt
      exact hnot ⟨j, hj, hcut, hj2, (lightCrossingInterval h j hh hj hj2).strict_compare _ ht0 |>.mp hgt⟩
    · have hj1 : j = 1 := by have := entropySupportIndex_pos hh.le; omega
      subst j
      simpa only [Nat.cast_one] using (binary_heavy_lightRealValue_eq hh hj t).le

end
end EntropyConstrainedMissingMass
