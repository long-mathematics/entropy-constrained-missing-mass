import EntropyConstrainedMissingMass.LightCrossing

/-! Canonical crossing endpoints and their closed/strict comparison rules. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set

def heavyCrossing (h : ℝ) (i j : ℕ) : ℝ := by
  classical
  exact if hv : 0 < h ∧ Real.exp h - 1 < i ∧ i < j then
    (heavy_heavy_single_crossing hv.1 hv.2.1 hv.2.2).choose else 0

theorem heavyCrossing_spec {h : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) :
    1 < heavyCrossing h i j ∧
      (∀ s : ℝ, heavyValue h s j = heavyValue h s i ↔ s = 0 ∨ s = heavyCrossing h i j) ∧
      analyticOrderAt (fun s => heavyValue h s j - heavyValue h s i) 0 = 1 ∧
      analyticOrderAt (fun s => heavyValue h s j - heavyValue h s i) (heavyCrossing h i j) = 1 ∧
      (∀ s ∈ Ioo 0 (heavyCrossing h i j), heavyValue h s j < heavyValue h s i) ∧
      (∀ s ∈ Ioi (heavyCrossing h i j), heavyValue h s i < heavyValue h s j) := by
  simp only [heavyCrossing, dite_eq_left (show 0 < h ∧ Real.exp h - 1 < (i : ℝ) ∧ i < j from ⟨hh, hi, hij⟩)]
  exact (heavy_heavy_single_crossing hh hi hij).choose_spec

theorem heavy_comparison_iff {h s : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) (hs : 0 < s) :
    (heavyValue h s i ≤ heavyValue h s j ↔ heavyCrossing h i j ≤ s) ∧
      (heavyValue h s i < heavyValue h s j ↔ heavyCrossing h i j < s) := by
  obtain ⟨_, hz, _, _, hn, hp⟩ := heavyCrossing_spec hh hi hij
  rcases lt_trichotomy s (heavyCrossing h i j) with hlt | rfl | hgt
  · have hv := hn s ⟨hs, hlt⟩
    simp [not_le.mpr hv, not_lt.mpr hv.le, not_le.mpr hlt, not_lt.mpr hlt.le]
  · have he := (hz _).mpr (Or.inr rfl)
    simp [he]
  · have hv := hp s hgt
    simp [hv.le, hv, hgt.le, hgt]

theorem heavy_reverse_comparison_iff {h s : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) (hs : 0 < s) :
    heavyValue h s j ≤ heavyValue h s i ↔ s ≤ heavyCrossing h i j := by
  have hc := (heavy_comparison_iff hh hi hij hs).2
  exact not_lt.symm.trans (hc.not.trans not_lt)

theorem heavy_comparison_persists {h s₁ s₂ : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) (hs₁ : 0 < s₁) (hs : s₁ < s₂)
    (hwin : heavyValue h s₁ i ≤ heavyValue h s₁ j) : heavyValue h s₂ i < heavyValue h s₂ j :=
  (heavy_comparison_iff hh hi hij (hs₁.trans hs)).2.mpr
    (((heavy_comparison_iff hh hi hij hs₁).1.mp hwin).trans_lt hs)

private theorem signs_to_interval_comparison {f : ℝ → ℝ} {α β : ℝ}
    (hαβ : α < β) (hzα : f α = 0) (hzβ : f β = 0)
    (hl : ∀ s ∈ Ioo 0 α, f s < 0) (hm : ∀ s ∈ Ioo α β, 0 < f s)
    (hr : ∀ s ∈ Ioi β, f s < 0) {s : ℝ} (hs : 0 < s) :
    (0 ≤ f s ↔ α ≤ s ∧ s ≤ β) ∧ (0 < f s ↔ α < s ∧ s < β) := by
  rcases lt_trichotomy s α with hsa | rfl | has
  · have hfs := hl s ⟨hs, hsa⟩
    simp [not_le.mpr hfs, not_lt.mpr hfs.le, not_le.mpr hsa, not_lt.mpr hsa.le]
  · simp [hzα, hαβ.le, hαβ]
  · rcases lt_trichotomy s β with hsb | rfl | hbs
    · have hfs := hm s ⟨has, hsb⟩
      simp [hfs, hfs.le, has, has.le, hsb, hsb.le]
    · simp [hzβ, hαβ.le, hαβ]
    · have hfs := hr s hbs
      simp [not_le.mpr hfs, not_lt.mpr hfs.le, not_le.mpr hbs, not_lt.mpr hbs.le]

structure LightCrossingInterval (h : ℝ) (m : ℕ) where
  lower : ℝ
  upper : WithTop ℝ
  lower_gt_two : 2 < lower
  lower_lt_upper : (lower : WithTop ℝ) < upper
  compare : ∀ s : ℝ, 0 < s →
    (lightRealValue h s ≤ heavyValue h s m ↔ lower ≤ s ∧ (s : WithTop ℝ) ≤ upper)
  strict_compare : ∀ s : ℝ, 0 < s →
    (lightRealValue h s < heavyValue h s m ↔ lower < s ∧ (s : WithTop ℝ) < upper)
  upper_eq_top_iff : upper = ⊤ ↔ lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h

theorem exists_lightCrossingInterval {h : ℝ} {m : ℕ} (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) : Nonempty (LightCrossingInterval h m) := by
  by_cases he : lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h
  · obtain ⟨α, hα, hz, _, _, hn, hp⟩ := light_heavy_single_crossing hh hm hm2 he
    have hw {s : ℝ} (hs : 0 < s) :
        (lightRealValue h s ≤ heavyValue h s m ↔ α ≤ s) ∧
        (lightRealValue h s < heavyValue h s m ↔ α < s) := by
      rcases lt_trichotomy s α with hlt | rfl | hgt
      · have hv := hn s ⟨hs, hlt⟩
        simp [not_le.mpr hv, not_lt.mpr hv.le, not_le.mpr hlt, not_lt.mpr hlt.le]
      · have hv := (hz _).mpr (Or.inr rfl)
        simp [hv]
      · have hv := hp s hgt
        simp [hv, hv.le, hgt, hgt.le]
    exact ⟨⟨α, ⊤, hα, WithTop.coe_lt_top α, fun s hs => by simpa using (hw hs).1,
      fun s hs => by simpa using (hw hs).2, by simp [he]⟩⟩
  · have ha : 0 < lightRoot h := lt_of_le_of_ne (light_parameters hh).1
      (Ne.symm (fun hz => he (Or.inl hz)))
    have haq : lightRoot h < heavyLight h m := lt_of_not_ge (fun hqa => he (Or.inr hqa))
    obtain ⟨α, β, hα, hαβ, hz, _, _, _, hn, hp, hr⟩ := light_heavy_double_crossing hh hm hm2 ha haq
    have hw {s : ℝ} (hs : 0 < s) := signs_to_interval_comparison
      (f := fun s => heavyValue h s m - lightRealValue h s) hαβ
      (sub_eq_zero.mpr ((hz α).mpr (Or.inr (Or.inl rfl))))
      (sub_eq_zero.mpr ((hz β).mpr (Or.inr (Or.inr rfl))))
      (fun s hs => sub_neg.mpr (hn s hs)) (fun s hs => sub_pos.mpr (hp s hs))
      (fun s hs => sub_neg.mpr (hr s hs)) hs
    exact ⟨⟨α, β, hα, WithTop.coe_lt_coe.mpr hαβ,
      fun s hs => by simpa only [sub_nonneg, WithTop.coe_le_coe] using (hw hs).1,
      fun s hs => by simpa only [sub_pos, WithTop.coe_lt_coe] using (hw hs).2,
      by simp [he]⟩⟩

def lightCrossingInterval (h : ℝ) (m : ℕ) (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (hm2 : 2 ≤ m) : LightCrossingInterval h m := (exists_lightCrossingInterval hh hm hm2).some

end
end EntropyConstrainedMissingMass
