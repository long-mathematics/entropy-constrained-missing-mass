import EntropyConstrainedMissingMass.LightCrossingParameters
import EntropyConstrainedMissingMass.SmallSampleOptimality
import EntropyConstrainedMissingMass.CandidateShapes

/-! Real sample-size light-heavy crossing comparisons. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def lightRealValue (h s : ℝ) : ℝ :=
  lightRoot h * (1 - lightRoot h) ^ s + (1 - lightRoot h) * (1 - lightRepeated h) ^ s

theorem lightRealValue_nat (h : ℝ) (t : ℕ) : lightRealValue h t = lightValue t h := by
  simp only [lightRealValue, lightValue, branchObjective, lightRepeated, Real.rpow_natCast]

theorem analyticAt_lightRealValue {h : ℝ} (hh : 0 < h) (x : ℝ) :
    AnalyticAt ℝ (lightRealValue h) x := by
  obtain ⟨_, hay, _, hy1⟩ := light_parameters hh
  unfold lightRealValue
  simp_rw [Real.rpow_def_of_pos (sub_pos.mpr (hay.trans hy1)),
    Real.rpow_def_of_pos (sub_pos.mpr hy1)]
  fun_prop

theorem light_heavy_difference_entropy_series {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) :
    HasSum (fun n : ℕ => (heavyValue h (n + 1) m - lightRealValue h (n + 1)) / (n + 1)) 0 := by
  let p := canonicalHeavy h hh m hm
  let q := canonicalLight h hh
  have hp : p.entropy = ENNReal.ofReal h := by
    dsimp [p, canonicalHeavy]
    rw [entropy_natCandidateVector, (heavyRoot_spec hh (heavy_domain_of_index hm)).2]
  have hq : q.entropy = ENNReal.ofReal h := by
    dsimp [q, canonicalLight]
    rw [entropy_natCandidateVector, (lightRoot_spec hh).2]
  have hs := p.hasSum_objective_sub_div_zero q (hp ▸ ENNReal.ofReal_ne_top) (hp.trans hq.symm)
  convert hs using 1
  funext n
  dsimp [p, q]
  rw [objective_canonicalHeavy, objective_canonicalLight]
  simp only [heavyCandidateValue, ← heavyValue_integer_eq hh (heavy_domain_of_index hm),
    ← lightRealValue_nat, Nat.cast_add, Nat.cast_one]

theorem heavy_strict_below_light_smallSamples {h : ℝ} {m t : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (ht : t = 1 ∨ t = 2) : heavyValue h t m < lightRealValue h t := by
  let p := canonicalHeavy h hh m hm
  have hp : p ∈ ProbabilityVector.Feasible h := canonicalHeavy_feasible hh m hm
  have hle : p.objective t ≤ lightValue t h := by
    rw [← ProbabilityVector.optimalValue_eq_lightValue_smallSamples ht hh]
    exact objective_le_optimalValue p t hp
  have hne : p.objective t ≠ lightValue t h := by
    intro he
    have hmax : ∀ q : ProbabilityVector ℕ, q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t := by
      intro q hq
      rw [he, ← ProbabilityVector.optimalValue_eq_lightValue_smallSamples ht hh]
      exact objective_le_optimalValue q t hq
    have hl := (ProbabilityVector.globalMax_iff_lightCandidateForm_smallSamples p ht hh).mp ⟨hp, hmax⟩
    obtain ⟨_, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
    exact ProbabilityVector.not_lightCandidateForm_heavy hm2 ⟨hq.trans hqz, hz1⟩ hqz
      (candidateIndexEmbedding m) hl
  have hlt := lt_of_le_of_ne hle hne
  rw [objective_canonicalHeavy] at hlt
  simpa only [heavyCandidateValue, ← heavyValue_integer_eq hh (heavy_domain_of_index hm),
    ← lightRealValue_nat] using hlt

theorem light_heavy_difference_eq {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (s : ℝ) :
    heavyValue h s m - lightRealValue h s =
      heavyRoot h m * (1 - heavyRoot h m) ^ s -
      (1 - lightRoot h) * (1 - lightRepeated h) ^ s +
      (1 - heavyRoot h m) * (1 - heavyLight h m) ^ s - lightRoot h * (1 - lightRoot h) ^ s := by
  rw [heavyValue_eq hh (heavy_domain_of_index hm), lightRealValue]
  ring

theorem light_heavy_uniform_or_equal_representation {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (haq : lightRoot h = 0 ∨ heavyLight h m = lightRoot h) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℝ, heavyValue h s m - lightRealValue h s =
      heavyRoot h m * (1 - heavyRoot h m) ^ s - (1 - lightRoot h) * (1 - lightRepeated h) ^ s +
        D * (1 - heavyLight h m) ^ s := by
  obtain ⟨hm0, hq, _, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
  rcases haq with ha | hqa
  · refine ⟨1 - heavyRoot h m, sub_pos.mpr hz1, fun s => ?_⟩
    rw [light_heavy_difference_eq hh hm, ha]
    simp
  · refine ⟨1 - heavyRoot h m - lightRoot h, ?_, fun s => ?_⟩
    · have ha : 0 < lightRoot h := hqa ▸ hq
      have hnorm : (m : ℝ) * lightRoot h = 1 - heavyRoot h m := by
        rw [← hqa, heavyLight, mul_div_cancel₀ _ hm0.ne']
      have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith
    · rw [light_heavy_difference_eq hh hm, hqa]
      ring

theorem light_heavy_single_zero_bound {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (haq : lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h) :
    ZeroMultiplicityBound (fun s => heavyValue h s m - lightRealValue h s) 2 := by
  obtain ⟨_, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
  obtain ⟨ha, hay, _, hy1⟩ := light_parameters hh
  obtain ⟨hqy, hyz⟩ := light_heavy_mass_order hh hm hm2
  have hne : heavyValue h 2 m - lightRealValue h 2 ≠ 0 :=
    (sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inr rfl))).ne
  by_cases he : lightRoot h = 0 ∨ heavyLight h m = lightRoot h
  · obtain ⟨D, hD, heq⟩ := light_heavy_uniform_or_equal_representation hh hm hm2 he
    have hz := three_term_zeros_rpow (heavyRoot h m) (-(1 - lightRoot h)) D
      (1 - heavyRoot h m) (1 - lightRepeated h) (1 - heavyLight h m)
      (sub_pos.mpr hz1) (by linarith) (by linarith)
      ⟨2, by simpa only [neg_mul, sub_eq_add_neg] using (heq 2 ▸ hne)⟩
    simpa only [heq, sub_eq_add_neg, neg_mul] using hz
  · have ha' : 0 < lightRoot h := lt_of_le_of_ne ha (Ne.symm (fun hz => he (Or.inl hz)))
    have hqa : heavyLight h m < lightRoot h :=
      lt_of_le_of_ne (haq.resolve_left (fun hz => he (Or.inl hz))) (fun hz => he (Or.inr hz))
    have hz := four_term_zeros (heavyRoot h m) (1 - lightRoot h) (lightRoot h) (1 - heavyRoot h m)
      (1 - heavyRoot h m) (1 - lightRepeated h) (1 - lightRoot h) (1 - heavyLight h m)
      (hq.trans hqz) (sub_pos.mpr (hay.trans hy1)) ha' (sub_pos.mpr hz1)
      (sub_pos.mpr hz1) (by linarith) (by linarith) (by linarith)
    convert hz using 1
    funext s
    rw [light_heavy_difference_eq hh hm]
    ring

theorem light_heavy_single_eventually_pos {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (haq : lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h) :
    ∀ᶠ s : ℝ in atTop, 0 < heavyValue h s m - lightRealValue h s := by
  obtain ⟨_, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
  obtain ⟨ha, hay, _, hy1⟩ := light_parameters hh
  obtain ⟨hqy, hyz⟩ := light_heavy_mass_order hh hm hm2
  by_cases he : lightRoot h = 0 ∨ heavyLight h m = lightRoot h
  · obtain ⟨D, hD, heq⟩ := light_heavy_uniform_or_equal_representation hh hm hm2 he
    have hp := eventually_pos_four_term (heavyRoot h m) (1 - lightRoot h) 0 D
      (1 - heavyRoot h m) (1 - lightRepeated h) (1 - lightRepeated h) (1 - heavyLight h m)
      hD (sub_pos.mpr hz1) (sub_pos.mpr hy1) (sub_pos.mpr hy1)
      (by linarith) (by linarith) (by linarith)
    simpa only [zero_mul, sub_zero, ← heq] using hp
  · have hqa : heavyLight h m < lightRoot h :=
      lt_of_le_of_ne (haq.resolve_left (fun hz => he (Or.inl hz))) (fun hz => he (Or.inr hz))
    have hp := eventually_pos_four_term (heavyRoot h m) (1 - lightRoot h) (lightRoot h) (1 - heavyRoot h m)
      (1 - heavyRoot h m) (1 - lightRepeated h) (1 - lightRoot h) (1 - heavyLight h m)
      (sub_pos.mpr hz1) (sub_pos.mpr hz1) (sub_pos.mpr hy1) (sub_pos.mpr (hay.trans hy1))
      (by linarith) (by linarith) (by linarith)
    filter_upwards [hp] with s hs
    rw [light_heavy_difference_eq hh hm]
    linarith

theorem light_heavy_double_zero_bound {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (haq : lightRoot h < heavyLight h m) :
    ZeroMultiplicityBound (fun s => heavyValue h s m - lightRealValue h s) 3 := by
  obtain ⟨_, hq, _, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
  obtain ⟨hqy, hyz⟩ := light_heavy_mass_order hh hm hm2
  have hne : heavyValue h 2 m - lightRealValue h 2 ≠ 0 :=
    (sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inr rfl))).ne
  have he (s : ℝ) : heavyValue h s m - lightRealValue h s =
      heavyRoot h m * (1 - heavyRoot h m) ^ s +
      (-(1 - lightRoot h)) * (1 - lightRepeated h) ^ s +
      (1 - heavyRoot h m) * (1 - heavyLight h m) ^ s + (-lightRoot h) * (1 - lightRoot h) ^ s := by
    rw [light_heavy_difference_eq hh hm]
    ring
  have hz := four_term_zeros_rpow (heavyRoot h m) (-(1 - lightRoot h)) (1 - heavyRoot h m) (-lightRoot h)
    (1 - heavyRoot h m) (1 - lightRepeated h) (1 - heavyLight h m) (1 - lightRoot h)
    (sub_pos.mpr hz1) (by linarith) (by linarith) (by linarith) ⟨2, he 2 ▸ hne⟩
  simpa only [he] using hz

theorem light_heavy_double_eventually_neg {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (ha : 0 < lightRoot h) (haq : lightRoot h < heavyLight h m) :
    ∀ᶠ s : ℝ in atTop, heavyValue h s m - lightRealValue h s < 0 := by
  obtain ⟨_, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh (heavy_domain_of_index hm)
  obtain ⟨_, _, _, hy1⟩ := light_parameters hh
  obtain ⟨hqy, hyz⟩ := light_heavy_mass_order hh hm hm2
  have hp := eventually_pos_four_term (-heavyRoot h m) (-(1 - lightRoot h)) (1 - heavyRoot h m) (lightRoot h)
    (1 - heavyRoot h m) (1 - lightRepeated h) (1 - heavyLight h m) (1 - lightRoot h)
    ha (sub_pos.mpr hz1) (sub_pos.mpr hy1) (sub_pos.mpr (hqz.trans hz1))
    (by linarith) (by linarith) (by linarith)
  filter_upwards [hp] with s hs
  rw [light_heavy_difference_eq hh hm]
  linarith

/-- The uniform light case and `q≤a` have a single simple positive crossing after two. -/
theorem light_heavy_single_crossing {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (haq : lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h) :
    ∃ α : ℝ, 2 < α ∧
      (∀ s : ℝ, heavyValue h s m = lightRealValue h s ↔ s = 0 ∨ s = α) ∧
      analyticOrderAt (fun s => heavyValue h s m - lightRealValue h s) 0 = 1 ∧
      analyticOrderAt (fun s => heavyValue h s m - lightRealValue h s) α = 1 ∧
      (∀ s ∈ Ioo 0 α, heavyValue h s m < lightRealValue h s) ∧
      (∀ s ∈ Ioi α, lightRealValue h s < heavyValue h s m) := by
  have h0 : heavyValue h 0 m - lightRealValue h 0 = 0 := by
    rw [heavyValue_eq hh (heavy_domain_of_index hm), lightRealValue]
    simp only [Real.rpow_zero, mul_one]
    ring
  obtain ⟨α, hα, hz, hs0, hsα, hn, hp⟩ := single_crossing_of_two_zeros
    (f := fun s => heavyValue h s m - lightRealValue h s)
    (fun s => (analyticAt_heavyValue hh (heavy_domain_of_index hm) s).sub (analyticAt_lightRealValue hh s))
    (light_heavy_single_zero_bound hh hm hm2 haq) h0 (by norm_num : (0 : ℝ) < 2)
    (sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inr rfl)))
    (light_heavy_single_eventually_pos hh hm hm2 haq)
  exact ⟨α, hα, by simpa only [sub_eq_zero] using hz, hs0, hsα,
    fun s hs => sub_neg.mp (hn s hs), fun s hs => sub_pos.mp (hp s hs)⟩

/-- If `0<a<q`, there are exactly two simple positive crossings after two,
and the heavy branch is better exactly between them. -/
theorem light_heavy_double_crossing {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m)
    (ha : 0 < lightRoot h) (haq : lightRoot h < heavyLight h m) :
    ∃ α β : ℝ, 2 < α ∧ α < β ∧
      (∀ s : ℝ, heavyValue h s m = lightRealValue h s ↔ s = 0 ∨ s = α ∨ s = β) ∧
      analyticOrderAt (fun s => heavyValue h s m - lightRealValue h s) 0 = 1 ∧
      analyticOrderAt (fun s => heavyValue h s m - lightRealValue h s) α = 1 ∧
      analyticOrderAt (fun s => heavyValue h s m - lightRealValue h s) β = 1 ∧
      (∀ s ∈ Ioo 0 α, heavyValue h s m < lightRealValue h s) ∧
      (∀ s ∈ Ioo α β, lightRealValue h s < heavyValue h s m) ∧
      (∀ s ∈ Ioi β, heavyValue h s m < lightRealValue h s) := by
  let f : ℝ → ℝ := fun s => heavyValue h s m - lightRealValue h s
  have hn := light_heavy_double_eventually_neg hh hm hm2 ha haq
  have hs : HasSum (fun n : ℕ => (-f) (n + 1) / (n + 1)) 0 := by
    simpa only [Pi.neg_apply, neg_div, neg_zero] using (light_heavy_difference_entropy_series hh hm).neg
  obtain ⟨n, hnpos⟩ := exists_negative_integer_of_zero_series (f := -f) hs (by
    simpa only [Pi.neg_apply, neg_pos] using hn)
  have hfn : 0 < f (n + 1) := by simpa using hnpos
  have hn2 : (2 : ℝ) < n + 1 := by
    have h1 : f 1 < 0 := by
      simpa only [f, Nat.cast_one] using
        sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inl rfl))
    have h2 : f 2 < 0 := by
      simpa only [f, Nat.cast_ofNat] using
        sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inr rfl))
    have hn0 : n ≠ 0 := by intro he; subst n; norm_num at hfn; linarith
    have hn1 : n ≠ 1 := by intro he; subst n; norm_num at hfn; linarith
    have hn2 : 2 ≤ n := by omega
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have h0 : f 0 = 0 := by
    dsimp [f]
    rw [heavyValue_eq hh (heavy_domain_of_index hm), lightRealValue]
    simp only [Real.rpow_zero, mul_one]
    ring
  obtain ⟨α, β, haα, hαn, hnβ, hz, hs0, hsα, hsβ, hleft, hmid, hright⟩ :=
    double_crossing_of_three_zeros (f := f)
      (fun s => (analyticAt_heavyValue hh (heavy_domain_of_index hm) s).sub (analyticAt_lightRealValue hh s))
      (light_heavy_double_zero_bound hh hm hm2 haq) h0 (by norm_num : (0 : ℝ) < 2) hn2
      (sub_neg.mpr (heavy_strict_below_light_smallSamples hh hm hm2 (Or.inr rfl))) hfn hn
  exact ⟨α, β, haα, hαn.trans hnβ, by simpa only [f, sub_eq_zero] using hz, hs0, hsα, hsβ,
    fun s hs => sub_neg.mp (hleft s hs), fun s hs => sub_pos.mp (hmid s hs),
    fun s hs => sub_neg.mp (hright s hs)⟩

/-- The omitted heavy binary candidate is exactly the light candidate, for every real exponent. -/
theorem binary_heavy_lightRealValue_eq {h : ℝ} (hh : 0 < h)
    (hk : entropySupportIndex h ≤ 1) (s : ℝ) : heavyValue h s 1 = lightRealValue h s := by
  have hk1 : entropySupportIndex h = 1 := by have := entropySupportIndex_pos hh.le; omega
  have hh2 : h < Real.log 2 := by
    convert (entropySupportIndex_log_bounds hh.le).2 using 1
    norm_num [hk1]
  have hdom := heavy_domain_of_index hk
  have hz := (binary_entropy_root_duplicate hh hh2 (lightRoot_spec hh).1 (lightRoot_spec hh).2
    (by simpa using (heavyRoot_spec hh hdom).1) (by simpa using (heavyRoot_spec hh hdom).2)).2
  rw [heavyValue_eq hh (by simpa using hdom)]
  simp only [lightRealValue, lightRepeated, heavyLight, hk1, Nat.cast_one, div_one, hz,
    sub_sub_cancel]
  ring

/-- Beyond the binary duplicate, the light-heavy difference always starts with a negative slope. -/
theorem light_heavy_deriv_zero_neg {h : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    deriv (fun s => heavyValue h s m - lightRealValue h s) 0 < 0 := by
  have hf := (analyticAt_heavyValue hh (heavy_domain_of_index hm) 0).sub (analyticAt_lightRealValue hh 0)
  by_cases he : lightRoot h = 0 ∨ heavyLight h m ≤ lightRoot h
  · obtain ⟨α, ha, _, hs0, _, hn, _⟩ := light_heavy_single_crossing hh hm hm2 he
    exact deriv_neg_of_simple_zero_negative_right hf hs0 (by linarith)
      (fun s hs => sub_neg.mpr (hn s hs))
  · have ha : 0 < lightRoot h := lt_of_le_of_ne (light_parameters hh).1
      (Ne.symm (fun hz => he (Or.inl hz)))
    have haq : lightRoot h < heavyLight h m := lt_of_not_ge (fun hqa => he (Or.inr hqa))
    obtain ⟨α, β, haα, _, _, hs0, _, _, hn, _, _⟩ := light_heavy_double_crossing hh hm hm2 ha haq
    exact deriv_neg_of_simple_zero_negative_right hf hs0 (by linarith)
      (fun s hs => sub_neg.mpr (hn s hs))

end
end EntropyConstrainedMissingMass
