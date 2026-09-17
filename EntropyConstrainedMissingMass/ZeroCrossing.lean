import EntropyConstrainedMissingMass.ExponentialZeros
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Crossing consequences of the analytic multiplicity bound. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology

theorem ZeroMultiplicityBound.sum_le {f : ℝ → ℝ} {n : ℕ}
    (hb : ZeroMultiplicityBound f n) (s : Finset ℝ) (hs : ∀ x ∈ s, f x = 0) :
    (∑ x ∈ s, analyticOrderAt f x) ≤ (n : ℕ∞) := by
  obtain ⟨t, ht, hn⟩ := hb
  exact (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (ht x).mp (hs x hx))
    (fun _ _ _ => zero_le)).trans hn

theorem ZeroMultiplicityBound.card_le {f : ℝ → ℝ} {n : ℕ}
    (hb : ZeroMultiplicityBound f n) (hf : ∀ x, AnalyticAt ℝ f x)
    (s : Finset ℝ) (hs : ∀ x ∈ s, f x = 0) : s.card ≤ n := by
  have h := hb.sum_le s hs
  have h1 : (s.card : ℕ∞) ≤ ∑ x ∈ s, analyticOrderAt f x := by
    simpa using Finset.sum_le_sum (fun x hx =>
      Order.one_le_iff_ne_zero.mpr ((hf x).analyticOrderAt_ne_zero.mpr (hs x hx)))
  exact_mod_cast h1.trans h

/-- If distinct zeros already exhaust a multiplicity bound, there are no other zeros
and every listed zero is simple. -/
theorem ZeroMultiplicityBound.exhausted {f : ℝ → ℝ} {n : ℕ}
    (hb : ZeroMultiplicityBound f n) (hf : ∀ x, AnalyticAt ℝ f x)
    (s : Finset ℝ) (hcard : s.card = n) (hs : ∀ x ∈ s, f x = 0) :
    (∀ x, f x = 0 ↔ x ∈ s) ∧ ∀ x ∈ s, analyticOrderAt f x = 1 := by
  classical
  have h1 (x : ℝ) (hx : x ∈ s) : (1 : ℕ∞) ≤ analyticOrderAt f x :=
    Order.one_le_iff_ne_zero.mpr ((hf x).analyticOrderAt_ne_zero.mpr (hs x hx))
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨fun hx => ?_, hs x⟩
    by_contra hxs
    have hh := hb.card_le hf (insert x s) (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs y hy)
    rw [Finset.card_insert_of_notMem hxs, hcard] at hh
    omega
  · intro x hx
    have he : ((s.erase x).card : ℕ∞) ≤ ∑ y ∈ s.erase x, analyticOrderAt f y := by
      simpa using Finset.sum_le_sum (fun y hy => h1 y (Finset.mem_erase.mp hy).2)
    have hsum : analyticOrderAt f x + (∑ y ∈ s.erase x, analyticOrderAt f y) ≤ (n : ℕ∞) := by
      rw [Finset.add_sum_erase _ _ hx]
      exact hb.sum_le s hs
    have hcard' : (n : ℕ∞) = 1 + (s.erase x).card := by
      rw [← hcard, ← Finset.card_erase_add_one hx, Nat.cast_add, Nat.cast_one, add_comm]
    rw [hcard'] at hsum
    have hu : analyticOrderAt f x ≤ 1 :=
      (WithTop.add_le_add_iff_right (ENat.natCast_ne_top _)).mp
        ((add_le_add le_rfl he).trans hsum)
    exact le_antisymm hu (h1 x hx)

/-- Two distinct zeros exhaust a bound of two, and both zeros are simple. -/
theorem ZeroMultiplicityBound.two_zeros {f : ℝ → ℝ}
    (hb : ZeroMultiplicityBound f 2) (hf : ∀ x, AnalyticAt ℝ f x)
    {a b : ℝ} (hab : a ≠ b) (ha : f a = 0) (hb' : f b = 0) :
    (∀ x, f x = 0 ↔ x = a ∨ x = b) ∧
      analyticOrderAt f a = 1 ∧ analyticOrderAt f b = 1 := by
  classical
  have hz : ∀ x, f x = 0 ↔ x = a ∨ x = b := by
    intro x
    constructor
    · intro hx
      by_contra hh
      have hxa : x ≠ a := fun he => hh (Or.inl he)
      have hxb : x ≠ b := fun he => hh (Or.inr he)
      have hcard := hb.card_le hf {a, b, x} (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl <;> assumption)
      simp [hab, Ne.symm hxa, Ne.symm hxb] at hcard
    · rintro (rfl | rfl) <;> assumption
  have ha1 : (1 : ℕ∞) ≤ analyticOrderAt f a :=
    Order.one_le_iff_ne_zero.mpr ((hf a).analyticOrderAt_ne_zero.mpr ha)
  have hb1 : (1 : ℕ∞) ≤ analyticOrderAt f b :=
    Order.one_le_iff_ne_zero.mpr ((hf b).analyticOrderAt_ne_zero.mpr hb')
  have hsum : analyticOrderAt f a + analyticOrderAt f b ≤ (2 : ℕ∞) := by
    simpa [Finset.sum_pair hab] using hb.sum_le {a, b} (by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
  have hleft : analyticOrderAt f a ≤ 1 :=
    (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      ((add_le_add le_rfl hb1).trans hsum)
  have hright : analyticOrderAt f b ≤ 1 :=
    (WithTop.add_le_add_iff_left (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      ((add_le_add ha1 le_rfl).trans hsum)
  exact ⟨hz, le_antisymm hleft ha1, le_antisymm hright hb1⟩

theorem deriv_ne_zero_of_analyticOrderAt_eq_one {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = 1) : deriv f a ≠ 0 := by
  have hh := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf (n := 1)).mp ho
  simpa using hh.2

theorem negative_on_interval_of_no_zeros {f : ℝ → ℝ} {I : Set ℝ}
    (hc : Continuous f) (hI : OrdConnected I) (hn : ∀ x ∈ I, f x ≠ 0)
    {a : ℝ} (ha : a ∈ I) (hfa : f a < 0) : ∀ x ∈ I, f x < 0 := by
  intro x hx
  by_contra hfx
  have hfx' : 0 ≤ f x := le_of_not_gt hfx
  rcases le_total a x with hax | hxa
  · obtain ⟨z, hz, he⟩ := intermediate_value_Icc hax hc.continuousOn ⟨hfa.le, hfx'⟩
    exact hn z (hI.out ha hx hz) he
  · obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hxa hc.continuousOn ⟨hfa.le, hfx'⟩
    exact hn z (hI.out hx ha hz) he

/-- A two-zero bound, a zero at zero, a negative positive-time value, and eventual
positivity force exactly one positive simple crossing with the asserted sign orientation. -/
theorem single_crossing_of_two_zeros {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (hb : ZeroMultiplicityBound f 2)
    (h0 : f 0 = 0) (ha : 0 < a) (hfa : f a < 0)
    (hpos : ∀ᶠ x in atTop, 0 < f x) :
    ∃ τ : ℝ, a < τ ∧ (∀ x, f x = 0 ↔ x = 0 ∨ x = τ) ∧
      analyticOrderAt f 0 = 1 ∧ analyticOrderAt f τ = 1 ∧
      (∀ x ∈ Ioo 0 τ, f x < 0) ∧ (∀ x ∈ Ioi τ, 0 < f x) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hpos
  let b := max R (a + 1)
  have hab : a < b := by dsimp [b]; linarith [le_max_right R (a + 1)]
  have hfb : 0 < f b := hR b (le_max_left _ _)
  obtain ⟨τ, hτ, hzero⟩ := intermediate_value_Icc hab.le hc.continuousOn ⟨hfa.le, hfb.le⟩
  have haτ : a < τ := lt_of_le_of_ne hτ.1 (by intro he; rw [← he] at hzero; linarith)
  have hτb : τ < b := lt_of_le_of_ne hτ.2 (by intro he; rw [he] at hzero; linarith)
  have hτ0 : 0 < τ := ha.trans haτ
  obtain ⟨hz, hsimple0, hsimpleτ⟩ := hb.two_zeros hf hτ0.ne h0 hzero
  refine ⟨τ, haτ, hz, hsimple0, hsimpleτ, ?_, ?_⟩
  · apply negative_on_interval_of_no_zeros hc ordConnected_Ioo
      (fun x hx hh => ?_) ⟨ha, haτ⟩ hfa
    rcases (hz x).mp hh with he | he <;> subst x <;> simp_all
  · have hn : ∀ x ∈ Ioi τ, (-f) x ≠ 0 := by
      intro x hx hh
      have he : f x = 0 := neg_eq_zero.mp hh
      rcases (hz x).mp he with he | he
      · subst x
        exact not_lt_of_ge hτ0.le hx
      · subst x
        exact lt_irrefl τ hx
    have hn' := negative_on_interval_of_no_zeros hc.neg ordConnected_Ioi hn hτb
      (show (-f) b < 0 by simpa using neg_neg_of_pos hfb)
    intro x hx
    simpa using hn' x hx

/-- A simple zero with negative values immediately to its right has negative derivative. -/
theorem deriv_neg_of_simple_zero_negative_right {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticAt ℝ f a) (ho : analyticOrderAt f a = 1) (hab : a < b)
    (hn : ∀ x ∈ Ioo a b, f x < 0) : deriv f a < 0 := by
  have hz : f a = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [ho]; norm_num)
  have hd : HasDerivAt f (deriv f a) a := hf.differentiableAt.hasDerivAt
  have hle : deriv f a ≤ 0 := by
    apply le_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
    filter_upwards [(eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with x hxb hax
    rw [slope_def_field, hz, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hn x ⟨hax, hxb⟩).le (sub_nonneg.mpr hax.le)
  exact lt_of_le_of_ne hle (deriv_ne_zero_of_analyticOrderAt_eq_one hf ho)

/-- Three permitted zeros, a negative value followed by a positive value, and a
negative tail force two simple positive crossings and the complete sign pattern. -/
theorem double_crossing_of_three_zeros {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (hb : ZeroMultiplicityBound f 3)
    (h0 : f 0 = 0) (ha : 0 < a) (hab : a < b) (hfa : f a < 0) (hfb : 0 < f b)
    (hneg : ∀ᶠ x in atTop, f x < 0) :
    ∃ α β : ℝ, a < α ∧ α < b ∧ b < β ∧
      (∀ x, f x = 0 ↔ x = 0 ∨ x = α ∨ x = β) ∧
      analyticOrderAt f 0 = 1 ∧ analyticOrderAt f α = 1 ∧ analyticOrderAt f β = 1 ∧
      (∀ x ∈ Ioo 0 α, f x < 0) ∧ (∀ x ∈ Ioo α β, 0 < f x) ∧
      (∀ x ∈ Ioi β, f x < 0) := by
  classical
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  obtain ⟨R, hR⟩ := eventually_atTop.mp hneg
  let c := max R (b + 1)
  have hbc : b < c := by dsimp [c]; linarith [le_max_right R (b + 1)]
  have hfc : f c < 0 := hR c (le_max_left _ _)
  obtain ⟨α, hα, hzα⟩ := intermediate_value_Icc hab.le hc.continuousOn ⟨hfa.le, hfb.le⟩
  obtain ⟨β, hβ, hzβ⟩ := intermediate_value_Icc' hbc.le hc.continuousOn ⟨hfc.le, hfb.le⟩
  have haα : a < α := lt_of_le_of_ne hα.1 (by intro he; rw [← he] at hzα; linarith)
  have hαb : α < b := lt_of_le_of_ne hα.2 (by intro he; rw [he] at hzα; linarith)
  have hbβ : b < β := lt_of_le_of_ne hβ.1 (by intro he; rw [← he] at hzβ; linarith)
  have hβc : β < c := lt_of_le_of_ne hβ.2 (by intro he; rw [he] at hzβ; linarith)
  have h0α : 0 < α := ha.trans haα
  have hαβ : α < β := hαb.trans hbβ
  have h0β : 0 < β := h0α.trans hαβ
  obtain ⟨hz, hs⟩ := hb.exhausted hf {0, α, β} (by simp [h0α.ne, h0β.ne, hαβ.ne])
    (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hs
  refine ⟨α, β, haα, hαb, hbβ, hz, hs 0 (Or.inl rfl), hs α (Or.inr (Or.inl rfl)),
    hs β (Or.inr (Or.inr rfl)), ?_, ?_, ?_⟩
  · apply negative_on_interval_of_no_zeros hc ordConnected_Ioo
      (fun x hx hh => ?_) ⟨ha, haα⟩ hfa
    rcases (hz x).mp hh with he | he | he <;> subst x <;> rcases hx with ⟨hx1, hx2⟩ <;> linarith
  · have hn : ∀ x ∈ Ioo α β, (-f) x ≠ 0 := by
      intro x hx hh
      have he : f x = 0 := neg_eq_zero.mp hh
      rcases (hz x).mp he with he | he | he <;> subst x <;> rcases hx with ⟨hx1, hx2⟩ <;> linarith
    have hh := negative_on_interval_of_no_zeros hc.neg ordConnected_Ioo hn ⟨hαb, hbβ⟩
      (show (-f) b < 0 by simpa using neg_neg_of_pos hfb)
    intro x hx
    simpa using hh x hx
  · apply negative_on_interval_of_no_zeros hc ordConnected_Ioi
      (fun x hx hh => ?_) hβc hfc
    rcases (hz x).mp hh with he | he | he <;> subst x <;> change β < _ at hx <;> linarith

end
end EntropyConstrainedMissingMass
