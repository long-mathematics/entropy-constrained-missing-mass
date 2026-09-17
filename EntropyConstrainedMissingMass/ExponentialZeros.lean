import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Finset.Max

/-! Real zero counts with analytic multiplicity, including the multiplicity form of Rolle. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set

/-- A finite real zero set whose total analytic multiplicity is at most `n`.
Using `ℕ∞` prevents a locally zero function from receiving a spurious finite count. -/
def ZeroMultiplicityBound (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ s : Finset ℝ, (∀ x, f x = 0 ↔ x ∈ s) ∧
    (∑ x ∈ s, analyticOrderAt f x) ≤ (n : ℕ∞)

theorem finite_zeros_of_finite_deriv_zeros {f : ℝ → ℝ} (hf : Continuous f)
    {t : Finset ℝ} (ht : ∀ x, deriv f x = 0 → x ∈ t) : {x | f x = 0}.Finite := by
  classical
  by_contra h
  obtain ⟨s, hs, hc⟩ := Set.Infinite.exists_subset_card_eq h (t.card + 2)
  have hcard : s.card ≤ t.card + 1 := by
    apply Finset.card_le_of_interleaved
    intro x hx y hy hxy _
    obtain ⟨z, hz, hdz⟩ := exists_deriv_eq_zero hxy hf.continuousOn ((hs hx).trans (hs hy).symm)
    exact ⟨z, ht z hdz, hz⟩
  omega

/-- Rolle's theorem including repeated zeros: differentiating loses at most one zero,
with multiplicity measured by Mathlib's analytic order. -/
theorem rolle_multiplicity {f : ℝ → ℝ} {n : ℕ}
    (hf : ∀ x, AnalyticAt ℝ f x) (hd : ZeroMultiplicityBound (deriv f) n) :
    ZeroMultiplicityBound f (n + 1) := by
  classical
  obtain ⟨t, ht, htn⟩ := hd
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hfinite := finite_zeros_of_finite_deriv_zeros hfcont (fun x hx => (ht x).mp hx)
  let s := hfinite.toFinset
  have hs (x : ℝ) : f x = 0 ↔ x ∈ s := by simp [s]
  have hcard : s.card ≤ (t \ s).card + 1 := by
    apply Finset.card_le_sdiff_of_interleaved
    intro x hx y hy hxy _
    obtain ⟨z, hz, hdz⟩ := exists_deriv_eq_zero hxy hfcont.continuousOn
      (((hs x).mpr hx).trans ((hs y).mpr hy).symm)
    exact ⟨z, (ht z).mp hdz, hz⟩
  have horder (x : ℝ) (hx : x ∈ s) :
      analyticOrderAt f x = analyticOrderAt (deriv f) x + 1 := by
    simpa [(hs x).mpr hx] using (hf x).analyticOrderAt_deriv_add_one.symm
  have hone (x : ℝ) (hx : x ∈ t \ s) : (1 : ℕ∞) ≤ analyticOrderAt (deriv f) x := by
    exact Order.one_le_iff_ne_zero.mpr ((hf x).deriv.analyticOrderAt_ne_zero.mpr
      ((ht x).mpr (Finset.mem_sdiff.mp hx).1))
  have hsum : (∑ x ∈ s, analyticOrderAt (deriv f) x) +
      (∑ x ∈ t \ s, analyticOrderAt (deriv f) x) = ∑ x ∈ t, analyticOrderAt (deriv f) x := by
    rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
    symm
    exact Finset.sum_subset Finset.subset_union_right (fun x _ hx => by
      exact (hf x).deriv.analyticOrderAt_eq_zero.mpr (fun h => hx ((ht x).mp h)))
  refine ⟨s, hs, ?_⟩
  calc
    (∑ x ∈ s, analyticOrderAt f x) =
        (∑ x ∈ s, analyticOrderAt (deriv f) x) + (s.card : ℕ∞) := by
      simp_rw [Finset.sum_congr rfl horder, Finset.sum_add_distrib]
      simp
    _ ≤ (∑ x ∈ s, analyticOrderAt (deriv f) x) + ((t \ s).card + 1 : ℕ) := by
      exact add_le_add le_rfl (show (s.card : ℕ∞) ≤ ((t \ s).card + 1 : ℕ) by exact_mod_cast hcard)
    _ ≤ (∑ x ∈ s, analyticOrderAt (deriv f) x) +
        ((∑ x ∈ t \ s, analyticOrderAt (deriv f) x) + 1) := by
      simp only [Nat.cast_add, Nat.cast_one]
      exact add_le_add le_rfl (add_le_add (by simpa using Finset.sum_le_sum hone) le_rfl)
    _ = (∑ x ∈ t, analyticOrderAt (deriv f) x) + 1 := by rw [← add_assoc, hsum]
    _ ≤ ((n + 1 : ℕ) : ℕ∞) := by simpa only [Nat.cast_add, Nat.cast_one] using add_le_add htn (le_refl (1 : ℕ∞))

theorem zeroMultiplicityBound_zero_of_nonvanishing {f : ℝ → ℝ} (hf : ∀ x, f x ≠ 0) :
    ZeroMultiplicityBound f 0 := by
  exact ⟨∅, by simp [hf], by simp⟩

theorem ZeroMultiplicityBound.mul_nonvanishing {f g : ℝ → ℝ} {n : ℕ}
    (h : ZeroMultiplicityBound f n) (hf : ∀ x, AnalyticAt ℝ f x)
    (hg : ∀ x, AnalyticAt ℝ g x) (hgz : ∀ x, g x ≠ 0) :
    ZeroMultiplicityBound (fun x => f x * g x) n := by
  obtain ⟨s, hs, hn⟩ := h
  refine ⟨s, fun x => by simpa [mul_eq_zero, hgz] using hs x, ?_⟩
  have ho (x : ℝ) : analyticOrderAt (fun x => f x * g x) x = analyticOrderAt f x := by
    rw [show (fun x => f x * g x) = f * g from rfl, analyticOrderAt_mul (hf x) (hg x),
      (hg x).analyticOrderAt_eq_zero.mpr (hgz x), add_zero]
  simpa only [ho] using hn

theorem zeroMultiplicityBound_one_of_deriv_pos {f : ℝ → ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (hd : ∀ x, 0 < deriv f x) :
    ZeroMultiplicityBound f 1 :=
  rolle_multiplicity hf (zeroMultiplicityBound_zero_of_nonvanishing (fun x => (hd x).ne'))

theorem hasDerivAt_scaled_exp (c r x : ℝ) :
    HasDerivAt (fun x => c * Real.exp (r * x)) (c * r * Real.exp (r * x)) x := by
  simpa only [id_eq, mul_assoc, mul_comm, mul_left_comm, one_mul] using
    (((hasDerivAt_id x).const_mul r).exp.const_mul c)

/-- Distinct real exponential rates, with all coefficients nonzero, have at most
one fewer real zeros than terms, counted with analytic multiplicity. -/
theorem exponential_sum_zeros {ι : Type*} (s : Finset ι) (c r : ι → ℝ)
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) :
    ZeroMultiplicityBound (fun x => ∑ i ∈ s, c i * Real.exp (r i * x)) (s.card - 1) := by
  classical
  induction s using Finset.induction_on generalizing c r with
  | empty => simp at hs
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
    by_cases hs' : s.Nonempty
    · let u : ℝ → ℝ := fun x => c a + ∑ i ∈ s, c i * Real.exp ((r i - r a) * x)
      let d : ℝ → ℝ := fun x => ∑ i ∈ s, (c i * (r i - r a)) * Real.exp ((r i - r a) * x)
      have hderiv (x : ℝ) : HasDerivAt u (d x) x := by
        simpa [u, d] using
          (HasDerivAt.sum (fun i (_ : i ∈ s) => hasDerivAt_scaled_exp (c i) (r i - r a) x)).const_add (c a)
      have hd : ZeroMultiplicityBound d (s.card - 1) := by
        apply ih (fun i => c i * (r i - r a)) (fun i => r i - r a) hs'
        · intro i hi
          apply mul_ne_zero (hc i (Finset.mem_insert_of_mem hi))
          intro hz
          have he := hr (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s) (sub_eq_zero.mp hz)
          exact ha (he ▸ hi)
        · intro i hi j hj hij
          exact hr (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) (by linarith)
      have hdu : deriv u = d := funext (fun x => (hderiv x).deriv)
      have hu : ∀ x, AnalyticAt ℝ u x := by intro x; dsimp [u]; fun_prop
      have hb : ZeroMultiplicityBound u s.card := by
        have hh := rolle_multiplicity hu (hdu.symm ▸ hd)
        simpa [Nat.sub_add_cancel hs'.card_pos] using hh
      have hmul := hb.mul_nonvanishing hu
        (show ∀ x, AnalyticAt ℝ (fun x => Real.exp (r a * x)) x by intro x; fun_prop)
        (fun x => Real.exp_ne_zero _)
      convert hmul using 1
      funext x
      rw [Finset.sum_insert ha]
      dsimp [u]
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      subst s
      simpa using zeroMultiplicityBound_zero_of_nonvanishing
        (f := fun x => c a * Real.exp (r a * x))
        (fun x => mul_ne_zero (hc a (Finset.mem_insert_self a ∅)) (Real.exp_ne_zero _))

theorem ZeroMultiplicityBound.mono {f : ℝ → ℝ} {m n : ℕ}
    (h : ZeroMultiplicityBound f m) (hmn : m ≤ n) : ZeroMultiplicityBound f n := by
  obtain ⟨s, hs, hb⟩ := h
  exact ⟨s, hs, hb.trans (by exact_mod_cast hmn)⟩

/-- Zero coefficients are harmless: only nonzeroness of the represented function is required. -/
theorem exponential_sum_zeros_of_nonzero {ι : Type*} (s : Finset ι) (c r : ι → ℝ)
    (hr : Set.InjOn r s) (hn : ∃ x, (∑ i ∈ s, c i * Real.exp (r i * x)) ≠ 0) :
    ZeroMultiplicityBound (fun x => ∑ i ∈ s, c i * Real.exp (r i * x)) (s.card - 1) := by
  classical
  let t := s.filter (fun i => c i ≠ 0)
  have he (x : ℝ) : (∑ i ∈ t, c i * Real.exp (r i * x)) = ∑ i ∈ s, c i * Real.exp (r i * x) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hni
    have hc : c i = 0 := by simpa [t, hi] using hni
    simp [hc]
  have ht : t.Nonempty := by
    by_contra hh
    have he' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    obtain ⟨x, hx⟩ := hn
    rw [← he x, he'] at hx
    simp at hx
  have h := exponential_sum_zeros t c r ht (fun i hi => (Finset.mem_filter.mp hi).2)
    (hr.mono (Finset.filter_subset _ _))
  have hb := h.mono (Nat.sub_le_sub_right (Finset.card_le_card (Finset.filter_subset _ _)) 1)
  simpa only [he] using hb

/-- The sharper four-term sign pattern `+,-,-,+` has at most two zeros,
including multiplicities. -/
theorem four_term_zeros_exp (A B C D α β γ δ : ℝ)
    (hA : 0 < A) (_hB : 0 < B) (hC : 0 < C) (_hD : 0 < D)
    (hab : α < β) (hbc : β < γ) (hcd : γ < δ) :
    ZeroMultiplicityBound (fun x => A * Real.exp (α * x) - B * Real.exp (β * x) -
      C * Real.exp (γ * x) + D * Real.exp (δ * x)) 2 := by
  let u : ℝ → ℝ := fun x => A * Real.exp ((α - β) * x) - B -
    C * Real.exp ((γ - β) * x) + D * Real.exp ((δ - β) * x)
  let v : ℝ → ℝ := fun x => A * (α - β) * Real.exp ((α - δ) * x) -
    C * (γ - β) * Real.exp ((γ - δ) * x) + D * (δ - β)
  have hu (x : ℝ) : AnalyticAt ℝ u x := by dsimp [u]; fun_prop
  have hv (x : ℝ) : AnalyticAt ℝ v x := by dsimp [v]; fun_prop
  have hvd (x : ℝ) : 0 < deriv v x := by
    have hd := ((hasDerivAt_scaled_exp (A * (α - β)) (α - δ) x).sub
      (hasDerivAt_scaled_exp (C * (γ - β)) (γ - δ) x)).add_const (D * (δ - β))
    change HasDerivAt v _ x at hd
    rw [hd.deriv]
    have h1 : 0 < A * (α - β) * (α - δ) * Real.exp ((α - δ) * x) :=
      mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hA (sub_neg.mpr hab))
        (sub_neg.mpr (hab.trans (hbc.trans hcd)))) (Real.exp_pos _)
    have h2 : C * (γ - β) * (γ - δ) * Real.exp ((γ - δ) * x) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hC (sub_pos.mpr hbc))
        (sub_neg.mpr hcd)) (Real.exp_pos _)
    linarith
  have hvbound := zeroMultiplicityBound_one_of_deriv_pos hv hvd
  have hdu (x : ℝ) : deriv u x = v x * Real.exp ((δ - β) * x) := by
    have hd := (((hasDerivAt_scaled_exp A (α - β) x).sub_const B).sub
      (hasDerivAt_scaled_exp C (γ - β) x)).add (hasDerivAt_scaled_exp D (δ - β) x)
    change HasDerivAt u _ x at hd
    rw [hd.deriv]
    dsimp [v]
    have hexp (r : ℝ) : Real.exp ((r - β) * x) =
        Real.exp ((r - δ) * x) * Real.exp ((δ - β) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp α, hexp γ]
    ring
  have hdubound : ZeroMultiplicityBound (deriv u) 1 := by
    have hb := hvbound.mul_nonvanishing hv
      (show ∀ x, AnalyticAt ℝ (fun x => Real.exp ((δ - β) * x)) x by intro x; fun_prop)
      (fun x => Real.exp_ne_zero _)
    simpa only [← hdu] using hb
  have hubound := rolle_multiplicity hu hdubound
  have hb := hubound.mul_nonvanishing hu
    (show ∀ x, AnalyticAt ℝ (fun x => Real.exp (β * x)) x by intro x; fun_prop)
    (fun x => Real.exp_ne_zero _)
  convert hb using 1
  funext x
  have hexp (r : ℝ) : Real.exp (r * x) =
      Real.exp ((r - β) * x) * Real.exp (β * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp α, hexp γ, hexp δ]
  dsimp [u]
  ring

/-- The manuscript's first zero-count assertion, in positive-base notation. -/
theorem exponential_sum_zeros_rpow {ι : Type*} (s : Finset ι) (c b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) (hi : Set.InjOn b s)
    (hn : ∃ x : ℝ, (∑ i ∈ s, c i * (b i) ^ x) ≠ 0) :
    ZeroMultiplicityBound (fun x : ℝ => ∑ i ∈ s, c i * (b i) ^ x) (s.card - 1) := by
  have he (x : ℝ) : (∑ i ∈ s, c i * (b i) ^ x) =
      ∑ i ∈ s, c i * Real.exp (Real.log (b i) * x) := by
    exact Finset.sum_congr rfl (fun i hi => by rw [Real.rpow_def_of_pos (hb i hi)])
  have hr : Set.InjOn (fun i => Real.log (b i)) s := by
    intro i hi' j hj' hij
    exact hi hi' hj' (Real.log_injOn_pos (hb i hi') (hb j hj') hij)
  have hz := exponential_sum_zeros_of_nonzero s c (fun i => Real.log (b i)) hr
    (by simpa only [he] using hn)
  simpa only [he] using hz

/-- The manuscript's sharper `+,-,-,+` four-term assertion in positive-base notation. -/
theorem four_term_zeros (A B C D a b c d : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ZeroMultiplicityBound (fun x : ℝ => A * a ^ x - B * b ^ x - C * c ^ x + D * d ^ x) 2 := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hd := hc.trans hcd
  simpa only [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb,
    Real.rpow_def_of_pos hc, Real.rpow_def_of_pos hd] using
    four_term_zeros_exp A B C D (Real.log a) (Real.log b) (Real.log c) (Real.log d)
      hA hB hC hD (Real.log_lt_log ha hab) (Real.log_lt_log hb hbc) (Real.log_lt_log hc hcd)

end
end EntropyConstrainedMissingMass
