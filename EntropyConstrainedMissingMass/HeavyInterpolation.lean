import EntropyConstrainedMissingMass.BranchEntropy
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Real multiplicity interpolation of the heavy entropy branch. -/

open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section

/-- The heavy root; outside its natural domain the value is immaterial. -/
def heavyRoot (h m : ℝ) : ℝ := by
  classical
  exact if he : ∃ z, z ∈ Ioo (1 / (m + 1)) 1 ∧ branchEntropy m z = h then he.choose else 0

theorem heavyRoot_spec {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    heavyRoot h m ∈ Ioo (1 / (m + 1)) 1 ∧ branchEntropy m (heavyRoot h m) = h := by
  have hm0 : 0 < m := lt_of_le_of_lt (by linarith [Real.one_le_exp_iff.mpr hh.le]) hm
  have he := (existsUnique_heavy_entropy_root hm0 hh
    ((Real.lt_log_iff_exp_lt (by positivity)).mpr (by linarith))).exists
  simp only [heavyRoot, dite_eq_left he]
  exact he.choose_spec

theorem heavyRoot_eq_of_spec {h m z : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m)
    (hz : z ∈ Ioo (1 / (m + 1)) 1) (he : branchEntropy m z = h) : heavyRoot h m = z := by
  have hm0 : 0 < m := lt_of_le_of_lt (by linarith [Real.one_le_exp_iff.mpr hh.le]) hm
  have hs := heavyRoot_spec hh hm
  exact (strictAntiOn_branchEntropy hm0).injOn ⟨hs.1.1.le, hs.1.2.le⟩
    ⟨hz.1.le, hz.2.le⟩ (hs.2.trans he.symm)

private def entropyPair (u : ℝ × ℝ) : ℝ := branchEntropy u.1 u.2

private theorem contDiffAt_entropyPair {m z : ℝ} (hm : 0 < m) (hz : 0 < z) (hz1 : z < 1) :
    ContDiffAt ℝ ⊤ entropyPair (m,z) := by
  unfold entropyPair branchEntropy
  have hfst : ContDiffAt ℝ ⊤ (fun u : ℝ × ℝ => u.1) (m,z) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ ⊤ (fun u : ℝ × ℝ => u.2) (m,z) := contDiffAt_snd
  exact (hsnd.neg.mul (hsnd.log hz.ne')).sub
    ((contDiffAt_const.sub hsnd).mul (((contDiffAt_const.sub hsnd).div hfst hm.ne').log
      (div_ne_zero (sub_pos.mpr hz1).ne' hm.ne')))

private theorem entropyPair_partial_z {m z : ℝ} (hm : 0 < m) (hz : 0 < z) (hz1 : z < 1) :
    fderiv ℝ entropyPair (m,z) (0,1) = Real.log ((1-z)/(m*z)) := by
  have hf := (contDiffAt_entropyPair hm hz hz1).differentiableAt (by simp)
  have hd := hf.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z m).prodMk (hasDerivAt_id z))
  exact hd.unique (hasDerivAt_branchEntropy hm hz hz1)

private theorem entropyPair_z_invertible {m z : ℝ} (hm : 0 < m)
    (hz : z ∈ Ioo (1 / (m+1)) 1) :
    (fderiv ℝ entropyPair (m,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  have hz0 : 0 < z := lt_trans (by positivity) hz.1
  have hn : Real.log ((1-z)/(m*z)) ≠ 0 := by
    apply ne_of_lt
    apply Real.log_neg (div_pos (sub_pos.mpr hz.2) (mul_pos hm hz0))
    apply (div_lt_one (mul_pos hm hz0)).mpr
    have := (div_lt_iff₀ (show 0 < m+1 by positivity)).mp hz.1
    nlinarith
  have heq : fderiv ℝ entropyPair (m,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (Real.log ((1-z)/(m*z))) := by
    apply ContinuousLinearMap.ext_ring
    simpa using entropyPair_partial_z hm hz0 hz.2
  rw [heq]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (Real.log ((1-z)/(m*z)))⁻¹)
  · ext; simp [hn]
  · ext; simp [hn]

/-- Smoothness follows from the implicit function theorem and uniqueness of the
heavy root, rather than being imposed as a hypothesis. -/
theorem contDiffAt_heavyRoot {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    ContDiffAt ℝ ⊤ (heavyRoot h) m := by
  have hm0 : 0 < m := lt_of_le_of_lt (by linarith [Real.one_le_exp_iff.mpr hh.le]) hm
  let z := heavyRoot h m
  have hs := heavyRoot_spec hh hm
  have hz0 : 0 < z := lt_trans (by positivity) hs.1.1
  let hc := contDiffAt_entropyPair hm0 hz0 hs.1.2
  let hi := entropyPair_z_invertible hm0 hs.1
  let g := hc.implicitFunction (by simp) hi
  have hg : g m = z := ContDiffAt.implicitFunction_apply_self hc (by simp) hi
  have hgc : ContDiffAt ℝ ⊤ g m := ContDiffAt.contDiffAt_implicitFunction hc (by simp) hi
  have he : ∀ᶠ r in 𝓝 m, branchEntropy r (g r) = h := by
    have he := hc.eventually_apply_implicitFunction (by simp) hi
    change ∀ᶠ r in 𝓝 m, branchEntropy r (g r) = branchEntropy m z at he
    simpa only [z, hs.2] using he
  have hdom : ∀ᶠ r in 𝓝 m, Real.exp h - 1 < r := eventually_gt_nhds hm
  have hgt : ∀ᶠ r in 𝓝 m, 1 / (r+1) < g r := by
    apply (continuousAt_const.div (continuousAt_id.add continuousAt_const)
      (show m+1 ≠ 0 by positivity)).eventually_lt hgc.continuousAt
    simpa only [Pi.div_apply, Pi.add_apply, id_eq, hg] using hs.1.1
  have hlt : ∀ᶠ r in 𝓝 m, g r < 1 := by
    apply hgc.continuousAt.eventually_lt continuousAt_const
    simpa only [hg] using hs.1.2
  apply hgc.congr_of_eventuallyEq
  filter_upwards [hdom, hgt, hlt, he] with r hr hgr hgl her
  exact (heavyRoot_eq_of_spec hh hr ⟨hgr,hgl⟩ her)

/-- Repeated light mass at real multiplicity. -/
def heavyLight (h m : ℝ) : ℝ := (1 - heavyRoot h m) / m

/-- Positive logarithmic heavy/light mass ratio. -/
def heavySigma (h m : ℝ) : ℝ := Real.log (heavyRoot h m / heavyLight h m)

theorem heavy_parameters_pos {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    0 < m ∧ 0 < heavyLight h m ∧ heavyLight h m < heavyRoot h m ∧
      heavyRoot h m < 1 ∧ 0 < heavySigma h m := by
  have hm0 : 0 < m := lt_of_le_of_lt (by linarith [Real.one_le_exp_iff.mpr hh.le]) hm
  have hs := heavyRoot_spec hh hm
  have ho := heavy_parameter_mass_order hm0 hs.1
  refine ⟨hm0, ho.1, ho.2, hs.1.2, ?_⟩
  exact Real.log_pos ((one_lt_div ho.1).mpr ho.2)

theorem heavySigma_eq {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    heavySigma h m = Real.log (heavyRoot h m) + Real.log m - Real.log (1-heavyRoot h m) := by
  obtain ⟨hm0,hq,hqz,hz1,_⟩ := heavy_parameters_pos hh hm
  have hz : 0 < heavyRoot h m := hq.trans hqz
  rw [heavySigma, Real.log_div hz.ne' hq.ne', heavyLight,
    Real.log_div (sub_pos.mpr hz1).ne' hm0.ne']
  ring

/-- The actual derivative of the implicit heavy root is `q/σ`. -/
theorem hasDerivAt_heavyRoot {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    HasDerivAt (heavyRoot h) (heavyLight h m / heavySigma h m) m := by
  obtain ⟨hm0,hq,hqz,hz1,hsig⟩ := heavy_parameters_pos hh hm
  have hz : 0 < heavyRoot h m := hq.trans hqz
  have hd := ((contDiffAt_heavyRoot hh hm).differentiableAt (by simp)).hasDerivAt
  have h1 := ((Real.hasDerivAt_negMulLog hz.ne').comp m hd).add
    ((Real.hasDerivAt_negMulLog (sub_pos.mpr hz1).ne').comp m (hd.const_sub 1))
  have h2 := h1.add ((hd.const_sub 1).mul (Real.hasDerivAt_log hm0.ne'))
  have he : (fun r => Real.negMulLog (heavyRoot h r) + Real.negMulLog (1-heavyRoot h r) +
      (1-heavyRoot h r)*Real.log r) =ᶠ[𝓝 m] (fun _ => h) := by
    filter_upwards [eventually_gt_nhds hm] with r hr
    rw [← branchEntropy_eq_negMulLog (show r ≠ 0 by
      have : 0 < r := lt_of_le_of_lt (by linarith [Real.one_le_exp_iff.mpr hh.le]) hr
      exact this.ne')]
    exact (heavyRoot_spec hh hr).2
  have heq := h2.unique ((hasDerivAt_const m h).congr_of_eventuallyEq he)
  have hder : deriv (heavyRoot h) m = heavyLight h m / heavySigma h m := by
    apply (eq_div_iff hsig.ne').mpr
    rw [heavySigma_eq hh hm, heavyLight]
    rw [div_eq_mul_inv]
    nlinarith [heq]
  rwa [hder] at hd

/-- The actual derivative of the light mass along the implicit heavy branch. -/
theorem hasDerivAt_heavyLight {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    HasDerivAt (heavyLight h)
      (-(heavyLight h m * (1+heavySigma h m)) / (m*heavySigma h m)) m := by
  obtain ⟨hm0,_,_,_,hsig⟩ := heavy_parameters_pos hh hm
  have hd := ((hasDerivAt_heavyRoot hh hm).const_sub 1).div (hasDerivAt_id m) hm0.ne'
  convert hd using 1
  · rfl
  · dsimp [heavyLight]
    field_simp
    ring

/-- Entropy in logarithmic heavy/light coordinates. -/
theorem heavy_entropy_sigma {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) :
    h = -Real.log (heavyRoot h m) + (1-heavyRoot h m)*heavySigma h m := by
  obtain ⟨hm0,hq,hqz,hz1,_⟩ := heavy_parameters_pos hh hm
  have he := (heavyRoot_spec hh hm).2
  rw [branchEntropy_eq_negMulLog hm0.ne', Real.negMulLog, Real.negMulLog] at he
  rw [heavySigma_eq hh hm]
  linarith only [he]

/-- Real sample-size missing-mass summand. -/
def realMissingMassTerm (s u : ℝ) : ℝ := u * (1-u)^s

/-- Its derivative on `u<1`, in a form convenient for sign comparisons. -/
def realMissingMassDeriv (s u : ℝ) : ℝ := (1-u)^(s-1) * (1-(s+1)*u)

theorem hasDerivAt_realMissingMassTerm (s : ℝ) {u : ℝ} (hu : u < 1) :
    HasDerivAt (realMissingMassTerm s) (realMissingMassDeriv s u) u := by
  have hd := (hasDerivAt_id u).mul (((hasDerivAt_id u).const_sub 1).rpow_const (p := s)
    (Or.inl (sub_pos.mpr hu).ne'))
  convert hd using 1
  · rfl
  · simp only [realMissingMassDeriv, id_eq]
    rw [Real.rpow_sub_one (sub_pos.mpr hu).ne']
    field_simp [(sub_pos.mpr hu).ne']
    ring

/-- The heavy-family value, interpolated in both multiplicity and sample size. -/
def heavyValue (h s m : ℝ) : ℝ :=
  realMissingMassTerm s (heavyRoot h m) + m * realMissingMassTerm s (heavyLight h m)

/-- The sign-controlling expression in the manuscript. -/
def heavyPsi (s z q : ℝ) : ℝ :=
  realMissingMassDeriv s z - realMissingMassDeriv s q +
    s*q*Real.log (z/q)*(1-q)^(s-1)

/-- Actual objective derivative for arbitrary real exponent. -/
theorem hasDerivAt_heavyValue {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) (s : ℝ) :
    HasDerivAt (heavyValue h s)
      (heavyLight h m / heavySigma h m * heavyPsi s (heavyRoot h m) (heavyLight h m)) m := by
  obtain ⟨hm0,hq,hqz,hz1,hsig⟩ := heavy_parameters_pos hh hm
  have hq1 := hqz.trans hz1
  have hd := ((hasDerivAt_realMissingMassTerm s hz1).comp m (hasDerivAt_heavyRoot hh hm)).add
    ((hasDerivAt_id m).mul
      ((hasDerivAt_realMissingMassTerm s hq1).comp m (hasDerivAt_heavyLight hh hm)))
  convert hd using 1
  · rfl
  · change heavyLight h m / heavySigma h m *
      (realMissingMassDeriv s (heavyRoot h m) - realMissingMassDeriv s (heavyLight h m) +
        s*heavyLight h m*heavySigma h m*(1-heavyLight h m)^(s-1)) = _
    simp only [realMissingMassTerm, realMissingMassDeriv, Function.comp_apply, id_eq]
    rw [Real.rpow_sub_one (sub_pos.mpr hq1).ne']
    field_simp
    ring

end
end EntropyConstrainedMissingMass
