import EntropyConstrainedMissingMass.AsymptoticInversion
import EntropyConstrainedMissingMass.HeavyInterpolation

/-! The actual entropy root at the integer multiplicity ceil(h t). -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The integer multiplicity used for the asymptotic lower candidate. -/
def roundedMultiplicity (h t : ℝ) : ℕ := ⌈h * t⌉₊

def roundedTailMass (h t : ℝ) : ℝ := 1 - heavyRoot h (roundedMultiplicity h t)

def roundedEntropyScale (h t : ℝ) : ℝ := h / roundedTailMass h t

/-- Entropy dominates the total light mass times the logarithm of its multiplicity. -/
theorem heavy_tail_entropy_ge (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (hL1 : L < 1) :
    L * Real.log m ≤ branchEntropy m (1 - L) := by
  have h0 := Real.negMulLog_nonneg hL.le hL1.le
  have h1 := Real.negMulLog_nonneg (show 0 ≤ 1 - L by linarith) (show 1 - L ≤ 1 by linarith)
  rw [heavy_tail_entropy, Real.log_div (ne_of_gt hL) (ne_of_gt hm)]
  simp only [Real.negMulLog] at h0 h1
  nlinarith only [h0, h1]

/-- A uniform first-order bound following from the actual quadratic remainder. -/
theorem entropyTailCorrection_sub_one_bound (L : ℝ) (hL : 0 < L) (hL1 : L < 1) :
    |entropyTailCorrection L - 1| ≤ 2 * L := by
  have h := entropyTailCorrection_remainder_bound L hL hL1
  have ht := abs_sub_le (entropyTailCorrection L) (1 - L / 2) 1
  have he : |(1 - L / 2) - 1| = L / 2 := by
    rw [show (1 - L / 2) - 1 = -(L / 2) by ring, abs_neg, abs_of_pos (by positivity)]
  rw [he] at ht
  nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hL1.le)]

/-- A finite error estimate for any multiplicity in the rounding interval [h t,h t+1]. -/
theorem rounded_entropy_residual_bound (h t m L : ℝ)
    (hh : 0 < h) (ht : 0 < t) (hT : 4 ≤ Real.log t)
    (hlogh : 2 * |Real.log h| ≤ Real.log t) (hlogt : Real.log t ≤ h * t)
    (hml : h * t ≤ m) (hmu : m ≤ h * t + 1)
    (hL : 0 < L) (hL1 : L < 1) (he : branchEntropy m (1 - L) = h) :
    2 ≤ h / L ∧
      |(h / L - Real.log (h / L)) - (Real.log t + 1)| ≤ (1 + 4 * h) / Real.log t := by
  have hm : 0 < m := (mul_pos hh ht).trans_le hml
  have hTp : 0 < Real.log t := by linarith
  have hlm : Real.log t / 2 ≤ Real.log m := by
    have hlog := Real.log_le_log (mul_pos hh ht) hml
    rw [Real.log_mul (ne_of_gt hh) (ne_of_gt ht)] at hlog
    linarith [neg_abs_le (Real.log h)]
  have hd : Real.log m ≤ h / L := by
    apply (le_div_iff₀ hL).mpr
    have h := heavy_tail_entropy_ge m L hm hL hL1
    rw [he] at h
    nlinarith only [h]
  have hLb : L ≤ 2 * h / Real.log t := by
    apply (le_div_iff₀ hTp).mpr
    have hhL := (le_div_iff₀ hL).mp hd
    nlinarith [mul_le_mul_of_nonneg_right hlm hL.le]
  have hlogratio0 : 0 ≤ Real.log (m / (h * t)) := by
    apply Real.log_nonneg
    exact (one_le_div (mul_pos hh ht)).mpr hml
  have hlogratio : Real.log (m / (h * t)) ≤ 1 / Real.log t := by
    have hb0 := Real.log_le_sub_one_of_pos (div_pos hm (mul_pos hh ht))
    have hb : m / (h * t) - 1 ≤ 1 / (h * t) := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ (mul_pos hh ht)).mpr
      field_simp
      linarith only [hmu]
    exact hb0.trans (hb.trans (one_div_le_one_div_of_le hTp hlogt))
  have hA := entropyTailCorrection_sub_one_bound L hL hL1
  have hi := heavy_tail_entropy_inversion m L h hm hL hh he
  have hlogid : Real.log (m / h) - Real.log t = Real.log (m / (h * t)) := by
    rw [Real.log_div (ne_of_gt hm) (ne_of_gt hh),
      Real.log_div (ne_of_gt hm) (ne_of_gt (mul_pos hh ht)),
      Real.log_mul (ne_of_gt hh) (ne_of_gt ht)]
    ring
  have hid : (h / L - Real.log (h / L)) - (Real.log t + 1) =
      Real.log (m / (h * t)) + (entropyTailCorrection L - 1) := by
    linarith only [hi, hlogid]
  refine ⟨by linarith, ?_⟩
  rw [hid]
  have htriangle := abs_add_le (Real.log (m / (h * t))) (entropyTailCorrection L - 1)
  rw [abs_of_nonneg hlogratio0] at htriangle
  calc
    _ ≤ 1 / Real.log t + 2 * L := by linarith only [htriangle, hlogratio, hA]
    _ ≤ (1 + 4 * h) / Real.log t := by
      have hmL := mul_le_mul_of_nonneg_left hLb (by norm_num : (0 : ℝ) ≤ 2)
      convert add_le_add_left hmL (1 / Real.log t) using 1 <;> ring

/-- The rounded heavy root has an actual entropy equation for all sufficiently large t. -/
theorem roundedTailMass_eventually_spec (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℝ in atTop, 0 < roundedTailMass h t ∧ roundedTailMass h t < 1 ∧
      branchEntropy (roundedMultiplicity h t) (1 - roundedTailMass h t) = h := by
  have he : Tendsto (fun t : ℝ => h * t) atTop atTop := Tendsto.const_mul_atTop hh tendsto_id
  filter_upwards [he.eventually_gt_atTop (Real.exp h), eventually_gt_atTop (0 : ℝ)] with t hlarge ht
  have hm : Real.exp h - 1 < (roundedMultiplicity h t : ℝ) := by
    have hc := Nat.le_ceil (h * t)
    change h * t ≤ (roundedMultiplicity h t : ℝ) at hc
    linarith
  have hs := heavyRoot_spec hh hm
  have hmpos : 0 < (roundedMultiplicity h t : ℝ) :=
    (mul_pos hh ht).trans_le (Nat.le_ceil (h * t))
  have hzpos : 0 < heavyRoot h (roundedMultiplicity h t) :=
    (by positivity : 0 < 1 / ((roundedMultiplicity h t : ℝ) + 1)).trans hs.1.1
  refine ⟨by dsimp [roundedTailMass]; linarith [hs.1.2], by dsimp [roundedTailMass]; linarith, ?_⟩
  simpa only [roundedTailMass, sub_sub_cancel] using hs.2

/-- The actual rounded entropy root has residual O_h(1/log t). -/
theorem rounded_entropy_residual (h : ℝ) (hh : 0 < h) :
    (∀ᶠ t : ℝ in atTop, 2 ≤ roundedEntropyScale h t) ∧
    (fun t : ℝ => (roundedEntropyScale h t - Real.log (roundedEntropyScale h t)) -
      (Real.log t + 1)) =O[atTop] (fun t => 1 / Real.log t) := by
  have hev : ∀ᶠ t : ℝ in atTop, 2 ≤ roundedEntropyScale h t ∧
      |(roundedEntropyScale h t - Real.log (roundedEntropyScale h t)) - (Real.log t + 1)| ≤
        (1 + 4 * h) / Real.log t := by
    filter_upwards [roundedTailMass_eventually_spec h hh, eventually_gt_atTop (0 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop 4,
      Real.tendsto_log_atTop.eventually_ge_atTop (2 * |Real.log h|),
      Real.isLittleO_log_id_atTop.def hh] with t hs ht hT hlogh hlogt
    have hlogt' : Real.log t ≤ h * t := by
      simpa only [Real.norm_eq_abs, abs_of_pos ht, abs_of_nonneg (by linarith : 0 ≤ Real.log t), id_eq] using hlogt
    exact rounded_entropy_residual_bound h t (roundedMultiplicity h t) (roundedTailMass h t)
      hh ht hT hlogh hlogt' (Nat.le_ceil _) (Nat.ceil_lt_add_one (mul_pos hh ht).le).le hs.1 hs.2.1 hs.2.2
  refine ⟨hev.mono (fun _ ht => ht.1), Asymptotics.isBigO_iff.mpr ⟨1 + 4 * h, ?_⟩⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_gt_atTop 0] with t ht hlog
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos (one_div_pos.mpr hlog)]
  convert ht.2 using 1
  ring

/-- A uniform lower bound on the actual rounded entropy scale. -/
theorem rounded_entropy_scale_log_lower (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℝ in atTop, Real.log t / 2 ≤ roundedEntropyScale h t := by
  filter_upwards [roundedTailMass_eventually_spec h hh, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * |Real.log h|)] with t hs ht hlogh
  have hm : 0 < (roundedMultiplicity h t : ℝ) :=
    (mul_pos hh ht).trans_le (Nat.le_ceil (h * t))
  have hlog := Real.log_le_log (mul_pos hh ht) (Nat.le_ceil (h * t))
  rw [Real.log_mul (ne_of_gt hh) (ne_of_gt ht)] at hlog
  have hlm : Real.log t / 2 ≤ Real.log (roundedMultiplicity h t) := by
    change Real.log h + Real.log t ≤ Real.log (roundedMultiplicity h t) at hlog
    linarith [neg_abs_le (Real.log h)]
  have hd := heavy_tail_entropy_ge (roundedMultiplicity h t) (roundedTailMass h t) hm hs.1 hs.2.1
  rw [hs.2.2] at hd
  apply hlm.trans
  apply (le_div_iff₀ hs.1).mpr
  nlinarith only [hd]

/-- The entropy scale of m=ceil(h t) has the sharp first correction of the manuscript. -/
theorem rounded_entropy_scale_expansion (h : ℝ) (hh : 0 < h) :
    (fun t : ℝ => roundedEntropyScale h t - (Real.log t + Real.log (Real.log t) + 1))
      =O[atTop] (fun t => Real.log (Real.log t) / Real.log t) := by
  obtain ⟨hd, hr⟩ := rounded_entropy_residual h hh
  obtain ⟨C, hC, hr⟩ := Asymptotics.isBigO_iff'.mp hr
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨2 * (C + 2), ?_⟩
  filter_upwards [hd, hr, Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with t hd hr hT hTe
  have hTp : 0 < Real.log t := by linarith
  have hlog : 1 ≤ Real.log (Real.log t) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hTe
  have hlogp : 0 < Real.log (Real.log t) := by linarith
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num : (0 : ℝ) < 1) hTp)] at hr
  have hb := entropy_inversion_error_bound hT hd hr
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos hlogp hTp)]
  apply hb.trans
  have hnum : C + (Real.log (Real.log t) + 1) ≤ (C + 2) * Real.log (Real.log t) := by
    nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr hlog), hlog]
  have hdiv := (div_le_div_iff_of_pos_right hTp).mpr hnum
  convert mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

/-- The same expansion along the paper's natural sample sizes. -/
theorem rounded_entropy_scale_nat_expansion (h : ℝ) (hh : 0 < h) :
    (fun t : ℕ => roundedEntropyScale h t - (Real.log t + Real.log (Real.log t) + 1))
      =O[atTop] (fun t => Real.log (Real.log t) / Real.log t) :=
  (rounded_entropy_scale_expansion h hh).comp_tendsto tendsto_natCast_atTop_atTop

end
end EntropyConstrainedMissingMass
