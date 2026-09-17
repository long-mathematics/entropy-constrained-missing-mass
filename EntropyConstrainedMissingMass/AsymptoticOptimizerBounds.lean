import EntropyConstrainedMissingMass.AsymptoticHeavy
import EntropyConstrainedMissingMass.ScalarGapCoercivity

/-! Uniform scalar estimates for heavy maximizing parameters. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- Entropy prevents the largest atom of a heavy candidate from tending to zero. -/
theorem heavy_entropy_largest_atom_bound {m z h : ℝ} (hm : 0 < m)
    (hz : z ∈ Ioo (1 / (m + 1)) 1) (he : branchEntropy m z = h) :
    Real.exp (-h) ≤ z := by
  have hp := heavy_parameter_mass_order hm hz
  have hzpos : 0 < z := hp.1.trans hp.2
  have hlog := Real.log_le_log hp.1 hp.2.le
  have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hz.2.le)
  have hentropy : -Real.log z ≤ h := by
    rw [← he, branchEntropy]
    nlinarith only [hmul]
  have he' : -h ≤ Real.log z := by linarith
  simpa only [Real.exp_log hzpos] using Real.exp_le_exp.mpr he'

/-- Exact entropy in the scaled light-atom variable u=t L/m. -/
theorem heavy_scaled_entropy (t m L h : ℝ) (ht : 0 < t) (hm : 0 < m)
    (hL : 0 < L) (hh : 0 < h) (he : branchEntropy m (1 - L) = h) :
    h / L = Real.log t - Real.log (t * (L / m)) + entropyTailCorrection L := by
  have hi := heavy_tail_entropy_inversion m L h hm hL hh he
  rw [Real.log_div (ne_of_gt hm) (ne_of_gt hh),
    Real.log_div (ne_of_gt hh) (ne_of_gt hL)] at hi
  rw [Real.log_mul (ne_of_gt ht) (ne_of_gt (div_pos hL hm)),
    Real.log_div (ne_of_gt hL) (ne_of_gt hm)]
  linarith only [hi]

/-- The exponential envelope for the light block, valid for every natural sample size. -/
theorem light_block_le_exp (t : ℕ) {q : ℝ} (_hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ t ≤ Real.exp (-((t : ℝ) * q)) := by
  have he : 1 - q ≤ Real.exp (-q) := by simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-q)
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hq1) he t
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_neg] using hp

/-- The exact reciprocal perturbation estimate used to discard the exponentially small heavy atom. -/
theorem reciprocal_perturbation_bound {h B R r c : ℝ} (hh : 0 ≤ h) (hc : 0 < c)
    (hB : c ≤ B) (hR : c ≤ R) (hr : 0 ≤ r) (hBR : B ≤ R + r) :
    h / R - h / B ≤ h * r / c ^ 2 := by
  have hBp : 0 < B := hc.trans_le hB
  have hRp : 0 < R := hc.trans_le hR
  have hid : h / R - h / B = h * (B - R) / (R * B) := by field_simp
  rw [hid]
  have hden : c ^ 2 ≤ R * B := by nlinarith [mul_le_mul hR hB hc.le hRp.le]
  calc
    _ ≤ h * r / (R * B) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : B - R ≤ r) hh) (mul_pos hRp hBp).le
    _ ≤ h * r / c ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hh hr) (sq_pos_of_pos hc) hden

/-- Quantitative bootstrap: any competitive heavy block must have t q<1.
All hypotheses are finite inequalities, allowing one threshold to work for every optimizer. -/
theorem heavy_competitive_scaled_atom_lt_one (h T L u B r : ℝ)
    (hh : 0 < h) (hT : 0 < T) (hL : 0 < L) (hL1 : L < 1) (hu : 0 < u)
    (he : h / L = T - Real.log u + entropyTailCorrection L)
    (hBpos : 0 < B) (hBlow : h / (3 * T) ≤ B) (hBup : h / B ≤ 5 * T / 4)
    (hr : r ≤ h / (12 * T)) (hBR : B ≤ L * Real.exp (-u) + r)
    (hlog : Real.log (6 * T / h) ≤ T / 4) : u < 1 := by
  let R := L * Real.exp (-u)
  have hRp : 0 < R := by dsimp [R]; positivity
  have hRe : R * Real.exp u = L := by dsimp [R]; rw [mul_assoc, ← Real.exp_add]; simp
  have hRlow : h / (6 * T) ≤ R := by
    change B ≤ R + r at hBR
    have h0 : h / (3 * T) - h / (12 * T) ≥ h / (6 * T) := by
      field_simp
      nlinarith only [hh]
    linarith only [hBlow, hBR, hr, h0]
  have hexp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have huR : R * u ≤ L := (mul_le_mul_of_nonneg_left hexp hRp.le).trans_eq hRe
  have huBound : u ≤ 6 * T / h := by
    have ha := mul_le_mul_of_nonneg_right hRlow hu.le
    have hb : h / (6 * T) * u ≤ 1 := by linarith only [ha, huR, hL1]
    have hc : h * u ≤ 6 * T := by
      have hb' := (div_le_iff₀ (by positivity : 0 < 6 * T)).mp
        (show h * u / (6 * T) ≤ 1 by convert hb using 1; ring)
      simpa using hb'
    apply (le_div_iff₀ hh).mpr
    nlinarith only [hc]
  have hlogu := (Real.log_le_log hu huBound).trans hlog
  have hA := (entropyTailCorrection_bounds L hL hL1).1
  have hd : 3 * T / 4 ≤ h / L := by linarith only [he, hlogu, hA]
  have hLd : 3 * T * L ≤ 4 * h := by
    have hc := (le_div_iff₀ hL).mp hd
    nlinarith only [hc]
  by_contra hunot
  have hu1 : 1 ≤ u := le_of_not_gt hunot
  have hexp2 : 2 ≤ Real.exp u := by
    have hexp1 := Real.add_one_le_exp (1 : ℝ)
    have hm := Real.exp_le_exp.mpr hu1
    linarith only [hexp1, hm]
  have hRhalf : 2 * R ≤ L := by nlinarith [mul_le_mul_of_nonneg_left hexp2 hRp.le, hRe]
  have hBscaled := (div_le_iff₀ hBpos).mp hBup
  have hrscaled := (le_div_iff₀ (by positivity : 0 < 12 * T)).mp hr
  have hBRscaled := mul_le_mul_of_nonneg_left hBR hT.le
  change T * B ≤ T * (R + r) at hBRscaled
  have hRscaled := mul_le_mul_of_nonneg_left hRhalf hT.le
  nlinarith only [hBscaled, hrscaled, hBRscaled, hRscaled, hLd, hh]

/-- Once t q<1, the entropy equation forces the sharper scale lower bound d≥T. -/
theorem heavy_scale_ge_log_sample {h T L u : ℝ} (hL : 0 < L) (hL1 : L < 1)
    (hu : 0 < u) (hu1 : u < 1)
    (he : h / L = T - Real.log u + entropyTailCorrection L) : T ≤ h / L := by
  have hlog := Real.log_neg hu hu1
  have hA := (entropyTailCorrection_bounds L hL hL1).1
  linarith only [he, hlog, hA]

/-- The scalar entropy gap gives the sharp +2 lower bound, with an explicit uniform error. -/
theorem heavy_scalar_gap_strong (h T L u : ℝ) (hh : 0 < h) (hT : 0 < T)
    (hL : 0 < L) (hL1 : L < 1) (hu : 0 < u) (hu1 : u < 1)
    (he : h / L = T - Real.log u + entropyTailCorrection L) :
    T + Real.log T + 2 + scalarGap (T * u) - 2 * h / T ≤ (h / L) * Real.exp u := by
  have hd := heavy_scale_ge_log_sample hL hL1 hu hu1 he
  have hLb : L ≤ h / T := by
    apply (le_div_iff₀ hT).mpr
    have hb := (le_div_iff₀ hL).mp hd
    nlinarith only [hb]
  have hA := entropyTailCorrection_sub_one_bound L hL hL1
  have hAlow : 1 - 2 * h / T ≤ entropyTailCorrection L := by
    have ha := neg_abs_le (entropyTailCorrection L - 1)
    have hb : 2 * L ≤ 2 * h / T := by
      convert mul_le_mul_of_nonneg_left hLb (by norm_num : (0 : ℝ) ≤ 2) using 1
      ring
    linarith only [hA, ha, hb]
  have hexp := Real.add_one_le_exp u
  have hdp : 0 < h / L := div_pos hh hL
  have hmexp := mul_le_mul_of_nonneg_left hexp hdp.le
  have hmdu := mul_le_mul_of_nonneg_right hd hu.le
  unfold scalarGap
  rw [Real.log_mul (ne_of_gt hT) (ne_of_gt hu)]
  nlinarith only [he, hAlow, hmexp, hmdu]

/-- The full reciprocal lower bound once the common optimizer thresholds hold. -/
theorem heavy_competitive_reciprocal_lower_strong (h T L u B r : ℝ)
    (hh : 0 < h) (hT : 0 < T) (hL : 0 < L) (hL1 : L < 1) (hu : 0 < u)
    (he : h / L = T - Real.log u + entropyTailCorrection L)
    (hBpos : 0 < B) (hBlow : h / (3 * T) ≤ B) (hBup : h / B ≤ 5 * T / 4)
    (hr0 : 0 ≤ r) (hr : r ≤ h / (12 * T)) (hr3 : r ≤ h / (36 * T ^ 3))
    (hBR : B ≤ L * Real.exp (-u) + r) (hlog : Real.log (6 * T / h) ≤ T / 4) :
    u < 1 ∧ T ≤ h / L ∧ T + Real.log T + 2 + scalarGap (T * u) - (2 * h + 1) / T ≤ h / B := by
  have hu1 := heavy_competitive_scaled_atom_lt_one h T L u B r hh hT hL hL1 hu
    he hBpos hBlow hBup hr hBR hlog
  have hd := heavy_scale_ge_log_sample hL hL1 hu hu1 he
  have hgap := heavy_scalar_gap_strong h T L u hh hT hL hL1 hu hu1 he
  let R := L * Real.exp (-u)
  have hRlow : h / (6 * T) ≤ R := by
    change B ≤ R + r at hBR
    have h0 : h / (3 * T) - h / (12 * T) ≥ h / (6 * T) := by
      field_simp
      nlinarith only [hh]
    linarith only [hBlow, hBR, hr, h0]
  have hBweak : h / (6 * T) ≤ B := by
    apply le_trans _ hBlow
    apply div_le_div_of_nonneg_left hh.le (by positivity)
    linarith
  have hpert := reciprocal_perturbation_bound hh.le (by positivity : 0 < h / (6 * T))
    hBweak hRlow hr0 hBR
  have herr : h * r / (h / (6 * T)) ^ 2 ≤ 1 / T := by
    have hm := mul_le_mul_of_nonneg_left hr3
      (by positivity : 0 ≤ h / (h / (6 * T)) ^ 2)
    convert hm using 1 <;> field_simp
    ring
  have hid : h / R = (h / L) * Real.exp u := by
    dsimp [R]
    rw [Real.exp_neg]
    field_simp
  rw [hid] at hpert
  refine ⟨hu1, hd, ?_⟩
  have hn : (2 * h + 1) / T = 2 * h / T + 1 / T := by ring
  rw [hn]
  linarith only [hgap, hpert, herr]

end
end EntropyConstrainedMissingMass
