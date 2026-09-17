import EntropyConstrainedMissingMass.AsymptoticRounded
import EntropyConstrainedMissingMass.FiniteClassification

/-! A sharp reciprocal upper bound from the actual rounded heavy candidate.
Bernoulli's inequality suffices and avoids introducing an exponential approximation. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- Bernoulli gives the sharp constant term, with an explicit error bounded by 2/d. -/
theorem reciprocal_upper_of_heavy_candidate (t : ℕ) (h m L B : ℝ)
    (hh : 0 < h) (hm : 1 ≤ m) (hL : 0 < L) (hL1 : L < 1)
    (hmt : h * (t : ℝ) ≤ m) (hd : 2 ≤ h / L)
    (hB : branchObjective m t (1 - L) ≤ B) :
    0 < B ∧ h / B ≤ h / L + 1 + 2 / (h / L) := by
  have hmpos : 0 < m := by linarith
  have hLH : 2 * L ≤ h := (le_div_iff₀ hL).mp hd
  have hgap : 0 < h - L := by linarith
  have hq : L / m < 1 := (div_lt_one hmpos).mpr (hL1.trans_le hm)
  have htq : (t : ℝ) * (L / m) ≤ L / h := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hmpos hh).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hmt hL.le]
  have hbern : 1 - (t : ℝ) * (L / m) ≤ (1 - L / m) ^ t := by
    simpa only [mul_neg, sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -(L / m)) (by linarith : -2 ≤ -(L / m)) t)
  have hlower : L * (1 - L / h) ≤ B := by
    rw [heavy_tail_objective] at hB
    have hpos : 0 ≤ (1 - L) * L ^ t := by positivity
    have hh1 := mul_le_mul_of_nonneg_left hbern hL.le
    have hh2 := mul_le_mul_of_nonneg_left (sub_le_sub_left htq 1) hL.le
    nlinarith only [hB, hpos, hh1, hh2]
  have hbase : 0 < L * (1 - L / h) := by
    apply mul_pos hL
    exact sub_pos.mpr ((div_lt_one hh).mpr (by linarith))
  have hBpos := hbase.trans_le hlower
  refine ⟨hBpos, ?_⟩
  have hdiv := div_le_div_of_nonneg_left hh.le hbase hlower
  have hid : h / (L * (1 - L / h)) = h / L + 1 + L / (h - L) := by
    field_simp
    ring
  have hlast : L / (h - L) ≤ 2 / (h / L) := by
    have heq : 2 / (h / L) = 2 * L / h := by field_simp
    rw [heq]
    apply (div_le_div_iff₀ hgap hh).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hLH hL.le]
  rw [hid] at hdiv
  linarith only [hdiv, hlast]

/-- The actual rounded probability vector yields the reciprocal bound, eventually in natural t. -/
theorem rounded_reciprocal_upper (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, 0 < optimalValue t h ∧
      h / optimalValue t h ≤ roundedEntropyScale h t + 1 + 2 / roundedEntropyScale h t := by
  have hs := (roundedTailMass_eventually_spec h hh).filter_mono
    (show Filter.map (fun t : ℕ => (t : ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  have hd := (rounded_entropy_residual h hh).1.filter_mono
    (show Filter.map (fun t : ℕ => (t : ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ t : ℕ in atTop, _ at hs hd
  filter_upwards [hs, hd, eventually_ge_atTop (1 : ℕ)] with t hs hd ht
  let m := roundedMultiplicity h t
  let L := roundedTailMass h t
  have htpos : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmreal : 0 < (m : ℝ) := (mul_pos hh htpos).trans_le (Nat.le_ceil (h * t))
  have hm : 0 < m := Nat.cast_pos.mp hmreal
  have hz : 1 - L ∈ Icc 0 1 := ⟨by linarith [hs.2.1], by linarith [hs.1]⟩
  let p := natCandidateVector m (1 - L) hm hz
  have hp : p ∈ ProbabilityVector.Feasible h := natCandidateVector_feasible hm hz hs.2.2.le
  have hb := objective_le_optimalValue p t hp
  rw [objective_natCandidateVector] at hb
  exact reciprocal_upper_of_heavy_candidate t h m L (optimalValue t h) hh
    (by exact_mod_cast hm) hs.1 hs.2.1 (Nat.le_ceil _) hd hb

/-- An explicit eventual upper estimate with the paper's error scale and constant term +2. -/
theorem asymptotic_reciprocal_upper (h : ℝ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      0 < optimalValue t h ∧
      h / optimalValue t h ≤ Real.log t + Real.log (Real.log t) + 2 +
        C * (Real.log (Real.log t) / Real.log t) := by
  obtain ⟨C, hC, he⟩ := Asymptotics.isBigO_iff'.mp (rounded_entropy_scale_nat_expansion h hh)
  have hlo := (rounded_entropy_scale_log_lower h hh).filter_mono
    (show Filter.map (fun t : ℕ => (t : ℝ)) atTop ≤ atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ t : ℕ in atTop, _ at hlo
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨C + 4, by linarith, ?_⟩
  filter_upwards [rounded_reciprocal_upper h hh, he, hlo,
    hT.eventually_ge_atTop (Real.exp 1)] with t hu he hlo hlarge
  have hlog : 1 ≤ Real.log (Real.log t) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlarge
  have hTp : 0 < Real.log t := (Real.exp_pos 1).trans_le hlarge
  have hdp : 0 < roundedEntropyScale h t := (half_pos hTp).trans_le hlo
  have hratio : 0 < Real.log (Real.log t) / Real.log t := div_pos (by linarith) hTp
  simp only [Real.norm_eq_abs, abs_of_pos hratio] at he
  have hdub := (le_abs_self (roundedEntropyScale h t -
    (Real.log t + Real.log (Real.log t) + 1))).trans he
  have hsmall : 2 / roundedEntropyScale h t ≤ 4 * (Real.log (Real.log t) / Real.log t) := by
    have ha : 2 / roundedEntropyScale h t ≤ 2 / (Real.log t / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (half_pos hTp) hlo
    have hb : 2 / (Real.log t / 2) = 4 / Real.log t := by ring
    rw [hb] at ha
    have hc := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 / Real.log t)
    apply ha.trans
    convert hc using 1 <;> ring
  refine ⟨hu.1, ?_⟩
  nlinarith only [hu.2, hdub, hsmall]

end
end EntropyConstrainedMissingMass
