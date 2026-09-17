import EntropyConstrainedMissingMass.AsymptoticOptimizerBounds

/-! Common eventual thresholds, independent of the choice of maximizing candidate. -/

open Filter Set
open scoped Topology
namespace EntropyConstrainedMissingMass

/-- Powers of log t times a fixed geometric tail tend to zero. -/
theorem tendsto_log_pow_mul_geometric (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun t : ℕ => (Real.log t) ^ k * r ^ t) atTop (𝓝 0) := by
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hlim := (summable_pow_mul_geometric_of_norm_lt_one k hrnorm).tendsto_atTop_zero
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht)
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    have htp : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlog : 0 ≤ Real.log t := Real.log_nonneg (by exact_mod_cast ht)
    have hlogle : Real.log t ≤ (t : ℝ) :=
      (Real.log_le_sub_one_of_pos htp).trans (by linarith)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog hlogle k) (pow_nonneg hr0 t)

/-- Explicit inverse-logarithmic control of a geometric tail. -/
theorem geometric_eventually_le_inverse_log_pow (k : ℕ) {r c : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 < c) :
    ∀ᶠ t : ℕ in atTop, r ^ t ≤ c / (Real.log t) ^ k := by
  have hs := (tendsto_log_pow_mul_geometric k hr0 hr1).eventually_lt_const hc
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs, hT.eventually_gt_atTop 0] with t ht hT
  apply (le_div_iff₀ (pow_pos hT k)).mpr
  nlinarith only [ht]

/-- The logarithmic bound needed for the uniform competitive-block bootstrap. -/
theorem log_scaled_eventually_le_quarter (h : ℝ) (hh : 0 < h) :
    ∀ᶠ T : ℝ in atTop, Real.log (6 * T / h) ≤ T / 4 := by
  filter_upwards [Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1 / 8),
    eventually_ge_atTop (8 * |Real.log (6 / h)|), eventually_ge_atTop (1 : ℝ)] with T hsmall hlarge hT
  have hTp : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_pos hTp, id_eq] at hsmall
  have heq : 6 * T / h = (6 / h) * T := by ring
  rw [heq, Real.log_mul (ne_of_gt (div_pos (by norm_num) hh)) (ne_of_gt hTp)]
  linarith [le_abs_self (Real.log (6 / h))]

/-- A fixed coarse version of the sharp reciprocal upper bound. -/
theorem asymptotic_reciprocal_upper_five_quarters (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, h / optimalValue t h ≤ 5 * Real.log t / 4 := by
  obtain ⟨C, hC, he⟩ := asymptotic_reciprocal_upper h hh
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlittle := (Real.isLittleO_log_id_atTop.def (by positivity : 0 < 1 / (4 * (C + 3)))).filter_mono hT
  change ∀ᶠ t : ℕ in atTop, _ at hlittle
  filter_upwards [he, hlittle, hT.eventually_ge_atTop (Real.exp 1), hT.eventually_ge_atTop 1]
    with t he hlittle hTe hT1
  have hTp : 0 < Real.log t := by linarith
  have hlog : 1 ≤ Real.log (Real.log t) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hTe
  have hlogp : 0 < Real.log (Real.log t) := by linarith
  simp only [Real.norm_eq_abs, abs_of_pos hTp, abs_of_pos hlogp, id_eq] at hlittle
  have hscaled : (C + 3) * Real.log (Real.log t) ≤ Real.log t / 4 := by
    have hm := mul_le_mul_of_nonneg_left hlittle (by positivity : 0 ≤ C + 3)
    convert hm using 1
    field_simp
  have hratio : Real.log (Real.log t) / Real.log t ≤ Real.log (Real.log t) :=
    div_le_self hlogp.le hT1
  have hmul := mul_le_mul_of_nonneg_left hratio hC.le
  nlinarith only [he.2, hscaled, hmul, hlog]

end EntropyConstrainedMissingMass
