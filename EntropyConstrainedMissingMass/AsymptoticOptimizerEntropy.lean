import EntropyConstrainedMissingMass.AsymptoticOptimizerUniform

/-! A uniform explicit error bound for the optimizer entropy identity eq:optimizer-d. -/
open Filter Set
open scoped Topology
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The source's O_h(1/log t) entropy remainder, uniformly over all maximizing roots. -/
theorem optimalHeavy_entropy_remainder_uniform (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      |h / (1 - z) - (Real.log t - Real.log ((t : ℝ) * ((1 - z) / m)) + 1)|
        ≤ 2 * h / Real.log t := by
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [optimalHeavy_eventually_estimates h hh, hT.eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with t ht hlog ht1
  intro m z hp
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hp.multiplicity_pos
  have hord := heavy_parameter_mass_order hm hp.root_mem
  have hL : 0 < 1 - z := sub_pos.mpr hp.root_mem.2
  have hL1 : 1 - z < 1 := by linarith [hord.1.trans hord.2]
  have he := heavy_scaled_entropy t m (1 - z) h
    (Nat.cast_pos.mpr (by omega : 0 < t)) hm hL hh
    (by simpa only [sub_sub_cancel] using hp.entropy_eq)
  have hbound := entropyTailCorrection_sub_one_bound (1 - z) hL hL1
  have hscale := (ht m z hp).2.1
  have hLbound : (1 - z) * Real.log t ≤ h := by simpa only [mul_comm] using (le_div_iff₀ hL).mp hscale
  rw [he]
  have heq : Real.log t - Real.log ((t : ℝ) * ((1 - z) / m)) + entropyTailCorrection (1-z) -
      (Real.log t - Real.log ((t : ℝ) * ((1 - z) / m)) + 1) = entropyTailCorrection (1-z) - 1 := by ring
  rw [heq]
  exact hbound.trans ((le_div_iff₀ hlog).mpr (by nlinarith only [hLbound]))

/-- The literal uniform reciprocal perturbation in eq:reciprocal-uniform, with an explicit constant. -/
theorem optimalHeavy_reciprocal_perturbation_uniform (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      (h / (1 - z)) * Real.exp ((t : ℝ) * ((1 - z) / m)) - h / optimalValue t h
        ≤ (36 / h) * (Real.log t) ^ 2 * (1 - Real.exp (-h)) ^ t := by
  let ρ := 1 - Real.exp (-h)
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith [Real.exp_lt_one_iff.mpr (by linarith : -h < 0)]
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [Real.exp_pos (-h)]
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htail := geometric_eventually_le_inverse_log_pow 1 hρ0.le hρ1
    (by positivity : 0 < h / 12)
  filter_upwards [asymptotic_value_lower h hh, htail, hT.eventually_gt_atTop 0]
    with t hB htail hlog
  intro m z hp
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hp.multiplicity_pos
  have hord := heavy_parameter_mass_order hm hp.root_mem
  have hL : 0 < 1 - z := sub_pos.mpr hp.root_mem.2
  have hLρ : 1 - z ≤ ρ := by
    have := heavy_entropy_largest_atom_bound hm hp.root_mem hp.entropy_eq
    dsimp [ρ]; linarith only [this]
  have hBR : optimalValue t h ≤
      (1 - z) * Real.exp (-((t : ℝ) * ((1 - z) / m))) + ρ ^ t := by
    have hlight := mul_le_mul_of_nonneg_left
      (light_block_le_exp t hord.1.le (hord.2.le.trans hp.root_mem.2.le)) hL.le
    have hpwρ := pow_le_pow_left₀ hL.le hLρ t
    have hzm := mul_le_mul_of_nonneg_right hp.root_mem.2.le (pow_nonneg hL.le t)
    rw [← hp.objective_eq, branchObjective]
    linarith only [hlight, hpwρ, hzm]
  have hr : ρ ^ t ≤ h / (12 * Real.log t) := by
    simpa only [pow_one, div_div] using htail
  have hRlow : h / (6 * Real.log t) ≤
      (1 - z) * Real.exp (-((t : ℝ) * ((1 - z) / m))) := by
    have h0 : h / (6 * Real.log t) ≤ h / (3 * Real.log t) - h / (12 * Real.log t) := by
      field_simp
      nlinarith only [hh]
    linarith only [h0, hB.2, hBR, hr]
  have hBweak : h / (6 * Real.log t) ≤ optimalValue t h := by
    apply le_trans _ hB.2
    apply div_le_div_of_nonneg_left hh.le (by positivity)
    linarith
  have hpert := reciprocal_perturbation_bound hh.le
    (by positivity : 0 < h / (6 * Real.log t)) hBweak hRlow (pow_nonneg hρ0.le t) hBR
  have hid : h / ((1 - z) * Real.exp (-((t : ℝ) * ((1 - z) / m)))) =
      (h / (1 - z)) * Real.exp ((t : ℝ) * ((1 - z) / m)) := by
    rw [Real.exp_neg]
    field_simp
  rw [hid] at hpert
  convert hpert using 1
  dsimp [ρ]
  field_simp
  ring

/-- The displayed explicit reciprocal error is o(1/log t), independently of the optimizer. -/
theorem optimalHeavy_reciprocal_error_tendsto (h : ℝ) (hh : 0 < h) :
    Tendsto (fun t : ℕ => ((36 / h) * (Real.log t) ^ 2 * (1 - Real.exp (-h)) ^ t) * Real.log t)
      atTop (𝓝 0) := by
  have hρ0 : 0 ≤ 1 - Real.exp (-h) := by linarith [Real.exp_lt_one_iff.mpr (by linarith : -h < 0)]
  have hρ1 : 1 - Real.exp (-h) < 1 := by linarith [Real.exp_pos (-h)]
  have ht := (tendsto_log_pow_mul_geometric 3 hρ0 hρ1).const_mul (36 / h)
  convert ht using 1
  · ext t; ring
  · simp

end
end EntropyConstrainedMissingMass
