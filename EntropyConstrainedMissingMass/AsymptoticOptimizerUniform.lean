import EntropyConstrainedMissingMass.AsymptoticThresholds

/-! Optimizer-independent thresholds for all heavy maximizing candidates. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- An actual entropy-matched heavy candidate whose value equals the global value. -/
structure OptimalHeavyParameters (t : ℕ) (h : ℝ) (m : ℕ) (z : ℝ) : Prop where
  multiplicity_pos : 0 < m
  root_mem : z ∈ Ioo (1 / ((m : ℝ) + 1)) 1
  entropy_eq : branchEntropy m z = h
  objective_eq : branchObjective m t z = optimalValue t h

/-- The same eventual threshold works for every choice of maximizing parameters. -/
theorem optimalHeavy_eventually_estimates (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      (t : ℝ) * ((1 - z) / m) < 1 ∧
      Real.log t ≤ h / (1 - z) ∧
      Real.log t + Real.log (Real.log t) + 2 +
        scalarGap (Real.log t * ((t : ℝ) * ((1 - z) / m))) - (2 * h + 1) / Real.log t
          ≤ h / optimalValue t h := by
  let ρ := 1 - Real.exp (-h)
  have hρ0 : 0 < ρ := by dsimp [ρ]; have he := Real.exp_lt_one_iff.mpr (by linarith : -h < 0); linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [Real.exp_pos (-h)]
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := (log_scaled_eventually_le_quarter h hh).filter_mono hT
  change ∀ᶠ t : ℕ in atTop, _ at hlog
  have hr1 := geometric_eventually_le_inverse_log_pow 1 hρ0.le hρ1
    (by positivity : 0 < h / 12)
  have hr3 := geometric_eventually_le_inverse_log_pow 3 hρ0.le hρ1
    (by positivity : 0 < h / 36)
  filter_upwards [asymptotic_value_lower h hh, asymptotic_reciprocal_upper_five_quarters h hh,
    hr1, hr3, hlog, hT.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)]
    with t hB hBup hr1 hr3 hlog hTp ht
  intro m z hp
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hp.multiplicity_pos
  have hpar := heavy_parameter_mass_order hm hp.root_mem
  have hzpos : 0 < z := hpar.1.trans hpar.2
  have hL : 0 < 1 - z := sub_pos.mpr hp.root_mem.2
  have hL1 : 1 - z < 1 := by linarith
  have htz : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hu : 0 < (t : ℝ) * ((1 - z) / m) := mul_pos htz hpar.1
  have he : h / (1 - z) = Real.log t - Real.log ((t : ℝ) * ((1 - z) / m)) +
      entropyTailCorrection (1 - z) := by
    apply heavy_scaled_entropy (t : ℝ) m (1 - z) h htz hm hL hh
    simpa only [sub_sub_cancel] using hp.entropy_eq
  have hLρ : 1 - z ≤ ρ := by
    have hbound := heavy_entropy_largest_atom_bound hm hp.root_mem hp.entropy_eq
    dsimp [ρ]
    linarith only [hbound]
  have hBR : optimalValue t h ≤ (1 - z) * Real.exp (-((t : ℝ) * ((1 - z) / m))) + ρ ^ t := by
    have hpw := light_block_le_exp t hpar.1.le (hpar.2.le.trans hp.root_mem.2.le)
    have hlight := mul_le_mul_of_nonneg_left hpw hL.le
    have hheavy : z * (1 - z) ^ t ≤ ρ ^ t := by
      have hpwρ := pow_le_pow_left₀ hL.le hLρ t
      have hzm := mul_le_mul_of_nonneg_right hp.root_mem.2.le (pow_nonneg hL.le t)
      nlinarith only [hpwρ, hzm]
    rw [← hp.objective_eq, branchObjective]
    linarith only [hlight, hheavy]
  have hr1' : ρ ^ t ≤ h / (12 * Real.log t) := by
    simpa only [pow_one, div_div] using hr1
  have hr3' : ρ ^ t ≤ h / (36 * Real.log t ^ 3) := by simpa only [div_div] using hr3
  exact heavy_competitive_reciprocal_lower_strong h (Real.log t) (1 - z)
    ((t : ℝ) * ((1 - z) / m)) (optimalValue t h) (ρ ^ t)
    hh hTp hL hL1 hu he hB.1 hB.2 hBup (pow_nonneg hρ0.le t) hr1' hr3' hBR hlog

/-- Every sufficiently large sample size admits maximizing heavy parameters. -/
theorem optimalHeavy_eventually_exists (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop, ∃ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z := by
  filter_upwards [ProbabilityVector.globalMax_eventually_heavy (ι := ℕ) h hh] with t ht
  obtain ⟨p, hp, hmax⟩ := ProbabilityVector.exists_global_maximizer (ι := ℕ) t h hh.le
  obtain ⟨m, z, hm, hz, e, _, hroot, he, hrep⟩ := ht p hp hmax
  refine ⟨m, z, hm, hroot, he, ?_⟩
  have hobj := optimalValue_eq_of_globalMax p t hp hmax
  rw [hrep, ProbabilityVector.objective_zeroExtend, objective_candidateVector] at hobj
  exact hobj.symm

/-- The sharp reciprocal lower bound for the genuine optimal value. -/
theorem asymptotic_reciprocal_lower (h : ℝ) (hh : 0 < h) :
    ∀ᶠ t : ℕ in atTop,
      Real.log t + Real.log (Real.log t) + 2 - (2 * h + 1) / Real.log t ≤ h / optimalValue t h := by
  filter_upwards [optimalHeavy_eventually_estimates h hh, optimalHeavy_eventually_exists h hh,
    eventually_ge_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with t ht hex ht1 hlog
  obtain ⟨m, z, hp⟩ := hex
  have hbound := (ht m z hp).2.2
  have hpar := heavy_parameter_mass_order (Nat.cast_pos.mpr hp.multiplicity_pos) hp.root_mem
  have hv : 0 < Real.log t * ((t : ℝ) * ((1 - z) / m)) :=
    mul_pos hlog (mul_pos (Nat.cast_pos.mpr (by omega)) hpar.1)
  have hgap : 0 ≤ scalarGap (Real.log t * ((t : ℝ) * ((1 - z) / m))) := by
    have hl := Real.log_le_sub_one_of_pos hv
    unfold scalarGap
    linarith
  linarith only [hbound, hgap]

/-- The full sharp value asymptotic, with the paper's error scale along integer samples. -/
theorem optimalValue_sharp_asymptotic (h : ℝ) (hh : 0 < h) :
    (fun t : ℕ => h / optimalValue t h - (Real.log t + Real.log (Real.log t) + 2))
      =O[atTop] (fun t => Real.log (Real.log t) / Real.log t) := by
  obtain ⟨C, hC, hu⟩ := asymptotic_reciprocal_upper h hh
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C + 2 * h + 1, ?_⟩
  filter_upwards [hu, asymptotic_reciprocal_lower h hh, hT.eventually_ge_atTop (Real.exp 1)]
    with t hu hl hlarge
  have hTp : 0 < Real.log t := (Real.exp_pos 1).trans_le hlarge
  have hlog : 1 ≤ Real.log (Real.log t) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlarge
  have hratio : 0 ≤ Real.log (Real.log t) / Real.log t := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hratio]
  apply abs_le.mpr
  constructor
  · have he : (2 * h + 1) / Real.log t ≤ (C + 2 * h + 1) *
        (Real.log (Real.log t) / Real.log t) := by
      apply (div_le_iff₀ hTp).mpr
      have hid : (C + 2 * h + 1) * (Real.log (Real.log t) / Real.log t) * Real.log t =
          (C + 2 * h + 1) * Real.log (Real.log t) := by field_simp
      rw [hid]
      nlinarith only [mul_nonneg (by positivity : 0 ≤ C + 2 * h + 1) (sub_nonneg.mpr hlog), hC]
    linarith only [hl, he]
  · have he := mul_le_mul_of_nonneg_right (show C ≤ C + 2 * h + 1 by linarith) hratio
    linarith only [hu.2, he]

end
end EntropyConstrainedMissingMass
