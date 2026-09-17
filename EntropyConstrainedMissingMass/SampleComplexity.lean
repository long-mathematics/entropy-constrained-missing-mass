import EntropyConstrainedMissingMass.AsymptoticOptimizerUniform
import EntropyConstrainedMissingMass.SampleMonotonicity

/-! Inversion of the sharp missing-mass asymptotic at the actual integer hitting time. -/
open Filter Set
open scoped Topology Asymptotics
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The sharp reciprocal error tends to zero, not merely to a bounded interval. -/
theorem tendsto_optimalValue_reciprocal_error {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℕ => h/optimalValue t h-(Real.log t+Real.log (Real.log t)+2)) atTop (𝓝 0) :=
  (optimalValue_sharp_asymptotic h hh).trans_tendsto
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem tendsto_optimalValue_reciprocal_ratio {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℕ => (h/optimalValue t h)/Real.log t) atTop (𝓝 1) := by
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hT
  have hconst := hT.const_div_atTop 2
  have herr := (tendsto_optimalValue_reciprocal_error hh).div_atTop hT
  have hsum := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hlog).add hconst).add herr
  have he : (fun t : ℕ => (h/optimalValue t h)/Real.log t) =ᶠ[atTop]
      (fun t => 1 + Real.log (Real.log t)/Real.log t + 2/Real.log t +
        (h/optimalValue t h-(Real.log t+Real.log (Real.log t)+2))/Real.log t) := by
    filter_upwards [hT.eventually_gt_atTop 0] with t ht
    field_simp
    ring
  apply (show Tendsto (fun t : ℕ => 1 + Real.log (Real.log t)/Real.log t + 2/Real.log t +
      (h/optimalValue t h-(Real.log t+Real.log (Real.log t)+2))/Real.log t) atTop (𝓝 1) by
        simpa using hsum).congr'
  filter_upwards [he] with t ht
  exact ht.symm

theorem tendsto_optimalValue_reciprocal_atTop {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℕ => h/optimalValue t h) atTop atTop := by
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hm := hT.atTop_mul_pos (by norm_num : (0 : ℝ)<1) (tendsto_optimalValue_reciprocal_ratio hh)
  apply hm.congr'
  filter_upwards [hT.eventually_gt_atTop 0] with t ht
  field_simp

theorem tendsto_optimalValue_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℕ => optimalValue t h) atTop (𝓝 0) := by
  have hd := (tendsto_optimalValue_reciprocal_atTop hh).const_div_atTop h
  apply hd.congr'
  filter_upwards [] with t
  field_simp [hh.ne']

theorem exists_sample_bound {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    ∃ t : ℕ, optimalValue t h ≤ ε := by
  obtain ⟨t,ht⟩ := ((tendsto_optimalValue_zero hh).eventually (Iio_mem_nhds hε)).exists
  exact ⟨t,ht.le⟩

/-- The actual least integer sample size attaining the prescribed tolerance. -/
def sampleComplexity (h ε : ℝ) : ℕ := by
  classical
  exact if he : ∃ t : ℕ, optimalValue t h ≤ ε then Nat.find he else 0

theorem sampleComplexity_spec {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    optimalValue (sampleComplexity h ε) h ≤ ε := by
  classical
  have he := exists_sample_bound hh hε
  simp only [sampleComplexity,dite_eq_left he]
  exact Nat.find_spec he

theorem lt_optimalValue_of_lt_sampleComplexity {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    {t : ℕ} (ht : t < sampleComplexity h ε) : ε < optimalValue t h := by
  classical
  have he := exists_sample_bound hh hε
  simp only [sampleComplexity,dite_eq_left he] at ht
  exact lt_of_not_ge (Nat.find_min he ht)

theorem tendsto_sampleComplexity_atTop {h : ℝ} (hh : 0 < h) :
    Tendsto (sampleComplexity h) (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < optimalValue b h :=
    (eventually_lt_nhds (optimalValue_pos b hh)).filter_mono nhdsWithin_le_nhds
  filter_upwards [he,self_mem_nhdsWithin] with ε hε hεpos
  have hs := sampleComplexity_spec hh hεpos
  by_contra hnot
  have hN : sampleComplexity h ε ≤ b := by omega
  have hle := (strictAnti_optimalValue hh).antitone hN
  linarith

/-- The continuous inverse scale of `log t + log log t + 2`. -/
def sampleInverseScale (a : ℝ) : ℝ := Real.exp a / (Real.exp 2*a)

theorem tendsto_sampleInverseScale_reciprocal {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℕ => sampleInverseScale (h/optimalValue t h)/(t : ℝ)) atTop (𝓝 1) := by
  let r := fun t : ℕ => h/optimalValue t h-(Real.log t+Real.log (Real.log t)+2)
  have hr : Tendsto r atTop (𝓝 0) := tendsto_optimalValue_reciprocal_error hh
  have he := Real.continuous_exp.continuousAt.tendsto.comp hr
  have hratio := (tendsto_optimalValue_reciprocal_ratio hh).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hlim : Tendsto (fun t : ℕ => ((h/optimalValue t h)/Real.log t)⁻¹*Real.exp (r t)) atTop (𝓝 1) := by
    simpa using hratio.mul he
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with t ht
  have ht0 : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hT : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  have hA : 0 < h/optimalValue t h := div_pos hh (optimalValue_pos t hh)
  have ha : h/optimalValue t h = Real.log t+Real.log (Real.log t)+2+r t := by dsimp [r]; ring
  unfold sampleInverseScale
  rw [ha,Real.exp_add,Real.exp_add,Real.exp_add,Real.exp_log hT,Real.exp_log ht0]
  rw [← ha]
  field_simp [hT.ne',ht0.ne',hA.ne']

theorem hasDerivAt_sampleInverseScale {a : ℝ} (ha : a ≠ 0) :
    HasDerivAt sampleInverseScale (Real.exp a*(a-1)/(Real.exp 2*a^2)) a := by
  have hd := (Real.hasDerivAt_exp a).div ((hasDerivAt_id a).const_mul (Real.exp 2))
    (mul_ne_zero (Real.exp_ne_zero _) ha)
  convert hd using 1
  · rfl
  · simp only [id_eq]
    field_simp

theorem strictMonoOn_sampleInverseScale : StrictMonoOn sampleInverseScale (Ioi (1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _) _
  · intro a ha
    rw [interior_Ioi] at ha
    have hap : 0 < a := lt_trans zero_lt_one ha
    rw [(hasDerivAt_sampleInverseScale (ne_of_gt (lt_trans zero_lt_one ha))).deriv]
    exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr ha))
      (mul_pos (Real.exp_pos _) (sq_pos_of_pos hap))
  · intro a ha
    exact (hasDerivAt_sampleInverseScale (ne_of_gt (lt_trans zero_lt_one ha))).continuousAt.continuousWithinAt

private theorem tendsto_nat_pred_ratio :
    Tendsto (fun n : ℕ => ((n-1 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 1
  have he := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hi
  apply (show Tendsto (fun n : ℕ => 1-1/(n : ℝ)) atTop (𝓝 1) by simpa using he).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Nat.cast_sub hn,Nat.cast_one]
  field_simp

/-- The transformed reciprocal threshold is trapped between adjacent sample sizes.
This handles integer rounding in the definition of the minimum. -/
theorem tendsto_inverseScale_at_sampleComplexity {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ε : ℝ => sampleInverseScale (h/ε)/(sampleComplexity h ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  let N := sampleComplexity h
  have hN : Tendsto N (𝓝[>] (0 : ℝ)) atTop := tendsto_sampleComplexity_atTop hh
  have hP : Tendsto (fun ε => N ε-1) (𝓝[>] (0 : ℝ)) atTop := (tendsto_sub_atTop_nat 1).comp hN
  have hU := (tendsto_sampleInverseScale_reciprocal hh).comp hN
  have hL₁ := (tendsto_sampleInverseScale_reciprocal hh).comp hP
  have hL₂ := tendsto_nat_pred_ratio.comp hN
  have hL : Tendsto (fun ε => sampleInverseScale (h/optimalValue (N ε-1) h)/(N ε : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hl : Tendsto (fun ε => (sampleInverseScale (h/optimalValue (N ε-1) h)/((N ε-1 : ℕ) : ℝ))*
        (((N ε-1 : ℕ) : ℝ)/(N ε : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by simpa using hL₁.mul hL₂
    apply hl.congr'
    filter_upwards [hN.eventually_ge_atTop 2] with ε hε
    have hp : ((N ε-1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sampleInverseScale (h/optimalValue (N ε-1) h)/(N ε : ℝ) ≤ sampleInverseScale (h/ε)/(N ε : ℝ) ∧
      sampleInverseScale (h/ε)/(N ε : ℝ) ≤ sampleInverseScale (h/optimalValue (N ε) h)/(N ε : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,hN.eventually_ge_atTop 2,
      ((tendsto_optimalValue_reciprocal_atTop hh).comp hP).eventually_gt_atTop 1]
      with ε hε hN2 hA1
    have hε0 : 0 < ε := hε
    have hNM : N ε-1 < N ε := by omega
    have hprev := lt_optimalValue_of_lt_sampleComplexity hh hε0 hNM
    have hnext := sampleComplexity_spec hh hε0
    have hlt : h/optimalValue (N ε-1) h < h/ε := div_lt_div_of_pos_left hh hε0 hprev
    have hle : h/ε ≤ h/optimalValue (N ε) h :=
      div_le_div_of_nonneg_left hh.le (optimalValue_pos _ hh) hnext
    have hA : 1 < h/ε := hA1.trans hlt
    have hNpos : 0 ≤ (N ε : ℝ) := Nat.cast_nonneg _
    constructor
    · exact div_le_div_of_nonneg_right
        (strictMonoOn_sampleInverseScale.monotoneOn hA1 hA hlt.le) hNpos
    · exact div_le_div_of_nonneg_right
        (strictMonoOn_sampleInverseScale.monotoneOn hA (hA.trans_le hle) hle) hNpos
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU (hb.mono fun _ he => he.1) (hb.mono fun _ he => he.2)

/-- Manuscript sample-complexity asymptotic, expressed as convergence of the ratio to one. -/
theorem sampleComplexity_asymptotic_ratio {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ε : ℝ => (sampleComplexity h ε : ℝ) /
      (ε/(Real.exp 2*h)*Real.exp (h/ε))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hi := (tendsto_inverseScale_at_sampleComplexity hh).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply (show Tendsto (fun ε : ℝ => (sampleInverseScale (h/ε)/(sampleComplexity h ε : ℝ))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) by simpa using hi).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := (show 0 < ε from hε).ne'
  unfold sampleInverseScale
  field_simp

/-- The same conclusion in the standard asymptotic-equivalence notation. -/
theorem sampleComplexity_asymptotic {h : ℝ} (hh : 0 < h) :
    (fun ε : ℝ => (sampleComplexity h ε : ℝ)) ~[𝓝[>] (0 : ℝ)]
      (fun ε => ε/(Real.exp 2*h)*Real.exp (h/ε)) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · exact sampleComplexity_asymptotic_ratio hh
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (mul_pos (div_pos hε (mul_pos (Real.exp_pos _) hh)) (Real.exp_pos _)).ne'

end
end EntropyConstrainedMissingMass
