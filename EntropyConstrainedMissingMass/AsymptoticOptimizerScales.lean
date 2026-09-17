import EntropyConstrainedMissingMass.AsymptoticOptimizerUniform

/-! Uniform asymptotic scales for all heavy maximizing parameters, including all ties. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The rescaled light atom converges to one uniformly over all maximizing candidates. -/
theorem optimalHeavy_scaled_atom_uniform (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      |Real.log t * ((t : ℝ) * ((1 - z) / m)) - 1| < ε := by
  obtain ⟨δ, hδ, hcoerce⟩ := scalarGap_coercive ε hε
  obtain ⟨C, hC, hu⟩ := asymptotic_reciprocal_upper h hh
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto (fun t : ℕ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hT
  have hinv : Tendsto (fun t : ℕ => (2 * h + 1) / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hT
  have herror : Tendsto (fun t : ℕ => C * (Real.log (Real.log t) / Real.log t) +
      (2 * h + 1) / Real.log t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlogratio (a := C)).add hinv
  filter_upwards [optimalHeavy_eventually_estimates h hh, hu, herror.eventually_lt_const hδ,
    hT.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)] with t ht hu herr hlog ht1
  intro m z hp
  have hb := (ht m z hp).2.2
  have hgap : scalarGap (Real.log t * ((t : ℝ) * ((1 - z) / m))) < δ := by
    linarith only [hb, hu.2, herr]
  apply hcoerce _ _ hgap
  have hpar := heavy_parameter_mass_order (Nat.cast_pos.mpr hp.multiplicity_pos) hp.root_mem
  exact mul_pos hlog (mul_pos (Nat.cast_pos.mpr (by omega)) hpar.1)

private theorem tail_normalized_error {h T L E : ℝ} (hh : 0 < h) (hT : 0 < T) (hL : 0 < L)
    (hd : T ≤ h / L) (hE : h / L - T ≤ E) :
    |L * T / h - 1| ≤ E / T := by
  have hLT : L * T ≤ h := by
    have he := (le_div_iff₀ hL).mp hd
    nlinarith only [he]
  have hEp : 0 ≤ E := by linarith only [hd, hE]
  have hE' : h - T * L ≤ E * L := by
    have he := (div_le_iff₀ hL).mp (show h / L ≤ E + T by linarith only [hE])
    nlinarith only [he]
  have hmult := mul_le_mul_of_nonneg_right hE' hT.le
  have hmult' := mul_le_mul_of_nonneg_left hLT hEp
  have hfrac : L * T / h ≤ 1 := (div_le_one hh).mpr hLT
  rw [abs_of_nonpos (sub_nonpos.mpr hfrac)]
  have hid : -(L * T / h - 1) = (h - L * T) / h := by field_simp; ring
  rw [hid]
  apply (div_le_div_iff₀ hh hT).mpr
  nlinarith only [hmult, hmult']

/-- Total light mass has scale h/log t, uniformly in all maximizing parameters. -/
theorem optimalHeavy_tail_mass_uniform (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      |(1 - z) * Real.log t / h - 1| < ε := by
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto (fun t : ℕ => Real.log (Real.log t) / Real.log t) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hT
  have hinv : Tendsto (fun t : ℕ => (Real.log 2 + 1) / Real.log t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hT
  have herr : Tendsto (fun t : ℕ => (Real.log (Real.log t) + Real.log 2 + 1) / Real.log t)
      atTop (𝓝 0) := by
    convert hlogratio.add hinv using 1
    · funext t; ring
    · simp
  filter_upwards [optimalHeavy_eventually_estimates h hh,
    optimalHeavy_scaled_atom_uniform h hh (1 / 2) (by norm_num),
    herr.eventually_lt_const hε, hT.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)]
    with t ht hv herr hTp ht1
  intro m z hp
  have hpar := heavy_parameter_mass_order (Nat.cast_pos.mpr hp.multiplicity_pos) hp.root_mem
  have hL : 0 < 1 - z := sub_pos.mpr hp.root_mem.2
  have hL1 : 1 - z < 1 := by linarith [hpar.1.trans hpar.2]
  have hu : 0 < (t : ℝ) * ((1 - z) / m) :=
    mul_pos (Nat.cast_pos.mpr (by omega)) hpar.1
  have hscaled := hv m z hp
  have hvhalf : (1 / 2 : ℝ) ≤ Real.log t * ((t : ℝ) * ((1 - z) / m)) := by
    have hsmall := (abs_lt.mp hscaled).1
    linarith
  have hlogv := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hvhalf
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hloghalf, Real.log_mul (ne_of_gt hTp) (ne_of_gt hu)] at hlogv
  have hA := (entropyTailCorrection_bounds (1 - z) hL hL1).2
  have he := heavy_scaled_entropy (t : ℝ) m (1 - z) h
    (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr hp.multiplicity_pos) hL hh
    (by simpa only [sub_sub_cancel] using hp.entropy_eq)
  have hE : h / (1 - z) - Real.log t ≤ Real.log (Real.log t) + Real.log 2 + 1 := by
    linarith only [he, hlogv, hA]
  exact (tail_normalized_error hh hTp hL (ht m z hp).2.1 hE).trans_lt herr

/-- The number of light atoms has scale h t, uniformly over all maximizing candidates. -/
theorem optimalHeavy_multiplicity_uniform (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      |(m : ℝ) / (h * t) - 1| < ε := by
  have hT : Tendsto (fun t : ℕ => Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [optimalHeavy_tail_mass_uniform h hh (ε / 4) (by positivity),
    optimalHeavy_scaled_atom_uniform h hh (ε / 4) (by positivity),
    optimalHeavy_scaled_atom_uniform h hh (1 / 2) (by norm_num),
    hT.eventually_gt_atTop 0, eventually_ge_atTop (1 : ℕ)] with t hα hv hvhalf hTp ht1
  intro m z hp
  let α := (1 - z) * Real.log t / h
  let v := Real.log t * ((t : ℝ) * ((1 - z) / m))
  have hα' : |α - 1| < ε / 4 := hα m z hp
  have hv' : |v - 1| < ε / 4 := hv m z hp
  have hhalf : 1 / 2 < v := by
    have he := (abs_lt.mp (hvhalf m z hp)).1
    change -(1 / 2 : ℝ) < v - 1 at he
    linarith
  have hvp : 0 < v := by linarith
  have hL : 0 < 1 - z := sub_pos.mpr hp.root_mem.2
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hp.multiplicity_pos
  have htp : 0 < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hid : (m : ℝ) / (h * t) = α / v := by
    dsimp [α, v]
    field_simp
  rw [hid]
  have hsub : α / v - 1 = (α - v) / v := by field_simp
  rw [hsub, abs_div, abs_of_pos hvp]
  apply (div_lt_iff₀ hvp).mpr
  have htri := abs_sub_le α 1 v
  rw [abs_sub_comm 1 v] at htri
  have hmul := mul_lt_mul_of_pos_left hhalf hε
  nlinarith only [htri, hα', hv', hmul]

/-- All three manuscript scales, in explicit uniform epsilon form. -/
theorem optimizer_scales_uniform (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ (m : ℕ) (z : ℝ), OptimalHeavyParameters t h m z →
      |(1 - z) / (h / Real.log t) - 1| < ε ∧
      |((1 - z) / m) / (1 / ((t : ℝ) * Real.log t)) - 1| < ε ∧
      |(m : ℝ) / (h * t) - 1| < ε := by
  filter_upwards [optimalHeavy_tail_mass_uniform h hh ε hε,
    optimalHeavy_scaled_atom_uniform h hh ε hε, optimalHeavy_multiplicity_uniform h hh ε hε]
    with t hL hq hm
  intro m z hp
  refine ⟨?_, ?_, hm m z hp⟩
  · convert hL m z hp using 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    congr 1
    ring
  · convert hq m z hp using 1
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    congr 1
    ring

namespace ProbabilityVector
variable {ι : Type*}

/-- An actual heavy representation satisfying all three normalized scale estimates. -/
def HeavyScaleApproximation (t : ℕ) (h ε : ℝ) (p : ProbabilityVector ι) : Prop :=
  ∃ (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) (e : Fin (m + 1) ↪ ι),
    z ∈ Ioo (1 / ((m : ℝ) + 1)) 1 ∧
    p = zeroExtend e (candidateVector m z hm hz) ∧
    |(1 - z) / (h / Real.log t) - 1| < ε ∧
    |((1 - z) / m) / (1 / ((t : ℝ) * Real.log t)) - 1| < ε ∧
    |(m : ℝ) / (h * t) - 1| < ε

/-- Uniformity over the complete set of global maximizers, stated using actual laws. -/
theorem globalMax_optimizer_scales_uniform [Countable ι] [Infinite ι]
    (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ p : ProbabilityVector ι, p ∈ Feasible h →
      (∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) →
      HeavyScaleApproximation t h ε p := by
  filter_upwards [globalMax_eventually_heavy (ι := ι) h hh, optimizer_scales_uniform h hh ε hε]
    with t hheavy hscales
  intro p hp hmax
  obtain ⟨m, z, hm, hz, e, _, hroot, hentropy, hrep⟩ := hheavy p hp hmax
  have hobj := optimalValue_eq_of_globalMax p t hp hmax
  rw [hrep, objective_zeroExtend, objective_candidateVector] at hobj
  have hparams : OptimalHeavyParameters t h m z := ⟨hm, hroot, hentropy, hobj.symm⟩
  exact ⟨m, z, hm, hz, e, hroot, hrep, hscales m z hparams⟩

end ProbabilityVector

/-- The complete fixed-entropy asymptotic theorem, including uniformity over all maximizers.
The normalized epsilon statements are precisely the three asymptotic equivalences in the paper. -/
theorem thm_asymptotics (h : ℝ) (hh : 0 < h) :
    ((fun t : ℕ => h / optimalValue t h - (Real.log t + Real.log (Real.log t) + 2))
      =O[atTop] (fun t => Real.log (Real.log t) / Real.log t)) ∧
    (∀ᶠ t : ℕ in atTop, ∀ p : ProbabilityVector ℕ, p ∈ ProbabilityVector.Feasible h →
      (∀ q : ProbabilityVector ℕ, q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t) →
      ProbabilityVector.HeavyCandidateForm h p) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, ∀ p : ProbabilityVector ℕ,
      p ∈ ProbabilityVector.Feasible h →
      (∀ q : ProbabilityVector ℕ, q ∈ ProbabilityVector.Feasible h → q.objective t ≤ p.objective t) →
      ProbabilityVector.HeavyScaleApproximation t h ε p) :=
  ⟨optimalValue_sharp_asymptotic h hh, ProbabilityVector.globalMax_eventually_heavy h hh,
    fun ε hε => ProbabilityVector.globalMax_optimizer_scales_uniform h hh ε hε⟩

end
end EntropyConstrainedMissingMass
