import EntropyConstrainedMissingMass.EntropyLevelCurve
import EntropyConstrainedMissingMass.DividedDifferences
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The literal first and Hessian chain-rule variations along the actual entropy curve. -/

open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace EntropyConstrainedMissingMass.TripleGeometry
noncomputable section

private def directionalPartial (F : Triple → ℝ) (v : Triple) (c : Triple) : ℝ :=
  deriv (fun r : ℝ => F (c + r • v)) 0

private theorem directionalPartial_eq {F : Triple → ℝ} {c : Triple}
    (hF : DifferentiableAt ℝ F c) (v : Triple) :
    directionalPartial F v c = fderiv ℝ F c v := by
  have hp : HasDerivAt (fun r : ℝ => c + r • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add c
  have hc : HasFDerivAt F (fderiv ℝ F c) ((fun r : ℝ => c + r • v) 0) := by
    simpa only [zero_smul, add_zero] using hF.hasFDerivAt
  exact (hc.comp_hasDerivAt 0 hp).deriv

private theorem eventually_differentiable {F : Triple → ℝ} {c : Triple}
    (hF : ContDiffAt ℝ ⊤ F c) : ∀ᶠ y in 𝓝 c, DifferentiableAt ℝ F y := by
  have hc := hF.of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
  exact (hc.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))

private theorem contDiffAt_directionalPartial {F : Triple → ℝ} {c : Triple}
    (hF : ContDiffAt ℝ ⊤ F c) (v : Triple) :
    ContDiffAt ℝ 1 (directionalPartial F v) c := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) c := hF.fderiv_right (by simp)
  have heval : ContDiffAt ℝ 1 (fun y => fderiv ℝ F y v) c := hfd.clm_apply contDiffAt_const
  apply heval.congr_of_eventuallyEq
  exact (eventually_differentiable hF).mono (fun y hy => directionalPartial_eq hy v)

private theorem second_directionalPartial {F : Triple → ℝ} {c : Triple}
    (hF : ContDiffAt ℝ ⊤ F c) (v w : Triple) :
    directionalPartial (directionalPartial F v) w c = fderiv ℝ (fderiv ℝ F) c w v := by
  have hfdC : ContDiffAt ℝ 1 (fderiv ℝ F) c := hF.fderiv_right (by simp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) c := hfdC.differentiableAt (by norm_num)
  have hp : HasDerivAt (fun r : ℝ => c + r • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add c
  have hc : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) c)
      ((fun r : ℝ => c + r • w) 0) := by
    simpa only [zero_smul, add_zero] using hfd.hasFDerivAt
  have hd := (hc.comp_hasDerivAt 0 hp).clm_apply (hasDerivAt_const (0 : ℝ) v)
  simp only [map_zero, add_zero] at hd
  have ht : Tendsto (fun r : ℝ => c + r • w) (𝓝 0) (𝓝 c) := by
    simpa only [zero_smul, add_zero] using hp.continuousAt.tendsto
  have he : (fun r : ℝ => directionalPartial F v (c + r • w)) =ᶠ[𝓝 0]
      (fun r => fderiv ℝ F (c + r • w) v) := by
    filter_upwards [ht.eventually (eventually_differentiable hF)] with r hr
    exact directionalPartial_eq hr v
  exact (hd.congr_of_eventuallyEq he).deriv

/-- Mixed E,P partial derivatives of a smooth statistic really commute. -/
theorem mixed_partialE_partialP {F : Triple → ℝ} {c : Triple} (hF : ContDiffAt ℝ ⊤ F c) :
    partialP (partialE F) c = partialE (partialP F) c := by
  change directionalPartial (directionalPartial F ![0, 1, 0]) ![0, 0, 1] c =
    directionalPartial (directionalPartial F ![0, 0, 1]) ![0, 1, 0] c
  rw [second_directionalPartial hF, second_directionalPartial hF]
  exact (hF.isSymmSndFDerivAt (by simp)).eq _ _

/-- The first chain rule in symmetric coordinates with velocity (0,1,-m). -/
theorem hasDerivAt_symmetric_variation {F : Triple → ℝ} {c : ℝ → Triple} {a m : ℝ}
    (hF : DifferentiableAt ℝ F (c a)) (hc : HasDerivAt c ![0, 1, -m] a) :
    HasDerivAt (fun r => F (c r)) (partialE F (c a) - m * partialP F (c a)) a := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt a hc
  have hv : (![0, 1, -m] : Triple) = ![0, 1, 0] - m • ![0, 0, 1] := by
    ext i; fin_cases i <;> simp
  change HasDerivAt (fun r => F (c r))
    (directionalPartial F ![0, 1, 0] (c a) - m * directionalPartial F ![0, 0, 1] (c a)) a
  rw [directionalPartial_eq hF, directionalPartial_eq hF]
  convert hd using 1
  all_goals first | rfl | simp only [hv, map_sub, map_smul, smul_eq_mul]

/-- The complete literal Hessian chain rule, including the mixed-partial equality. -/
theorem hasDerivAt_deriv_symmetric_variation {F : Triple → ℝ} {c : ℝ → Triple}
    {a K : ℝ} {m : ℝ → ℝ} (hF : ContDiffAt ℝ ⊤ F (c a))
    (hc : ∀ᶠ r in 𝓝 a, HasDerivAt c ![0, 1, -(m r)] r)
    (hm : HasDerivAt m (-K) a) :
    HasDerivAt (deriv (fun r => F (c r)))
      (partialE (partialE F) (c a) - 2 * m a * partialP (partialE F) (c a) +
        (m a) ^ 2 * partialP (partialP F) (c a) + K * partialP F (c a)) a := by
  have hca := hc.self_of_nhds
  have hFE : DifferentiableAt ℝ (partialE F) (c a) :=
    (contDiffAt_directionalPartial hF ![0, 1, 0]).differentiableAt (by norm_num)
  have hFP : DifferentiableAt ℝ (partialP F) (c a) :=
    (contDiffAt_directionalPartial hF ![0, 0, 1]).differentiableAt (by norm_num)
  have hE := hasDerivAt_symmetric_variation hFE hca
  have hP := hasDerivAt_symmetric_variation hFP hca
  have hd := hE.sub (hm.mul hP)
  have hmix := mixed_partialE_partialP hF
  rw [← hmix] at hd
  have he : deriv (fun r => F (c r)) =ᶠ[𝓝 a]
      (fun r => partialE F (c r) - m r * partialP F (c r)) := by
    filter_upwards [hc, hca.continuousAt.tendsto.eventually (eventually_differentiable hF)] with r hr hFr
    exact (hasDerivAt_symmetric_variation hFr hr).deriv
  apply (hd.congr_deriv (by ring)).congr_of_eventuallyEq he

/-- All polynomial missing-mass statistics are smooth in the genuine local root chart. -/
theorem contDiffAt_localObjective (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (t : ℕ) :
    ContDiffAt ℝ ⊤ (localStatistic x h01 h12 (missingMassTerm t)) (symmetricMap x) := by
  unfold localStatistic
  apply ContDiffAt.sum
  intro i _
  have hr := (contDiffAt_apply ℝ ℝ i (localRoots x h01 h12 (symmetricMap x))).comp
    (symmetricMap x) (contDiffAt_localRoots x h01 h12)
  change ContDiffAt ℝ ⊤ (fun c => localRoots x h01 h12 c i * (1 - localRoots x h01 h12 c i) ^ t) _
  exact hr.mul ((contDiffAt_const.sub hr).pow t)

/-- The literal Hessian formula eq:variations for the actual entropy curve and objective. -/
theorem entropyCurve_objective_variations (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) (t : ℕ) :
    let F := localStatistic x h01 h12 (missingMassTerm t)
    let c := symmetricMap x
    let m := Curvature.m (x 0) (x 1) (x 2)
    let K := Curvature.K (x 0) (x 1) (x 2)
    let φ := fun r => ∑ i : Fin 3, missingMassTerm t (entropyCurve x h0 h01 h12 r i)
    HasDerivAt φ (partialE F c - m * partialP F c) 0 ∧
      HasDerivAt (deriv φ)
        (partialE (partialE F) c - 2 * m * partialP (partialE F) c +
          m ^ 2 * partialP (partialP F) c + K * partialP F c) 0 := by
  dsimp only
  let c := fun r => symmetricMap (entropyCurve x h0 h01 h12 r)
  let m := fun r => Curvature.m (entropyCurve x h0 h01 h12 r 0)
    (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2)
  let F := localStatistic x h01 h12 (missingMassTerm t)
  have hc : ∀ᶠ r in 𝓝 (0 : ℝ), HasDerivAt c ![0, 1, -(m r)] r := by
    filter_upwards [eventually_entropyCurve_derivatives x h0 h01 h12] with r hr
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hr.2.2.2.2.1
    · exact hr.2.2.2.2.2.1
    · exact hr.2.2.2.2.2.2
  have hF : ContDiffAt ℝ ⊤ F (c 0) := by
    simpa only [c, entropyCurve_zero] using contDiffAt_localObjective x h01 h12 t
  have hd := hasDerivAt_symmetric_variation (hF.differentiableAt (by simp)) hc.self_of_nhds
  have hd2 := hasDerivAt_deriv_symmetric_variation hF hc (hasDerivAt_entropyCurve_m x h0 h01 h12)
  have heq : (fun r => ∑ i : Fin 3, missingMassTerm t (entropyCurve x h0 h01 h12 r i)) =ᶠ[𝓝 0]
      (fun r => F (c r)) := by
    have ht : Tendsto (entropyCurve x h0 h01 h12) (𝓝 0) (𝓝 x) := by
      simpa only [entropyCurve_zero] using (contDiffAt_entropyCurve x h0 h01 h12).continuousAt.tendsto
    filter_upwards [ht.eventually (eventually_localRoots_left_inverse x h01 h12)] with r hr
    dsimp [F, c, localStatistic]
    rw [hr]
  have hv0 : c 0 = symmetricMap x := by simp [c]
  have hm0 : m 0 = Curvature.m (x 0) (x 1) (x 2) := by simp [m]
  rw [hv0, hm0] at hd hd2
  exact ⟨hd.congr_of_eventuallyEq heq, hd2.congr_of_eventuallyEq heq.deriv⟩

end
end EntropyConstrainedMissingMass.TripleGeometry
