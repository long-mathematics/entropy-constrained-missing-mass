import EntropyConstrainedMissingMass.EntropyHessian
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Actual smooth entropy-level curves of distinct positive triples. -/

open Filter MeasureTheory Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.TripleGeometry
noncomputable section

private theorem zero_triple : (![0, 0, 0] : Triple) = 0 := by ext i; fin_cases i <;> rfl

private theorem ordered_pos (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (i : Fin 3) : 0 < x i := by
  fin_cases i
  · exact h0
  · exact h0.trans h01
  · exact h0.trans (h01.trans h12)

theorem contDiffAt_localEntropy (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ContDiffAt ℝ ⊤ (localEntropy x h01 h12) (symmetricMap x) := by
  unfold localEntropy tripleEntropy
  apply ContDiffAt.sum
  intro i _
  have hr := (contDiffAt_apply ℝ ℝ i (localRoots x h01 h12 (symmetricMap x))).comp
    (symmetricMap x) (contDiffAt_localRoots x h01 h12)
  have hn : localRoots x h01 h12 (symmetricMap x) i ≠ 0 := by
    rw [localRoots_image]
    exact (ordered_pos x h0 h01 h12 i).ne'
  exact hr.neg.mul (hr.log hn)

/-- The fixed-sum entropy equation in displacement coordinates `(E-E₀,P-P₀)`. -/
def entropyEquation (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (z : ℝ × ℝ) : ℝ :=
  localEntropy x h01 h12 (symmetricMap x + ![0, z.1, z.2])

theorem contDiffAt_entropyEquation (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ContDiffAt ℝ ⊤ (entropyEquation x h01 h12) (0, 0) := by
  have hc : ContDiff ℝ ⊤ (fun z : ℝ × ℝ => symmetricMap x + ![0, z.1, z.2]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  apply ContDiffAt.comp (f := fun z : ℝ × ℝ => symmetricMap x + ![0, z.1, z.2]) (0, 0) _ hc.contDiffAt
  simpa only [zero_triple, add_zero] using contDiffAt_localEntropy x h0 h01 h12

theorem entropyEquation_partial_P (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    fderiv ℝ (entropyEquation x h01 h12) (0, 0) (0, 1) = Curvature.I0 (x 0) (x 1) (x 2) := by
  have hf := (contDiffAt_entropyEquation x h0 h01 h12).differentiableAt (by simp)
  have hp := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
  have hd := hf.hasFDerivAt.comp_hasDerivAt 0 hp
  have hactual := hasDerivAt_localEntropy_P x h0 h01 h12
  have hsame : (entropyEquation x h01 h12 ∘ (fun r : ℝ => ((0 : ℝ), r))) =
      fun r : ℝ => localEntropy x h01 h12 (symmetricMap x + r • ![0, 0, 1]) := by
    funext r
    simp [entropyEquation]
  rw [hsame] at hd
  exact hd.unique hactual

theorem entropyEquation_P_invertible (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    (fderiv ℝ (entropyEquation x h01 h12) (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
  have heq : fderiv ℝ (entropyEquation x h01 h12) (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (Curvature.I0 (x 0) (x 1) (x 2)) := by
    apply ContinuousLinearMap.ext_ring
    simpa using entropyEquation_partial_P x h0 h01 h12
  rw [heq]
  have hn : Curvature.I0 (x 0) (x 1) (x 2) ≠ 0 :=
    (Curvature.I0_pos _ _ _ h0 (h0.trans h01) (h0.trans (h01.trans h12))).ne'
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ (Curvature.I0 (x 0) (x 1) (x 2))⁻¹)
  · ext
    simp [hn]
  · ext
    simp [hn]

/-- The implicit change in `P` as `E` changes from its base value. -/
def entropyCurveP (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) : ℝ → ℝ :=
  (contDiffAt_entropyEquation x h0 h01 h12).implicitFunction (by simp)
    (entropyEquation_P_invertible x h0 h01 h12)

@[simp] theorem entropyCurveP_zero (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    entropyCurveP x h0 h01 h12 0 = 0 := ContDiffAt.implicitFunction_apply_self _ _ _

theorem contDiffAt_entropyCurveP (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ContDiffAt ℝ ⊤ (entropyCurveP x h0 h01 h12) 0 := ContDiffAt.contDiffAt_implicitFunction _ _ _

/-- The roots along the genuine fixed-sum, fixed-entropy curve, parametrized by the change in `E`. -/
def entropyCurve (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (r : ℝ) : Triple :=
  localRoots x h01 h12 (symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r])

@[simp] theorem entropyCurve_zero (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    entropyCurve x h0 h01 h12 0 = x := by
  simp only [entropyCurve, entropyCurveP_zero, zero_triple, add_zero, localRoots_image]

theorem contDiffAt_entropyCurve (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ContDiffAt ℝ ⊤ (entropyCurve x h0 h01 h12) 0 := by
  have hc : ContDiffAt ℝ ⊤ (fun r : ℝ => symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r]) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp
    · exact contDiffAt_const
    · exact contDiffAt_const.add contDiffAt_id
    · exact contDiffAt_const.add (contDiffAt_entropyCurveP x h0 h01 h12)
  apply ContDiffAt.comp (f := fun r : ℝ => symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r]) 0 _ hc
  simpa only [entropyCurveP_zero, zero_triple, add_zero] using contDiffAt_localRoots x h01 h12

theorem eventually_entropyCurve_entropy (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in nhds (0 : ℝ), tripleEntropy (entropyCurve x h0 h01 h12 r) = tripleEntropy x := by
  have hd := (contDiffAt_entropyEquation x h0 h01 h12).eventually_apply_implicitFunction
    (by simp) (entropyEquation_P_invertible x h0 h01 h12)
  simpa only [entropyEquation, localEntropy, entropyCurve, entropyCurveP, zero_triple, add_zero, localRoots_image] using hd

/-- The curve has the prescribed symmetric coordinates on a neighborhood of zero. -/
theorem eventually_entropyCurve_symmetric (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in nhds (0 : ℝ), symmetricMap (entropyCurve x h0 h01 h12 r) =
      symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r] := by
  have ht : Tendsto (fun r : ℝ => symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r])
      (nhds 0) (nhds (symmetricMap x)) := by
    have hc : ContinuousAt (fun r : ℝ => symmetricMap x + ![0, r, entropyCurveP x h0 h01 h12 r]) 0 := by
      apply continuousAt_pi.mpr
      intro i
      fin_cases i <;> dsimp
      · exact continuousAt_const
      · exact continuousAt_const.add continuousAt_id
      · exact continuousAt_const.add (contDiffAt_entropyCurveP x h0 h01 h12).continuousAt
    simpa only [entropyCurveP_zero, zero_triple, add_zero] using hc.tendsto
  exact ht.eventually (eventually_localRoots_right_inverse x h01 h12)

private theorem entropy_velocity_sum (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (b : ℝ) :
    (∑ i : Fin 3, (-Real.log (x i) - 1) * ((-(x i) + b) / rootDenom x i)) =
      Curvature.I1 (x 0) (x 1) (x 2) + b * Curvature.I0 (x 0) (x 1) (x 2) := by
  have heq (i : Fin 3) : (-Real.log (x i) - 1) * ((-(x i) + b) / rootDenom x i) =
      (x i / rootDenom x i) * Real.log (x i) + x i / rootDenom x i +
        b * ((-1 / rootDenom x i) * Real.log (x i)) - b * (1 / rootDenom x i) := by ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_root_div_rootDenom x h01 h12,
    sum_inv_rootDenom x h01 h12, ← I1_eq_log_sum x h0 h01 h12, ← I0_eq_log_sum x h0 h01 h12]
  ring

/-- Entropy conservation forces the actual product velocity `P′=-I1/I0`. -/
theorem hasDerivAt_P_of_entropy_path {p : ℝ → Triple} {a : ℝ}
    (hp : DifferentiableAt ℝ p a) (h0 : 0 < p a 0) (h01 : p a 0 < p a 1) (h12 : p a 1 < p a 2)
    (hS : HasDerivAt (fun r => symmetricMap (p r) 0) 0 a)
    (hE : HasDerivAt (fun r => symmetricMap (p r) 1) 1 a)
    (hH : HasDerivAt (fun r => tripleEntropy (p r)) 0 a) :
    HasDerivAt (fun r => symmetricMap (p r) 2) (-Curvature.m (p a 0) (p a 1) (p a 2)) a := by
  have hd := (hasFDerivAt_symmetricMap (p a)).comp_hasDerivAt a hp.hasDerivAt
  have hs := (hasDerivAt_pi.mp hd 0).unique hS
  have he := (hasDerivAt_pi.mp hd 1).unique hE
  let b := differential (p a) (deriv p a) 2
  have hv (i : Fin 3) : deriv p a i = (-(p a i) + b) / rootDenom (p a) i := by
    apply (eq_div_iff (rootDenom_ne_zero (p a) h01 h12 i)).mpr
    have hh := rootDenom_mul_eq_differential (p a) (deriv p a) i
    rw [hs, he] at hh
    dsimp [b]
    nlinarith only [hh]
  have hh (i : Fin 3) := (Real.hasDerivAt_negMulLog
    (ordered_pos (p a) h0 h01 h12 i).ne').comp a (hasDerivAt_pi.mp hp.hasDerivAt i)
  have hz := (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hh i)).unique hH
  simp_rw [hv] at hz
  rw [entropy_velocity_sum (p a) h0 h01 h12 b] at hz
  have hn := (Curvature.I0_pos _ _ _ h0 (h0.trans h01) (h0.trans (h01.trans h12))).ne'
  have hb : b = -Curvature.m (p a 0) (p a 1) (p a 2) := by
    unfold Curvature.m
    rw [← neg_div]
    apply (eq_div_iff hn).mpr
    linarith
  have hP := hasDerivAt_pi.mp hd 2
  change HasDerivAt (fun r => symmetricMap (p r) 2) b a at hP
  rw [hb] at hP
  exact hP

/-- The curve stays positive and ordered, and has the exact local symmetric velocities. -/
theorem eventually_entropyCurve_derivatives (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in nhds (0 : ℝ),
      DifferentiableAt ℝ (entropyCurve x h0 h01 h12) r ∧
      0 < entropyCurve x h0 h01 h12 r 0 ∧
      entropyCurve x h0 h01 h12 r 0 < entropyCurve x h0 h01 h12 r 1 ∧
      entropyCurve x h0 h01 h12 r 1 < entropyCurve x h0 h01 h12 r 2 ∧
      HasDerivAt (fun u => symmetricMap (entropyCurve x h0 h01 h12 u) 0) 0 r ∧
      HasDerivAt (fun u => symmetricMap (entropyCurve x h0 h01 h12 u) 1) 1 r ∧
      HasDerivAt (fun u => symmetricMap (entropyCurve x h0 h01 h12 u) 2)
        (-Curvature.m (entropyCurve x h0 h01 h12 r 0) (entropyCurve x h0 h01 h12 r 1)
          (entropyCurve x h0 h01 h12 r 2)) r := by
  let p := entropyCurve x h0 h01 h12
  have hc : ∀ᶠ r in nhds (0 : ℝ), DifferentiableAt ℝ p r := by
    have hd := (contDiffAt_entropyCurve x h0 h01 h12).of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
    exact (hd.eventually (by norm_num)).mono (fun r hr => hr.differentiableAt (by norm_num))
  have hp : ∀ᶠ r in nhds (0 : ℝ), 0 < p r 0 ∧ p r 0 < p r 1 ∧ p r 1 < p r 2 := by
    have hopen : IsOpen {y : Triple | 0 < y 0 ∧ y 0 < y 1 ∧ y 1 < y 2} :=
      (isOpen_lt continuous_const (continuous_apply 0)).inter
        ((isOpen_lt (continuous_apply 0) (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) (continuous_apply 2)))
    have ht : Tendsto p (nhds 0) (nhds x) := by
      simpa only [p, entropyCurve_zero] using (contDiffAt_entropyCurve x h0 h01 h12).continuousAt.tendsto
    exact ht.eventually (hopen.mem_nhds ⟨h0, h01, h12⟩)
  have hsym := (eventually_entropyCurve_symmetric x h0 h01 h12).eventually_nhds
  have hent := (eventually_entropyCurve_entropy x h0 h01 h12).eventually_nhds
  filter_upwards [hc, hp, hsym, hent] with r hr hp hs he
  have hS : HasDerivAt (fun u => symmetricMap (p u) 0) 0 r := by
    apply (hasDerivAt_const r (symmetricMap x 0)).congr_of_eventuallyEq
    filter_upwards [hs] with u hu
    simpa using congrArg (fun v : Triple => v 0) hu
  have hE : HasDerivAt (fun u => symmetricMap (p u) 1) 1 r := by
    apply ((hasDerivAt_id r).const_add (symmetricMap x 1)).congr_of_eventuallyEq
    filter_upwards [hs] with u hu
    simpa using congrArg (fun v : Triple => v 1) hu
  have hH : HasDerivAt (fun u => tripleEntropy (p u)) 0 r :=
    (hasDerivAt_const r (tripleEntropy x)).congr_of_eventuallyEq he
  exact ⟨hr, hp.1, hp.2.1, hp.2.2, hS, hE,
    hasDerivAt_P_of_entropy_path hr hp.1 hp.2.1 hp.2.2 hS hE hH⟩

private theorem fderiv_apply_of_direction {H : Triple → ℝ} {c w : Triple} {b : ℝ}
    (hH : DifferentiableAt ℝ H c)
    (hd : HasDerivAt (fun r : ℝ => H (c + r • w)) b 0) : fderiv ℝ H c w = b := by
  have hp : HasDerivAt (fun r : ℝ => c + r • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add c
  have hc : HasFDerivAt H (fderiv ℝ H c) ((fun r : ℝ => c + r • w) 0) := by
    simpa only [zero_smul, add_zero] using hH.hasFDerivAt
  exact (hc.comp_hasDerivAt 0 hp).unique hd

private theorem directionalPartial_eq_fderiv {H : Triple → ℝ} {c : Triple}
    (hH : DifferentiableAt ℝ H c) (w : Triple) :
    deriv (fun r : ℝ => H (c + r • w)) 0 = fderiv ℝ H c w := by
  have hp : HasDerivAt (fun r : ℝ => c + r • w) w 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add c
  have hc : HasFDerivAt H (fderiv ℝ H c) ((fun r : ℝ => c + r • w) 0) := by
    simpa only [zero_smul, add_zero] using hH.hasFDerivAt
  exact (hc.comp_hasDerivAt 0 hp).deriv

private theorem contDiffAt_directionalPartial {H : Triple → ℝ} {c : Triple}
    (hH : ContDiffAt ℝ ⊤ H c) (w : Triple) :
    ContDiffAt ℝ 1 (fun z => deriv (fun r : ℝ => H (z + r • w)) 0) c := by
  have hdiff : ∀ᶠ z in nhds c, DifferentiableAt ℝ H z := by
    have hc := hH.of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)
    exact (hc.eventually (by norm_num)).mono (fun z hz => hz.differentiableAt (by norm_num))
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ H) c := hH.fderiv_right (by simp)
  have heval : ContDiffAt ℝ 1 (fun z => fderiv ℝ H z w) c := hfd.clm_apply contDiffAt_const
  apply heval.congr_of_eventuallyEq
  exact hdiff.mono (fun z hz => directionalPartial_eq_fderiv hz w)

theorem differentiableAt_partialEntropy_E (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    DifferentiableAt ℝ (partialE (localEntropy x h01 h12)) (symmetricMap x) :=
  (contDiffAt_directionalPartial (contDiffAt_localEntropy x h0 h01 h12) ![0, 1, 0]).differentiableAt (by norm_num)

theorem differentiableAt_partialEntropy_P (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    DifferentiableAt ℝ (partialP (localEntropy x h01 h12)) (symmetricMap x) :=
  (contDiffAt_directionalPartial (contDiffAt_localEntropy x h0 h01 h12) ![0, 0, 1]).differentiableAt (by norm_num)

/-- The full symmetric-coordinate velocity along the entropy curve. -/
theorem hasDerivAt_entropyCurve_symmetric (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r => symmetricMap (entropyCurve x h0 h01 h12 r))
      ![0, 1, -Curvature.m (x 0) (x 1) (x 2)] 0 := by
  have hh := (eventually_entropyCurve_derivatives x h0 h01 h12).self_of_nhds
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2.1
  · change HasDerivAt (fun r => symmetricMap (entropyCurve x h0 h01 h12 r) 2)
      (-Curvature.m (x 0) (x 1) (x 2)) 0
    simpa only [entropyCurve_zero] using hh.2.2.2.2.2.2

private theorem eventually_curve_moments (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ r in nhds (0 : ℝ),
      partialE (localEntropy x h01 h12) (symmetricMap (entropyCurve x h0 h01 h12 r)) =
        Curvature.I1 (entropyCurve x h0 h01 h12 r 0) (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2) ∧
      partialP (localEntropy x h01 h12) (symmetricMap (entropyCurve x h0 h01 h12 r)) =
        Curvature.I0 (entropyCurve x h0 h01 h12 r 0) (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2) := by
  have ht : Tendsto (entropyCurve x h0 h01 h12) (nhds 0) (nhds x) := by
    simpa only [entropyCurve_zero] using (contDiffAt_entropyCurve x h0 h01 h12).continuousAt.tendsto
  have hsym : Tendsto (fun r => symmetricMap (entropyCurve x h0 h01 h12 r)) (nhds 0) (nhds (symmetricMap x)) :=
    contDiff_symmetricMap.continuous.continuousAt.tendsto.comp ht
  filter_upwards [hsym.eventually (eventually_partialEntropy_integrals x h0 h01 h12),
    ht.eventually (eventually_localRoots_left_inverse x h01 h12)] with r hr hroot
  simpa only [hroot] using hr

/-- Actual derivative of `I1` along the entropy level curve. -/
theorem hasDerivAt_curve_I1 (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r => Curvature.I1 (entropyCurve x h0 h01 h12 r 0)
      (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2))
      (-(∫ s in Ioi (0 : ℝ), s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) +
        Curvature.m (x 0) (x 1) (x 2) *
          (∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have hdf := differentiableAt_partialEntropy_E x h0 h01 h12
  have he := fderiv_apply_of_direction hdf (hasDerivAt_partialEntropy_EE x h0 h01 h12)
  have hp := fderiv_apply_of_direction hdf (hasDerivAt_partialEntropy_EP x h0 h01 h12)
  have hc : HasFDerivAt (partialE (localEntropy x h01 h12))
      (fderiv ℝ (partialE (localEntropy x h01 h12)) (symmetricMap x))
      (symmetricMap (entropyCurve x h0 h01 h12 0)) := by simpa only [entropyCurve_zero] using hdf.hasFDerivAt
  have hd := hc.comp_hasDerivAt 0 (hasDerivAt_entropyCurve_symmetric x h0 h01 h12)
  have hv : (![0, 1, -Curvature.m (x 0) (x 1) (x 2)] : Triple) =
      ![0, 1, 0] - Curvature.m (x 0) (x 1) (x 2) • ![0, 0, 1] := by ext i; fin_cases i <;> simp
  rw [hv, map_sub, map_smul, he, hp] at hd
  simp only [smul_eq_mul, mul_neg, sub_neg_eq_add] at hd
  apply hd.congr_of_eventuallyEq
  exact (eventually_curve_moments x h0 h01 h12).mono (fun r hr => hr.1.symm)

/-- Actual derivative of `I0` along the entropy level curve. -/
theorem hasDerivAt_curve_I0 (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r => Curvature.I0 (entropyCurve x h0 h01 h12 r 0)
      (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2))
      (-(∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) +
        Curvature.m (x 0) (x 1) (x 2) *
          (∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2)) 0 := by
  have hdf := differentiableAt_partialEntropy_P x h0 h01 h12
  have he := fderiv_apply_of_direction hdf (hasDerivAt_partialEntropy_PE x h0 h01 h12)
  have hp := fderiv_apply_of_direction hdf (hasDerivAt_partialEntropy_PP x h0 h01 h12)
  have hc : HasFDerivAt (partialP (localEntropy x h01 h12))
      (fderiv ℝ (partialP (localEntropy x h01 h12)) (symmetricMap x))
      (symmetricMap (entropyCurve x h0 h01 h12 0)) := by simpa only [entropyCurve_zero] using hdf.hasFDerivAt
  have hd := hc.comp_hasDerivAt 0 (hasDerivAt_entropyCurve_symmetric x h0 h01 h12)
  have hv : (![0, 1, -Curvature.m (x 0) (x 1) (x 2)] : Triple) =
      ![0, 1, 0] - Curvature.m (x 0) (x 1) (x 2) • ![0, 0, 1] := by ext i; fin_cases i <;> simp
  rw [hv, map_sub, map_smul, he, hp] at hd
  simp only [smul_eq_mul, mul_neg, sub_neg_eq_add] at hd
  apply hd.congr_of_eventuallyEq
  exact (eventually_curve_moments x h0 h01 h12).mono (fun r hr => hr.2.symm)

/-- Expanding the convergent numerator integral defining entropy curvature. -/
theorem integral_curvature_expand (x : Triple) (hx : ∀ i, 0 < x i) (m : ℝ) :
    (∫ s in Ioi (0 : ℝ), (s - m) ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) =
      (∫ s in Ioi (0 : ℝ), s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) -
      (2 * m) * (∫ s in Ioi (0 : ℝ), s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) +
      m ^ 2 * (∫ s in Ioi (0 : ℝ), 1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) := by
  have h0 := (integrableOn_div_D_sq x hx).1
  have h1 := (integrableOn_div_D_sq x hx).2
  have h2 : IntegrableOn (fun s : ℝ => s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) (Ioi (0 : ℝ)) := by
    simpa only [sub_zero] using Curvature.integrableOn_curvature_numerator (x 0) (x 1) (x 2) 0 (hx 0) (hx 1) (hx 2)
  have heq : (fun s : ℝ => (s - m) ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) =
      fun s : ℝ => s ^ 2 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2 -
        (2 * m) * (s / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) +
        m ^ 2 * (1 / (Curvature.D (x 0) (x 1) (x 2) s) ^ 2) := by funext s; ring
  rw [heq, integral_add (h2.fun_sub (h1.const_mul (2 * m))) (h0.const_mul (m ^ 2)),
    integral_sub h2 (h1.const_mul (2 * m)), integral_const_mul, integral_const_mul]

/-- The normalized mean decreases with derivative exactly minus the manuscript's curvature. -/
theorem hasDerivAt_entropyCurve_m (x : Triple) (h0 : 0 < x 0) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (fun r => Curvature.m (entropyCurve x h0 h01 h12 r 0)
      (entropyCurve x h0 h01 h12 r 1) (entropyCurve x h0 h01 h12 r 2))
      (-Curvature.K (x 0) (x 1) (x 2)) 0 := by
  have hn : Curvature.I0 (x 0) (x 1) (x 2) ≠ 0 :=
    (Curvature.I0_pos _ _ _ h0 (h0.trans h01) (h0.trans (h01.trans h12))).ne'
  have hn' : Curvature.I0 (entropyCurve x h0 h01 h12 0 0)
      (entropyCurve x h0 h01 h12 0 1) (entropyCurve x h0 h01 h12 0 2) ≠ 0 := by
    simpa only [entropyCurve_zero] using hn
  have hd := (hasDerivAt_curve_I1 x h0 h01 h12).div (hasDerivAt_curve_I0 x h0 h01 h12) hn'
  simp only [entropyCurve_zero] at hd
  convert hd using 1
  · rfl
  · rw [Curvature.K, integral_curvature_expand x (ordered_pos x h0 h01 h12)]
    unfold Curvature.m
    field_simp
    ring

/-- The actual second product derivative is the normalized entropy curvature `K`. -/
theorem hasDerivAt_deriv_entropyCurve_product (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasDerivAt (deriv (fun r => symmetricMap (entropyCurve x h0 h01 h12 r) 2))
      (Curvature.K (x 0) (x 1) (x 2)) 0 := by
  have hd := (hasDerivAt_entropyCurve_m x h0 h01 h12).neg
  simp only [neg_neg] at hd
  apply hd.congr_of_eventuallyEq
  exact (eventually_entropyCurve_derivatives x h0 h01 h12).mono (fun r hr => hr.2.2.2.2.2.2.deriv)

end
end EntropyConstrainedMissingMass.TripleGeometry
