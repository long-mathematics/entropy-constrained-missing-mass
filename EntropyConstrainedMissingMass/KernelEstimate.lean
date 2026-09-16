import EntropyConstrainedMissingMass.CurvatureIntegrals

/-! The probability kernels used in Appendix A and their mixed quadratic integral. -/

open MeasureTheory Set Filter
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- The probability kernel of scale `a`. -/
noncomputable def kernel (a s : ℝ) : ℝ := 2 * a ^ 2 / (s + a) ^ 3

/-- Appendix A's mixed quadratic kernel integral. -/
noncomputable def J (a : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (s - 1) ^ 2 * kernel 1 s * kernel a s

/-- The kernel has total mass one. -/
theorem integral_kernel (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), kernel a s) = 1 := by
  have heq : kernel a = fun s : ℝ => (2 * a ^ 2) * (1 / (s + a) ^ 3) := by
    funext s
    simp [kernel, div_eq_mul_inv]
  rw [heq, integral_const_mul, integral_inv_add_pow a ha 1]
  norm_num
  field_simp

/-- The kernel's mean is its scale. -/
theorem integral_mul_kernel (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), s * kernel a s) = a := by
  have heq : (fun s : ℝ => s * kernel a s) =
      fun s : ℝ => (2 * a ^ 2) * (s / D a a a s) := by
    funext s
    rw [D_uniform]
    simp [kernel]
    ring
  rw [heq, integral_const_mul]
  change (2 * a ^ 2) * I1 a a a = a
  rw [I1_uniform a ha]
  field_simp

/-- The mixed kernel integral at the uniform scale. -/
theorem J_one : J 1 = 8 / 15 := by
  have heq : (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel 1 s) =
      fun s : ℝ => 4 * ((s - 1) ^ 2 / ((s + 1) ^ 3) ^ 2) := by
    funext s
    simp only [kernel, one_pow, mul_one, div_eq_mul_inv, ← inv_pow]
    ring
  unfold J
  rw [heq, integral_const_mul, integral_uniform_curvature_numerator 1 (by norm_num)]
  norm_num

/-- The convergent difference of two reciprocal kernels integrates to a logarithm. -/
theorem integral_reciprocal_difference (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => 1 / (s + 1) - 1 / (s + a)) (Ioi (0 : ℝ)) ∧
      (∫ s in Ioi (0 : ℝ), (1 / (s + 1) - 1 / (s + a))) = Real.log a := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt
      (fun v : ℝ => Real.log (v + 1) - Real.log (v + a))
      (1 / (s + 1) - 1 / (s + a)) s := by
    intro s hs
    have hs1 : s + 1 ≠ 0 := by linarith [mem_Ici.mp hs]
    have hsa : s + a ≠ 0 := by linarith [mem_Ici.mp hs]
    simpa using (((hasDerivAt_id s).add_const 1).log hs1).fun_sub
      (((hasDerivAt_id s).add_const a).log hsa)
  have hinv : Tendsto (fun s : ℝ => (s + a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ a tendsto_id)
  have hrat : Tendsto (fun s : ℝ => 1 + (1 - a) * (s + a)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hrat
  have ht : Tendsto (fun s : ℝ => Real.log (s + 1) - Real.log (s + a)) atTop (𝓝 0) := by
    have hfun : (fun s : ℝ => Real.log (1 + (1 - a) * (s + a)⁻¹)) =ᶠ[atTop]
        (fun s : ℝ => Real.log (s + 1) - Real.log (s + a)) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have hsa : s + a ≠ 0 := by linarith
      have hs1 : s + 1 ≠ 0 := by linarith
      have hrat_eq : 1 + (1 - a) * (s + a)⁻¹ = (s + 1) / (s + a) := by
        field_simp
        ring
      rw [hrat_eq, Real.log_div hs1 hsa]
    simpa using hlog.congr' hfun
  have hi : IntegrableOn (fun s : ℝ => 1 / (s + 1) - 1 / (s + a)) (Ioi (0 : ℝ)) := by
    by_cases h1a : 1 ≤ a
    · apply integrableOn_Ioi_deriv_of_nonneg' hd _ ht
      intro s hs
      have hp : 0 < s + 1 := by linarith [mem_Ioi.mp hs]
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hp (by linarith))
    · apply integrableOn_Ioi_deriv_of_nonpos' hd _ ht
      intro s hs
      have hp : 0 < s + a := by linarith [mem_Ioi.mp hs]
      exact sub_nonpos.mpr (one_div_le_one_div_of_le hp (by linarith))
  refine ⟨hi, ?_⟩
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht

/-- The partial-fraction identity underlying the closed form of `J`. -/
theorem kernel_integrand_partial_fraction (a s : ℝ) (ha : a ≠ 1)
    (hs1 : s + 1 ≠ 0) (hsa : s + a ≠ 0) :
    (s - 1) ^ 2 * kernel 1 s * kernel a s =
      (16 * a ^ 2 / (a - 1) ^ 3) * (1 / (s + 1) ^ 3) -
      (4 * a ^ 2 * (a + 1) ^ 2 / (a - 1) ^ 3) * (1 / (s + a) ^ 3) -
      (16 * a ^ 2 * (a + 2) / (a - 1) ^ 4) * (1 / (s + 1) ^ 2) -
      (4 * a ^ 2 * (a + 1) * (a + 5) / (a - 1) ^ 4) * (1 / (s + a) ^ 2) +
      (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) / (a - 1) ^ 5) *
        (1 / (s + 1) - 1 / (s + a)) := by
  have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  unfold kernel
  field_simp
  ring

/-- The nonuniform mixed integral is convergent and has the exact logarithmic
closed form printed in Appendix A. Simple-pole terms are integrated as a
convergent difference, rather than individually. -/
theorem J_closed_form_aux (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    IntegrableOn (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel a s) (Ioi (0 : ℝ)) ∧
      J a = (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) * Real.log a -
        2 * (a - 1) * (7 * a ^ 3 + 33 * a ^ 2 + 9 * a - 1)) / (a - 1) ^ 5 := by
  let A3 : ℝ := 16 * a ^ 2 / (a - 1) ^ 3
  let B3 : ℝ := 4 * a ^ 2 * (a + 1) ^ 2 / (a - 1) ^ 3
  let A2 : ℝ := 16 * a ^ 2 * (a + 2) / (a - 1) ^ 4
  let B2 : ℝ := 4 * a ^ 2 * (a + 1) * (a + 5) / (a - 1) ^ 4
  let L : ℝ := 4 * a ^ 2 * (a ^ 2 + 10 * a + 13) / (a - 1) ^ 5
  let f : ℝ → ℝ := fun s => A3 * (1 / (s + 1) ^ 3) - B3 * (1 / (s + a) ^ 3) -
    A2 * (1 / (s + 1) ^ 2) - B2 * (1 / (s + a) ^ 2) +
      L * (1 / (s + 1) - 1 / (s + a))
  have hEq : ∀ s ∈ Ioi (0 : ℝ), (s - 1) ^ 2 * kernel 1 s * kernel a s = f s := by
    intro s hs
    exact kernel_integrand_partial_fraction a s ha1
      (by linarith [mem_Ioi.mp hs]) (by linarith [mem_Ioi.mp hs])
  have h13 : IntegrableOn (fun s : ℝ => A3 * (1 / (s + 1) ^ 3)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow 1 (by norm_num) 1).const_mul A3
  have ha3 : IntegrableOn (fun s : ℝ => B3 * (1 / (s + a) ^ 3)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow a ha 1).const_mul B3
  have h12 : IntegrableOn (fun s : ℝ => A2 * (1 / (s + 1) ^ 2)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow 1 (by norm_num) 0).const_mul A2
  have ha2 : IntegrableOn (fun s : ℝ => B2 * (1 / (s + a) ^ 2)) (Ioi (0 : ℝ)) :=
    (integrableOn_inv_add_pow a ha 0).const_mul B2
  have hl : IntegrableOn (fun s : ℝ => L * (1 / (s + 1) - 1 / (s + a))) (Ioi (0 : ℝ)) :=
    (integral_reciprocal_difference a ha).1.const_mul L
  have hf : IntegrableOn f (Ioi (0 : ℝ)) :=
    (((h13.fun_sub ha3).fun_sub h12).fun_sub ha2).fun_add hl
  refine ⟨hf.congr_fun (fun s hs => (hEq s hs).symm) measurableSet_Ioi, ?_⟩
  have hiEq : J a = ∫ s in Ioi (0 : ℝ), f s :=
    setIntegral_congr_fun measurableSet_Ioi hEq
  rw [hiEq]
  dsimp only [f]
  rw [integral_add (((h13.fun_sub ha3).fun_sub h12).fun_sub ha2) hl,
    integral_sub ((h13.fun_sub ha3).fun_sub h12) ha2,
    integral_sub (h13.fun_sub ha3) h12, integral_sub h13 ha3]
  simp only [integral_const_mul]
  rw [integral_inv_add_pow 1 (by norm_num) 1, integral_inv_add_pow a ha 1,
    integral_inv_add_pow 1 (by norm_num) 0, integral_inv_add_pow a ha 0,
    (integral_reciprocal_difference a ha).2]
  dsimp [A3, B3, A2, B2, L]
  have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  norm_num
  field_simp
  ring

/-- Closed form for a scale different from one. -/
theorem J_closed_form (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    J a = (4 * a ^ 2 * (a ^ 2 + 10 * a + 13) * Real.log a -
      2 * (a - 1) * (7 * a ^ 3 + 33 * a ^ 2 + 9 * a - 1)) / (a - 1) ^ 5 :=
  (J_closed_form_aux a ha ha1).2

/-- Convergence of the mixed kernel integral for every positive scale. -/
theorem integrableOn_J (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => (s - 1) ^ 2 * kernel 1 s * kernel a s) (Ioi (0 : ℝ)) := by
  by_cases ha1 : a = 1
  · subst a
    have hu : IntegrableOn (fun s : ℝ => 4 * ((s - 1) ^ 2 / (D 1 1 1 s) ^ 2))
        (Ioi (0 : ℝ)) :=
      (integrableOn_curvature_numerator 1 1 1 1 (by norm_num) (by norm_num)
        (by norm_num)).const_mul 4
    refine hu.congr_fun (fun s hs => ?_) measurableSet_Ioi
    dsimp only
    rw [D_uniform]
    simp only [kernel, one_pow, mul_one, div_eq_mul_inv, ← inv_pow]
    ring
  · exact (J_closed_form_aux a ha ha1).1

/-- The sharp kernel bound holds with equality at the uniform scale. -/
theorem kernel_bound_one : J 1 = 2 * (9 - (1 : ℝ)) / (15 * (1 + 1)) := by
  rw [J_one]
  norm_num

/-- The cubic appearing in the positive remainder is positive on positive arguments. -/
theorem kernel_remainder_cubic_pos (b : ℝ) (hb : 0 < b) :
    0 < 2 * b ^ 3 + 12 * b ^ 2 - 10 * b + 13 := by
  have hsq := sq_nonneg (b - 5 / 12)
  have hc : 0 < b ^ 3 := pow_pos hb 3
  nlinarith

private noncomputable def remainderPrimitive (a b : ℝ) : ℝ :=
    ((-1 / 3 : ℝ)) * b ^ 6 +
    (2 * (a - 1)) * b ^ 5 +
    (-(10 * a ^ 2 - 25 * a - 11) / 2) * b ^ 4 +
    ((20 * a ^ 3 - 100 * a ^ 2 - 110 * a - 23) / 3) * b ^ 3 +
    ((-10 * a ^ 4 + 100 * a ^ 3 + 220 * a ^ 2 + 115 * a + 13) / 2) * b ^ 2 +
    (a * (2 * a ^ 4 - 50 * a ^ 3 - 220 * a ^ 2 - 230 * a - 65)) * b +
    (10 * a ^ 2 * (a + 1) * (a ^ 2 + 10 * a + 13)) * Real.log b +
    (a ^ 3 * (22 * a ^ 2 + 115 * a + 130)) * b⁻¹ +
    (-a ^ 4 * (23 * a + 65) / 2) * (b⁻¹) ^ 2 +
    (13 * a ^ 5 / 3) * (b⁻¹) ^ 3

private theorem hasDerivAt_remainderPrimitive (a b : ℝ) (hb : b ≠ 0) :
    HasDerivAt (remainderPrimitive a)
      ((b - 1) * (a - b) ^ 5 * (2 * b ^ 3 + 12 * b ^ 2 - 10 * b + 13) / b ^ 4) b := by
  have h0 := ((hasDerivAt_id b).fun_pow 6).const_mul ((-1 / 3 : ℝ))
  have h1 := ((hasDerivAt_id b).fun_pow 5).const_mul (2 * (a - 1))
  have h2 := ((hasDerivAt_id b).fun_pow 4).const_mul (-(10 * a ^ 2 - 25 * a - 11) / 2)
  have h3 := ((hasDerivAt_id b).fun_pow 3).const_mul ((20 * a ^ 3 - 100 * a ^ 2 - 110 * a - 23) / 3)
  have h4 := ((hasDerivAt_id b).fun_pow 2).const_mul
    ((-10 * a ^ 4 + 100 * a ^ 3 + 220 * a ^ 2 + 115 * a + 13) / 2)
  have h5 := (hasDerivAt_id b).const_mul (a * (2 * a ^ 4 - 50 * a ^ 3 - 220 * a ^ 2 - 230 * a - 65))
  have h6 := (Real.hasDerivAt_log hb).const_mul (10 * a ^ 2 * (a + 1) * (a ^ 2 + 10 * a + 13))
  have h7 := ((hasDerivAt_id b).inv hb).const_mul (a ^ 3 * (22 * a ^ 2 + 115 * a + 130))
  have h8 := (((hasDerivAt_id b).inv hb).fun_pow 2).const_mul (-a ^ 4 * (23 * a + 65) / 2)
  have h9 := (((hasDerivAt_id b).inv hb).fun_pow 3).const_mul (13 * a ^ 5 / 3)
  have hsum := (((((h0.fun_add h1).fun_add h2).fun_add h3).fun_add h4).fun_add h5).fun_add h6
  convert ((hsum.fun_add h7).fun_add h8).fun_add h9 using 1
  · rfl
  · norm_num
    field_simp
    ring

/-- The nonnegative density in Appendix A's exact remainder. -/
noncomputable def kernelRemainderDensity (a v : ℝ) : ℝ :=
  let b := 1 + v * (a - 1)
  v * (1 - v) ^ 5 * (2 * b ^ 3 + 12 * b ^ 2 - 10 * b + 13) / b ^ 4

private theorem affine_scale_pos (a v : ℝ) (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < 1 + v * (a - 1) := by
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvpos : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    have hva := mul_pos hvpos ha
    nlinarith [hv.2]

/-- The remainder density is continuous across the whole unit interval. -/
theorem continuousOn_kernelRemainderDensity (a : ℝ) (ha : 0 < a) :
    ContinuousOn (kernelRemainderDensity a) (Icc (0 : ℝ) 1) := by
  unfold kernelRemainderDensity
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro v hv
    exact pow_ne_zero _ (ne_of_gt (affine_scale_pos a v ha hv))

/-- Nonnegativity of the remainder density. -/
theorem kernelRemainderDensity_nonneg (a v : ℝ) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) 1) : 0 ≤ kernelRemainderDensity a v := by
  have hb := affine_scale_pos a v ha hv
  have hpoly := kernel_remainder_cubic_pos _ hb
  unfold kernelRemainderDensity
  exact div_nonneg (mul_nonneg (mul_nonneg hv.1 (pow_nonneg (by linarith [hv.2]) 5))
    (le_of_lt hpoly)) (le_of_lt (pow_pos hb 4))

private theorem hasDerivAt_scaled_remainderPrimitive (a v : ℝ)
    (ha : 0 < a) (ha1 : a ≠ 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun w : ℝ => remainderPrimitive a (1 + w * (a - 1)) / (a - 1) ^ 7)
      (kernelRemainderDensity a v) v := by
  have hb := affine_scale_pos a v ha hv
  have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have h := ((hasDerivAt_remainderPrimitive a _ (ne_of_gt hb)).comp v
    (((hasDerivAt_id v).mul_const (a - 1)).const_add 1)).div_const ((a - 1) ^ 7)
  convert h using 1
  · rfl
  · unfold kernelRemainderDensity
    dsimp only
    field_simp
    ring

/-- Direct evaluation of the finite rational integral used for the remainder. -/
private theorem integral_kernelRemainderDensity (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    (∫ v in (0 : ℝ)..1, kernelRemainderDensity a v) =
      (remainderPrimitive a a - remainderPrimitive a 1) / (a - 1) ^ 7 := by
  have hi : IntervalIntegrable (kernelRemainderDensity a) volume 0 1 :=
    (continuousOn_kernelRemainderDensity a ha).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have hd : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun w : ℝ => remainderPrimitive a (1 + w * (a - 1)) / (a - 1) ^ 7)
      (kernelRemainderDensity a v) v := by
    intro v hv
    apply hasDerivAt_scaled_remainderPrimitive a v ha ha1
    simpa using hv
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert h using 1
  simp [sub_div]

/-- The exact positive remainder displayed in Appendix A. Its proof evaluates
the rational integral directly using an explicit antiderivative. -/
theorem kernel_remainder_identity (a : ℝ) (ha : 0 < a) :
    J a - 2 * (9 - a) / (15 * (a + 1)) =
      (2 * (a - 1) ^ 2 / (5 * (a + 1))) *
        ∫ v in (0 : ℝ)..1, kernelRemainderDensity a v := by
  by_cases ha1 : a = 1
  · subst a
    rw [J_one]
    norm_num
  · rw [J_closed_form a ha ha1, integral_kernelRemainderDensity a ha ha1]
    unfold remainderPrimitive
    have ham : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
    have hap : a + 1 ≠ 0 := by linarith
    norm_num
    field_simp
    ring

/-- The remainder integral is strictly positive for every positive scale. -/
theorem integral_kernelRemainderDensity_pos (a : ℝ) (ha : 0 < a) :
    0 < ∫ v in (0 : ℝ)..1, kernelRemainderDensity a v := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuousOn_kernelRemainderDensity a ha).intervalIntegrable_of_Icc (by norm_num))
    _ (by norm_num)
  intro v hv
  have hb := affine_scale_pos a v ha ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hpoly := kernel_remainder_cubic_pos _ hb
  unfold kernelRemainderDensity
  exact div_pos (mul_pos (mul_pos hv.1 (pow_pos (by linarith [hv.2]) 5))
    hpoly) (pow_pos hb 4)

/-- The sharp kernel estimate is strict away from the uniform scale. -/
theorem kernel_bound_strict (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    2 * (9 - a) / (15 * (a + 1)) < J a := by
  have hrem := kernel_remainder_identity a ha
  have hint := integral_kernelRemainderDensity_pos a ha
  have hsq : 0 < (a - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ha1)
  have hcoeff : 0 < 2 * (a - 1) ^ 2 / (5 * (a + 1)) := by positivity
  have hpos := mul_pos hcoeff hint
  linarith

/-- Appendix A's sharp kernel inequality. -/
theorem kernel_bound (a : ℝ) (ha : 0 < a) :
    2 * (9 - a) / (15 * (a + 1)) ≤ J a := by
  by_cases ha1 : a = 1
  · subst a
    exact le_of_eq kernel_bound_one.symm
  · exact le_of_lt (kernel_bound_strict a ha ha1)

/-- Equality in the sharp kernel inequality occurs only at scale one. -/
theorem kernel_bound_eq_iff (a : ℝ) (ha : 0 < a) :
    J a = 2 * (9 - a) / (15 * (a + 1)) ↔ a = 1 := by
  constructor
  · intro heq
    by_contra ha1
    exact (ne_of_gt (kernel_bound_strict a ha ha1)) heq
  · intro ha1
    subst a
    exact kernel_bound_one

/-- The equivalent form used when averaging over a probability mixture. -/
theorem kernel_bound_mixture_form (a : ℝ) (ha : 0 < a) :
    (13 / 15 : ℝ) - a / 3 + (a - 1) ^ 2 / (3 * (a + 1)) ≤ J a := by
  have heq : (13 / 15 : ℝ) - a / 3 + (a - 1) ^ 2 / (3 * (a + 1)) =
      2 * (9 - a) / (15 * (a + 1)) := by
    have hap : a + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [heq]
  exact kernel_bound a ha

end Curvature
end EntropyConstrainedMissingMass
