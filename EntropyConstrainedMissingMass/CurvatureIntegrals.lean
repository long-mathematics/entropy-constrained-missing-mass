import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Integral definitions and the uniform entropy-curvature calculation

The manuscript's integrals from zero to infinity are Lebesgue integrals over
`Ioi 0`. Including the endpoint zero gives the same integral, since Lebesgue
measure has no atom there. Definitions are total; convergence is asserted
separately rather than silently included in a definition.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- The cubic denominator from the three-coordinate geometry. -/
def D (x y z s : ℝ) : ℝ := (s + x) * (s + y) * (s + z)

noncomputable def I0 (x y z : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), 1 / D x y z s

noncomputable def I1 (x y z : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s / D x y z s

noncomputable def m (x y z : ℝ) : ℝ := I1 x y z / I0 x y z

noncomputable def K (x y z : ℝ) : ℝ :=
  (1 / I0 x y z) * ∫ s in Ioi (0 : ℝ), (s - m x y z) ^ 2 / (D x y z s) ^ 2

/-- Adding the zero endpoint does not change the improper integral. -/
theorem integral_Ici_zero_eq (f : ℝ → ℝ) :
    (∫ s in Ici (0 : ℝ), f s) = ∫ s in Ioi (0 : ℝ), f s :=
  integral_Ici_eq_integral_Ioi

/-- The shifted real-power integral, evaluated by the improper FTC. -/
theorem integral_add_rpow (a p : ℝ) (ha : 0 < a) (hp : p < -1) :
    (∫ s in Ioi (0 : ℝ), (s + a) ^ p) = -a ^ (p + 1) / (p + 1) := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt
      (fun v : ℝ => (v + a) ^ (p + 1) / (p + 1)) ((s + a) ^ p) s := by
    intro s hs
    have hsa : id s + a ≠ 0 := by linarith [mem_Ici.mp hs, id_eq s]
    convert (((hasDerivAt_id s).add_const a).rpow_const (p := p + 1)
      (Or.inl hsa)).div_const (p + 1) using 1 <;>
      simp [show p + 1 ≠ 0 by linarith, mul_comm]
  have ht : Tendsto (fun s : ℝ => (s + a) ^ (p + 1) / (p + 1))
      atTop (𝓝 (0 / (p + 1))) := by
    rw [← neg_neg (p + 1)]
    exact ((tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ a tendsto_id)).div_const _
  have hi := integrableOn_add_rpow_Ioi_of_lt hp (by linarith : -a < (0 : ℝ))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht using 1
  simp [neg_div]

/-- Integrability of every shifted inverse power with exponent at least two. -/
theorem integrableOn_inv_add_pow (a : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun s : ℝ => 1 / (s + a) ^ (n + 2)) (Ioi (0 : ℝ)) := by
  have hn : -((n + 2 : ℕ) : ℝ) < -1 := by push_cast; linarith
  refine (integrableOn_add_rpow_Ioi_of_lt hn (by linarith : -a < (0 : ℝ))).congr_fun
    (fun s hs => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_neg (by linarith [mem_Ioi.mp hs]), Real.rpow_natCast, one_div]

/-- A reusable exact value for shifted inverse powers. -/
theorem integral_inv_add_pow (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∫ s in Ioi (0 : ℝ), 1 / (s + a) ^ (n + 2)) =
      1 / (((n : ℝ) + 1) * a ^ (n + 1)) := by
  have hn : -((n + 2 : ℕ) : ℝ) < -1 := by push_cast; linarith
  have heq : (∫ s in Ioi (0 : ℝ), 1 / (s + a) ^ (n + 2)) =
      ∫ s in Ioi (0 : ℝ), (s + a) ^ (-((n + 2 : ℕ) : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [Real.rpow_neg (by linarith [mem_Ioi.mp hs]), Real.rpow_natCast, one_div]
  rw [heq, integral_add_rpow a _ ha hn]
  have hexp : -((n + 2 : ℕ) : ℝ) + 1 = -((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_neg (le_of_lt ha), Real.rpow_natCast]
  push_cast
  field_simp

/-- The cubic denominator on the uniform diagonal. -/
theorem D_uniform (a s : ℝ) : D a a a s = (s + a) ^ 3 := by
  unfold D
  ring

/-- The first integral in Appendix A's uniform calculation. -/
theorem I0_uniform (a : ℝ) (ha : 0 < a) : I0 a a a = 1 / (2 * a ^ 2) := by
  unfold I0
  simp_rw [D_uniform]
  convert integral_inv_add_pow a ha 1 using 1
  norm_num

/-- The second integral in Appendix A's uniform calculation. -/
theorem I1_uniform (a : ℝ) (ha : 0 < a) : I1 a a a = 1 / (2 * a) := by
  have hi2 := integrableOn_inv_add_pow a ha 0
  have hi3 := integrableOn_inv_add_pow a ha 1
  have heq : I1 a a a =
      ∫ s in Ioi (0 : ℝ), (1 / (s + a) ^ 2 - a * (1 / (s + a) ^ 3)) := by
    unfold I1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [D_uniform]
    have hsa : s + a ≠ 0 := by linarith [mem_Ioi.mp hs]
    field_simp
    ring
  rw [heq, integral_sub hi2 (hi3.const_mul a), integral_const_mul]
  rw [integral_inv_add_pow a ha 0, integral_inv_add_pow a ha 1]
  norm_num
  field_simp
  ring

/-- The mean parameter equals the common atom size. -/
theorem m_uniform (a : ℝ) (ha : 0 < a) : m a a a = a := by
  unfold m
  rw [I0_uniform a ha, I1_uniform a ha]
  field_simp

/-- The numerator integral in the uniform curvature calculation. -/
theorem integral_uniform_curvature_numerator (a : ℝ) (ha : 0 < a) :
    (∫ s in Ioi (0 : ℝ), (s - a) ^ 2 / ((s + a) ^ 3) ^ 2) =
      2 / (15 * a ^ 3) := by
  have hi4 := integrableOn_inv_add_pow a ha 2
  have hi5 := integrableOn_inv_add_pow a ha 3
  have hi6 := integrableOn_inv_add_pow a ha 4
  have heq : (∫ s in Ioi (0 : ℝ), (s - a) ^ 2 / ((s + a) ^ 3) ^ 2) =
      ∫ s in Ioi (0 : ℝ),
        (1 / (s + a) ^ 4 - (4 * a) * (1 / (s + a) ^ 5) +
          (4 * a ^ 2) * (1 / (s + a) ^ 6)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hsa : s + a ≠ 0 := by linarith [mem_Ioi.mp hs]
    field_simp
    ring
  rw [heq, integral_add (hi4.fun_sub (hi5.const_mul (4 * a))) (hi6.const_mul (4 * a ^ 2)),
    integral_sub hi4 (hi5.const_mul (4 * a)), integral_const_mul, integral_const_mul]
  rw [integral_inv_add_pow a ha 2, integral_inv_add_pow a ha 3,
    integral_inv_add_pow a ha 4]
  norm_num
  field_simp
  ring

/-- Appendix A's exact uniform-triple curvature value. -/
theorem K_uniform (a : ℝ) (ha : 0 < a) : K a a a = 4 / (15 * a) := by
  unfold K
  rw [I0_uniform a ha, m_uniform a ha]
  simp_rw [D_uniform]
  rw [integral_uniform_curvature_numerator a ha]
  field_simp
  ring

/-- Convergence of the uniform first-moment integral. -/
theorem integrableOn_uniform_first_moment (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s / (s + a) ^ 3) (Ioi (0 : ℝ)) := by
  refine ((integrableOn_inv_add_pow a ha 0).fun_sub
    ((integrableOn_inv_add_pow a ha 1).const_mul a)).congr_fun
      (fun s hs => ?_) measurableSet_Ioi
  dsimp only
  have hsa : s + a ≠ 0 := by linarith [mem_Ioi.mp hs]
  field_simp
  ring

/-- Positivity of the geometric denominator on the integration domain. -/
theorem D_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (s : ℝ) (hs : 0 ≤ s) : 0 < D x y z s := by
  unfold D
  positivity

/-- A common lower bound for the cubic factors. -/
theorem D_ge_uniform (x y z c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (hcx : c ≤ x) (hcy : c ≤ y) (hcz : c ≤ z) :
    (s + c) ^ 3 ≤ D x y z s := by
  have hsc : 0 ≤ s + c := by positivity
  have hsx : 0 ≤ s + x := by linarith
  have hsy : 0 ≤ s + y := by linarith
  have hsz : 0 ≤ s + z := by linarith
  have hxy : (s + c) * (s + c) ≤ (s + x) * (s + y) :=
    mul_le_mul (by linarith) (by linarith) hsc hsx
  have hxyz := mul_le_mul hxy (by linarith : s + c ≤ s + z)
    hsc (mul_nonneg hsx hsy)
  simpa [D, pow_succ] using hxyz

/-- Convergence of I0 for every positive triple. -/
theorem integrableOn_I0 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => 1 / D x y z s) (Ioi (0 : ℝ)) := by
  let c := min x (min y z)
  have hc : 0 < c := lt_min hx (lt_min hy hz)
  have hcx : c ≤ x := min_le_left _ _
  have hcy : c ≤ y := (min_le_right _ _).trans (min_le_left _ _)
  have hcz : c ≤ z := (min_le_right _ _).trans (min_le_right _ _)
  have hmeas : Measurable (fun s : ℝ => 1 / D x y z s) := by
    unfold D
    fun_prop
  refine (integrableOn_inv_add_pow c hc 1).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := le_of_lt (mem_Ioi.mp hs)
  have hd := D_pos x y z hx hy hz s hs0
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
  exact one_div_le_one_div_of_le (by positivity)
    (D_ge_uniform x y z c s hc hs0 hcx hcy hcz)

/-- Convergence of I1 for every positive triple. -/
theorem integrableOn_I1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => s / D x y z s) (Ioi (0 : ℝ)) := by
  let c := min x (min y z)
  have hc : 0 < c := lt_min hx (lt_min hy hz)
  have hcx : c ≤ x := min_le_left _ _
  have hcy : c ≤ y := (min_le_right _ _).trans (min_le_left _ _)
  have hcz : c ≤ z := (min_le_right _ _).trans (min_le_right _ _)
  have hmeas : Measurable (fun s : ℝ => s / D x y z s) := by
    unfold D
    fun_prop
  refine (integrableOn_uniform_first_moment c hc).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := le_of_lt (mem_Ioi.mp hs)
  have hd := D_pos x y z hx hy hz s hs0
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs0 (le_of_lt hd))]
  exact div_le_div_of_nonneg_left hs0 (by positivity)
    (D_ge_uniform x y z c s hc hs0 hcx hcy hcz)

private theorem integral_Ioi_pos {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi (0 : ℝ))) (hp : ∀ s, 0 < s → 0 < f s) :
    0 < ∫ s in Ioi (0 : ℝ), f s := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact le_of_lt (hp s hs)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hi]
  have hsupp : Function.support f ∩ Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    apply inter_eq_right.mpr
    intro s hs
    exact ne_of_gt (hp s hs)
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- I0 is strictly positive, so the mean's denominator does not vanish. -/
theorem I0_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < I0 x y z := by
  apply integral_Ioi_pos (integrableOn_I0 x y z hx hy hz)
  intro s hs
  exact one_div_pos.mpr (D_pos x y z hx hy hz s (le_of_lt hs))

/-- I1 is strictly positive. -/
theorem I1_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < I1 x y z := by
  apply integral_Ioi_pos (integrableOn_I1 x y z hx hy hz)
  intro s hs
  exact div_pos hs (D_pos x y z hx hy hz s (le_of_lt hs))

/-- The integral-defined mean is positive for every positive triple. -/
theorem m_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < m x y z :=
  div_pos (I1_pos x y z hx hy hz) (I0_pos x y z hx hy hz)

/-- Convergence of the curvature numerator for any real center. -/
theorem integrableOn_curvature_numerator (x y z q : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => (s - q) ^ 2 / (D x y z s) ^ 2) (Ioi (0 : ℝ)) := by
  let c := min x (min y z)
  have hc : 0 < c := lt_min hx (lt_min hy hz)
  have hcx : c ≤ x := min_le_left _ _
  have hcy : c ≤ y := (min_le_right _ _).trans (min_le_left _ _)
  have hcz : c ≤ z := (min_le_right _ _).trans (min_le_right _ _)
  let C : ℝ := 1 + |q| / c
  have hC : 1 ≤ C := by
    have : 0 ≤ |q| / c := div_nonneg (abs_nonneg _) (le_of_lt hc)
    dsimp [C]
    linarith
  have hCc : C * c = c + |q| := by dsimp [C]; field_simp
  have hmeas : Measurable (fun s : ℝ => (s - q) ^ 2 / (D x y z s) ^ 2) := by
    unfold D
    fun_prop
  refine ((integrableOn_inv_add_pow c hc 2).const_mul (C ^ 2)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := le_of_lt (mem_Ioi.mp hs)
  have hsc : 0 < s + c := by positivity
  have hd := D_pos x y z hx hy hz s hs0
  have habs : |s - q| ≤ C * (s + c) := by
    have htri : |s - q| ≤ s + |q| := by
      simpa only [abs_of_nonneg hs0] using abs_sub s q
    have hCs : s ≤ C * s := by nlinarith
    nlinarith
  have hnum : (s - q) ^ 2 ≤ (C * (s + c)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (s - q)) habs 2
  have hden : ((s + c) ^ 3) ^ 2 ≤ (D x y z s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (D_ge_uniform x y z c s hc hs0 hcx hcy hcz) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    (s - q) ^ 2 / (D x y z s) ^ 2 ≤
        (C * (s + c)) ^ 2 / ((s + c) ^ 3) ^ 2 :=
      div_le_div₀ (sq_nonneg _) hnum (by positivity) hden
    _ = C ^ 2 * (1 / (s + c) ^ (2 + 2)) := by field_simp

/-- The curvature numerator has a strictly positive integral: its only possible
zero inside the domain is the single point equal to the center. -/
theorem integral_curvature_numerator_pos (x y z q : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < ∫ s in Ioi (0 : ℝ), (s - q) ^ 2 / (D x y z s) ^ 2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s : ℝ => (s - q) ^ 2 / (D x y z s) ^ 2) :=
    Filter.Eventually.of_forall (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg
    (integrableOn_curvature_numerator x y z q hx hy hz)]
  have hsupp : Function.support (fun s : ℝ => (s - q) ^ 2 / (D x y z s) ^ 2) ∩
      Ioi (0 : ℝ) = Ioi (0 : ℝ) \ {q} := by
    ext s
    by_cases hs : 0 < s
    · have hd : D x y z s ≠ 0 := ne_of_gt (D_pos x y z hx hy hz s (le_of_lt hs))
      simp [Function.mem_support, mem_Ioi, hs, hd, sub_ne_zero]
    · simp [mem_Ioi, hs]
  rw [hsupp, measure_sdiff_null (measure_singleton q), Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- The integral-defined curvature is strictly positive for every positive triple. -/
theorem K_pos (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    0 < K x y z :=
  mul_pos (one_div_pos.mpr (I0_pos x y z hx hy hz))
    (integral_curvature_numerator_pos x y z (m x y z) hx hy hz)

end Curvature
end EntropyConstrainedMissingMass
