import EntropyConstrainedMissingMass.RepeatedSize
import EntropyConstrainedMissingMass.QuadraticPathCalculus
import EntropyConstrainedMissingMass.EmbeddedPerturbation
import EntropyConstrainedMissingMass.GenericFiniteLocalMax
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Four-coordinate quadratic perturbations used in the repeated-size criterion. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology

def repeatedFourBase (x y : ℝ) : Fin 4 → ℝ := ![x, x, y, y]

def repeatedFourVelocity (left : Bool) : Fin 4 → ℝ :=
  if left then ![1, -1, 0, 0] else ![0, 0, 1, -1]

def repeatedFourAcceleration (c : ℝ) : Fin 4 → ℝ := ![c, c, -c, -c]

def repeatedFourPath (x y c : ℝ) (left : Bool) (ε : ℝ) (i : Fin 4) : ℝ :=
  repeatedFourBase x y i + repeatedFourVelocity left i * ε + repeatedFourAcceleration c i * ε ^ 2

@[simp] theorem repeatedFourPath_zero (x y c : ℝ) (left : Bool) :
    repeatedFourPath x y c left 0 = repeatedFourBase x y := by
  ext i
  simp [repeatedFourPath]

theorem repeatedFourPath_sum (x y c ε : ℝ) (left : Bool) :
    ∑ i, repeatedFourPath x y c left ε i = ∑ i, repeatedFourBase x y i := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourPath, repeatedFourBase,
    repeatedFourVelocity, repeatedFourAcceleration] <;> ring

theorem continuous_repeatedFourPath (x y c : ℝ) (left : Bool) :
    Continuous (repeatedFourPath x y c left) := by
  unfold repeatedFourPath
  fun_prop

theorem repeatedFourPath_eventually_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (c : ℝ) (left : Bool) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ i, 0 ≤ repeatedFourPath x y c left ε i := by
  apply Filter.eventually_all.mpr
  intro i
  have hi : 0 < repeatedFourBase x y i := by
    fin_cases i <;> simp [repeatedFourBase] <;> assumption
  have ht : Tendsto (fun ε => repeatedFourPath x y c left ε i) (𝓝 0)
      (𝓝 (repeatedFourBase x y i)) := by
    simpa [Function.comp_def] using
      ((continuous_apply i).comp (continuous_repeatedFourPath x y c left)).tendsto 0
  exact (ht.eventually (eventually_gt_nhds hi)).mono (fun _ h => h.le)

theorem repeatedFour_first_jet (f : ℝ → ℝ) (x y : ℝ) (left : Bool) :
    ∑ i, repeatedFourVelocity left i * deriv f (repeatedFourBase x y i) = 0 := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourVelocity, repeatedFourBase]

theorem repeatedFour_second_jet (f : ℝ → ℝ) (x y c : ℝ) (left : Bool) :
    (∑ i, ((repeatedFourVelocity left i) ^ 2 * deriv (deriv f) (repeatedFourBase x y i) +
      2 * repeatedFourAcceleration c i * deriv f (repeatedFourBase x y i))) =
      2 * (if left then deriv (deriv f) x else deriv (deriv f) y) +
        4 * c * (deriv f x - deriv f y) := by
  cases left <;> simp [Fin.sum_univ_succ, repeatedFourVelocity, repeatedFourBase,
    repeatedFourAcceleration] <;> ring

/-- A continuous inequality holding strictly to the left also holds at the endpoint. -/
theorem nonpos_at_of_forall_lt {F : ℝ → ℝ} {a : ℝ} (hF : ContinuousAt F a)
    (h : ∀ c < a, F c ≤ 0) : F a ≤ 0 := by
  apply le_of_tendsto (hF.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto F (𝓝[<] a) (𝓝 (F a)))
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact h c hc

theorem repeatedFourBase_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (i : Fin 4) :
    0 < repeatedFourBase x y i := by
  fin_cases i <;> simp [repeatedFourBase] <;> assumption

theorem hasDerivAt_repeatedFour_sum {f : ℝ → ℝ} (x y c : ℝ) (left : Bool)
    (hf : ∀ i, HasDerivAt f (deriv f (repeatedFourBase x y i)) (repeatedFourBase x y i)) :
    HasDerivAt (fun ε => ∑ i, f (repeatedFourPath x y c left ε i)) 0 0 := by
  have hd := hasDerivAt_sum_quadraticPath (repeatedFourBase x y)
    (repeatedFourVelocity left) (repeatedFourAcceleration c) (fun i => deriv f (repeatedFourBase x y i)) hf
  rw [repeatedFour_first_jet] at hd
  exact hd

theorem hasDerivAt_deriv_repeatedFour_sum {f : ℝ → ℝ} (x y c : ℝ) (left : Bool)
    (hf : ∀ i, ∀ᶠ u in 𝓝 (repeatedFourBase x y i), HasDerivAt f (deriv f u) u)
    (hdf : ∀ i, HasDerivAt (deriv f) (deriv (deriv f) (repeatedFourBase x y i))
      (repeatedFourBase x y i)) :
    HasDerivAt (deriv (fun ε => ∑ i, f (repeatedFourPath x y c left ε i)))
      (2 * (if left then deriv (deriv f) x else deriv (deriv f) y) +
        4 * c * (deriv f x - deriv f y)) 0 := by
  have hd := hasDerivAt_deriv_sum_quadraticPath (repeatedFourBase x y)
    (repeatedFourVelocity left) (repeatedFourAcceleration c)
    (fun i => deriv (deriv f) (repeatedFourBase x y i)) hf hdf
  rw [repeatedFour_second_jet] at hd
  exact hd

theorem hasDerivAt_deriv_negMulLog_at_pos {a : ℝ} (ha : 0 < a) :
    HasDerivAt (deriv Real.negMulLog) (-a⁻¹) a := by
  have heq : deriv Real.negMulLog =ᶠ[𝓝 a] fun u => -Real.log u - 1 := by
    filter_upwards [eventually_ne_nhds (ne_of_gt ha)] with u hu
    exact Real.deriv_negMulLog hu
  exact ((Real.hasDerivAt_log (ne_of_gt ha)).neg.sub_const 1).congr_of_eventuallyEq heq

theorem eventually_hasDerivAt_negMulLog_at_pos {a : ℝ} (ha : 0 < a) :
    ∀ᶠ u in 𝓝 a, HasDerivAt Real.negMulLog (deriv Real.negMulLog u) u := by
  filter_upwards [eventually_ne_nhds (ne_of_gt ha)] with u hu
  exact (Real.differentiableAt_negMulLog hu).hasDerivAt

theorem repeatedFour_entropy_first_deriv {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (c : ℝ) (left : Bool) :
    HasDerivAt (fun ε => ∑ i, Real.negMulLog (repeatedFourPath x y c left ε i)) 0 0 :=
  hasDerivAt_repeatedFour_sum x y c left (fun i =>
    (Real.differentiableAt_negMulLog (ne_of_gt (repeatedFourBase_pos hx hy i))).hasDerivAt)

theorem repeatedFour_entropy_second_deriv {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (c : ℝ) (left : Bool) :
    HasDerivAt (deriv (fun ε => ∑ i, Real.negMulLog (repeatedFourPath x y c left ε i)))
      (-2 / (if left then x else y) + 4 * c * (Real.log y - Real.log x)) 0 := by
  have hd := hasDerivAt_deriv_repeatedFour_sum x y c left
    (fun i => eventually_hasDerivAt_negMulLog_at_pos (repeatedFourBase_pos hx hy i))
    (fun i => (hasDerivAt_deriv_negMulLog_at_pos (repeatedFourBase_pos hx hy i)).differentiableAt.hasDerivAt)
  convert hd using 1
  rw [(hasDerivAt_deriv_negMulLog_at_pos hx).deriv, (hasDerivAt_deriv_negMulLog_at_pos hy).deriv,
    Real.deriv_negMulLog (ne_of_gt hx), Real.deriv_negMulLog (ne_of_gt hy)]
  cases left <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem repeatedFour_entropy_localMax {x y : ℝ} (hx : 0 < x) (hxy : x < y)
    (c : ℝ) (left : Bool)
    (hc : c < 1 / (2 * (if left then x else y) * (Real.log y - Real.log x))) :
    IsLocalMax (fun ε => ∑ i, Real.negMulLog (repeatedFourPath x y c left ε i)) 0 := by
  have hy := hx.trans hxy
  have hL : 0 < Real.log y - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxy)
  have hu : 0 < (if left then x else y) := by cases left <;> assumption
  have hmul := (lt_div_iff₀ (mul_pos (mul_pos (by norm_num) hu) hL)).mp hc
  have hd := repeatedFour_entropy_second_deriv hx hy c left
  have hfirst := repeatedFour_entropy_first_deriv hx hy c left
  apply isLocalMax_of_deriv_deriv_neg _ hfirst.deriv hfirst.continuousAt
  rw [hd.deriv]
  have heq : -2 / (if left then x else y) + 4 * c * (Real.log y - Real.log x) =
      (-2 + 4 * c * (Real.log y - Real.log x) * (if left then x else y)) /
        (if left then x else y) := by field_simp
  rw [heq]
  exact div_neg_of_neg_of_pos (by nlinarith) hu

/-- The genuine four-coordinate mass and upper-entropy constraint. -/
def repeatedFourConstraint (x y : ℝ) : Set (Fin 4 → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = ∑ i, repeatedFourBase x y i) ∧
    (∑ i, Real.negMulLog (v i)) ≤ ∑ i, Real.negMulLog (repeatedFourBase x y i)}

theorem localMax_repeatedFourPath {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hm : IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y))
    (c : ℝ) (left : Bool)
    (hent : IsLocalMax (fun ε => ∑ i, Real.negMulLog (repeatedFourPath x y c left ε i)) 0) :
    IsLocalMax (fun ε => ∑ i, f (repeatedFourPath x y c left ε i)) 0 := by
  have hlim : Tendsto (repeatedFourPath x y c left) (𝓝 0) (𝓝 (repeatedFourBase x y)) := by
    simpa using (continuous_repeatedFourPath x y c left).tendsto 0
  have hmem : ∀ᶠ ε : ℝ in 𝓝 0, repeatedFourPath x y c left ε ∈ repeatedFourConstraint x y := by
    filter_upwards [repeatedFourPath_eventually_nonneg hx hy c left, hent] with ε hn he
    exact ⟨hn, repeatedFourPath_sum x y c ε left, by simpa only [repeatedFourPath_zero] using he⟩
  have ht : Tendsto (repeatedFourPath x y c left) (𝓝 0)
      (𝓝[repeatedFourConstraint x y] (repeatedFourBase x y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hmem⟩
  change ∀ᶠ ε : ℝ in 𝓝 0, (∑ i, f (repeatedFourPath x y c left ε i)) ≤
    ∑ i, f (repeatedFourPath x y c left 0 i)
  simpa only [repeatedFourPath_zero] using ht.eventually hm

theorem weighted_bound_of_affine_nonpos {u L A D : ℝ} (hu : 0 < u) (hL : 0 < L)
    (h : 2 * A + 4 * (1 / (2 * u * L)) * (-D) ≤ 0) : u * A ≤ D / L := by
  have hm := mul_nonpos_of_nonpos_of_nonneg h (mul_pos hu hL).le
  have heq : (2 * A + 4 * (1 / (2 * u * L)) * (-D)) * (u * L) =
      2 * (u * A * L - D) := by field_simp; ring
  rw [heq] at hm
  apply (le_div_iff₀ hL).2
  linarith

/-- The endpoint bound follows from actual entropy-feasible paths, with no multiplier premise. -/
theorem repeatedFour_weighted_endpoint_bound {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hm : IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y))
    (hf : ∀ i, ∀ᶠ u in 𝓝 (repeatedFourBase x y i), HasDerivAt f (deriv f u) u)
    (hdf : ∀ i, HasDerivAt (deriv f) (deriv (deriv f) (repeatedFourBase x y i))
      (repeatedFourBase x y i)) (left : Bool) :
    (if left then x else y) * (if left then deriv (deriv f) x else deriv (deriv f) y) ≤
      (deriv f y - deriv f x) / (Real.log y - Real.log x) := by
  have hy := hx.trans hxy
  have hL : 0 < Real.log y - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxy)
  have hu : 0 < (if left then x else y) := by cases left <;> assumption
  have hnear (c : ℝ)
      (hc : c < 1 / (2 * (if left then x else y) * (Real.log y - Real.log x))) :
      2 * (if left then deriv (deriv f) x else deriv (deriv f) y) +
        4 * c * (deriv f x - deriv f y) ≤ 0 := by
    have hmax := localMax_repeatedFourPath hx hy hm c left
      (repeatedFour_entropy_localMax hx hxy c left hc)
    have hfirst := hasDerivAt_repeatedFour_sum x y c left (fun i => (hf i).self_of_nhds)
    have hsecond := hasDerivAt_deriv_repeatedFour_sum x y c left hf hdf
    have hle := second_derivative_nonpos_of_localMax hfirst.continuousAt hmax
    rwa [hsecond.deriv] at hle
  have hcrit := nonpos_at_of_forall_lt (by fun_prop) hnear
  apply weighted_bound_of_affine_nonpos hu hL
  convert hcrit using 1
  ring

/-- The general repeated-size criterion on the four coordinates involved in its proof. -/
theorem not_localMax_repeatedFour_of_strict_quasiconvex {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hf : ∀ i, ∀ᶠ u in 𝓝 (repeatedFourBase x y i), HasDerivAt f (deriv f u) u)
    (hdf : ∀ i, HasDerivAt (deriv f) (deriv (deriv f) (repeatedFourBase x y i))
      (repeatedFourBase x y i))
    (hc : ContinuousOn (deriv f) (Icc x y)) (hd : DifferentiableOn ℝ (deriv f) (Ioo x y))
    (hq : ∀ v ∈ Ioo x y, v * deriv (deriv f) v <
      max (x * deriv (deriv f) x) (y * deriv (deriv f) y)) :
    ¬ IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y) := by
  intro hm
  apply not_both_weighted_second_derivative_bounds hx hxy hc hd hq
  exact ⟨repeatedFour_weighted_endpoint_bound hx hxy hm hf hdf true,
    repeatedFour_weighted_endpoint_bound hx hxy hm hf hdf false⟩

theorem contDiffOn_repeatedFour_data {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    (∀ i, ∀ᶠ u in 𝓝 (repeatedFourBase x y i), HasDerivAt f (deriv f u) u) ∧
    (∀ i, HasDerivAt (deriv f) (deriv (deriv f) (repeatedFourBase x y i))
      (repeatedFourBase x y i)) ∧
    ContinuousOn (deriv f) (Icc x y) ∧ DifferentiableOn ℝ (deriv f) (Ioo x y) := by
  have hd := hf.differentiableOn (by norm_num)
  have hc1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 1) := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd1 := hc1.differentiableOn (by norm_num)
  have hb (i : Fin 4) : repeatedFourBase x y i ∈ Ioo 0 1 := by
    fin_cases i <;> simp [repeatedFourBase] <;> constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [isOpen_Ioo.mem_nhds (hb i)] with u hu
    exact (hd.differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
  · intro i
    exact (hd1.differentiableAt (isOpen_Ioo.mem_nhds (hb i))).hasDerivAt
  · exact hc1.continuousOn.mono (fun u hu => ⟨hx.trans_le hu.1, hu.2.trans_lt hy1⟩)
  · exact hd1.mono (fun u hu => ⟨hx.trans hu.1, hu.2.trans hy1⟩)

/-- The four-coordinate criterion with the manuscript's usual `C²(0,1)` assumption. -/
theorem not_localMax_repeatedFour_of_contDiffOn {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hx : 0 < x) (hxy : x < y) (hy1 : y < 1)
    (hq : ∀ v ∈ Ioo x y, v * deriv (deriv f) v <
      max (x * deriv (deriv f) x) (y * deriv (deriv f) y)) :
    ¬ IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y) := by
  obtain ⟨ha, hb, hc, hd⟩ := contDiffOn_repeatedFour_data hf hx hxy hy1
  exact not_localMax_repeatedFour_of_strict_quasiconvex hx hxy ha hb hc hd hq

theorem repeatedFour_nonpos_curvature {f : ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hx : 0 < x) (hxy : x < y) (hy1 : y < 1)
    (hm : IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y)) :
    deriv (deriv f) x ≤ 0 ∧ deriv (deriv f) y ≤ 0 := by
  obtain ⟨ha, hb, _, _⟩ := contDiffOn_repeatedFour_data hf hx hxy hy1
  have hL : 0 < Real.log y - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxy)
  have hbound (left : Bool) : (if left then deriv (deriv f) x else deriv (deriv f) y) ≤ 0 := by
    have hu : 0 < (if left then x else y) := by cases left <;> simp <;> linarith
    have hmax := localMax_repeatedFourPath hx (hx.trans hxy) hm 0 left
      (repeatedFour_entropy_localMax hx hxy 0 left (by positivity))
    have hfirst := hasDerivAt_repeatedFour_sum x y 0 left (fun i => (ha i).self_of_nhds)
    have hsecond := hasDerivAt_deriv_repeatedFour_sum x y 0 left ha hb
    have hle := second_derivative_nonpos_of_localMax hfirst.continuousAt hmax
    rw [hsecond.deriv] at hle
    linarith
  exact ⟨hbound true, hbound false⟩

/-- The full scalar repeated-size criterion restricted to its four involved coordinates.
The curvature-region premise is the manuscript's condition on `J`. -/
theorem repeated_size_criterion_four {f : ℝ → ℝ} {J : Set ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, deriv (deriv f) u ≤ 0 → u ∈ J)
    (hq : ∀ x ∈ J, ∀ y ∈ J, ∀ v ∈ Ioo x y,
      v * deriv (deriv f) v < max (x * deriv (deriv f) x) (y * deriv (deriv f) y))
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    ¬ IsLocalMaxOn (fun v : Fin 4 → ℝ => ∑ i, f (v i))
      (repeatedFourConstraint x y) (repeatedFourBase x y) := by
  intro hm
  obtain ⟨hxcurv, hycurv⟩ := repeatedFour_nonpos_curvature hf hx hxy hy1 hm
  have hxJ := hJ x ⟨hx, hxy.trans hy1⟩ hxcurv
  have hyJ := hJ y ⟨hx.trans hxy, hy1⟩ hycurv
  exact not_localMax_repeatedFour_of_contDiffOn hf hx hxy hy1 (hq x hxJ y hyJ) hm

namespace ProbabilityVector
variable {ι : Type*}

theorem no_two_ordered_repeated_sizes_statistic (p : ProbabilityVector ι)
    {f : ℝ → ℝ} {J : Set ℝ} (hf : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, deriv (deriv f) u ≤ 0 → u ∈ J)
    (hq : ∀ x ∈ J, ∀ y ∈ J, ∀ v ∈ Ioo x y,
      v * deriv (deriv f) v < max (x * deriv (deriv f) x) (y * deriv (deriv f) y))
    (hm : StatisticFiniteLocalMax f p) (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hikv : p.coord i < p.coord k) : False := by
  have hik : i ≠ k := by intro he; subst k; exact (lt_irrefl _ hikv)
  have hil : i ≠ l := by intro he; subst l; rw [hklv] at hikv; exact lt_irrefl _ hikv
  have hjk : j ≠ k := by intro he; subst k; rw [hijv] at hikv; exact lt_irrefl _ hikv
  have hjl : j ≠ l := by intro he; subst l; rw [← hklv, hijv] at hikv; exact lt_irrefl _ hikv
  let e : Fin 4 ↪ ι := ⟨![i, j, k, l], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩
  have hcoord (a : Fin 4) : p.coord (e a) = repeatedFourBase (p.coord i) (p.coord k) a := by
    change p.coord (![i, j, k, l] a) = _
    fin_cases a <;> simp [repeatedFourBase, hijv, hklv]
  have hlocal := hm 4 e
  unfold finiteEntropyConstraint at hlocal
  simp only [hcoord] at hlocal
  have hy1 : p.coord k < 1 := lt_of_le_of_lt (repeated_size_le_half p k l hkl hklv) (by norm_num)
  exact repeated_size_criterion_four hf hJ hq hi hikv hy1 hlocal

/-- The repeated-size criterion on any alphabet under finite-coordinate local maximality.
The objective's summability and the manuscript's endpoint continuity are explicit;
the proof only requires the interior regularity and the finite-coordinate changes. -/
theorem repeated_size_criterion (p : ProbabilityVector ι) {f : ℝ → ℝ} {J : Set ℝ}
    (_hc : ContinuousOn f (Icc 0 1)) (hf : ContDiffOn ℝ 2 f (Ioo 0 1))
    (_hsum : Summable (fun i => f (p.coord i)))
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, deriv (deriv f) u ≤ 0 → u ∈ J)
    (hq : ∀ x ∈ J, ∀ y ∈ J, ∀ v ∈ Ioo x y,
      v * deriv (deriv f) v < max (x * deriv (deriv f) x) (y * deriv (deriv f) y))
    (hm : StatisticFiniteLocalMax f p) (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hk : 0 < p.coord k) : p.coord i = p.coord k := by
  rcases lt_trichotomy (p.coord i) (p.coord k) with hlt | heq | hgt
  · exact (no_two_ordered_repeated_sizes_statistic p hf hJ hq hm i j k l hij hkl hijv hklv hi hlt).elim
  · exact heq
  · exact (no_two_ordered_repeated_sizes_statistic p hf hJ hq hm k l i j hkl hij hklv hijv hk hgt).elim

/-- Actual ℓ¹ local maximality of a summable atom objective implies the generic criterion. -/
theorem repeated_size_criterion_of_localMax (p : ProbabilityVector ι) {f : ℝ → ℝ}
    {J : Set ℝ} {h : ℝ} (hc : ContinuousOn f (Icc 0 1)) (hf : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hsum : Summable (fun i => f (p.coord i))) (hp : p ∈ Feasible h)
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, deriv (deriv f) u ≤ 0 → u ∈ J)
    (hq : ∀ x ∈ J, ∀ y ∈ J, ∀ v ∈ Ioo x y,
      v * deriv (deriv f) v < max (x * deriv (deriv f) x) (y * deriv (deriv f) y))
    (hm : IsLocalMaxOn (fun q : ProbabilityVector ι => ∑' a, f (q.coord a)) (Feasible h) p)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hk : 0 < p.coord k) : p.coord i = p.coord k :=
  repeated_size_criterion p hc hf hsum hJ hq
    (statisticFiniteLocalMax_of_localMax p hp f hsum hm) i j k l hij hkl hijv hklv hi hk

/-- On a finite alphabet the criterion applies directly to the finite sum objective,
with no summability assumption to discharge. -/
theorem repeated_size_criterion_finite [Fintype ι] (p : ProbabilityVector ι)
    {f : ℝ → ℝ} {J : Set ℝ} {h : ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hf : ContDiffOn ℝ 2 f (Ioo 0 1)) (hp : p ∈ Feasible h)
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, deriv (deriv f) u ≤ 0 → u ∈ J)
    (hq : ∀ x ∈ J, ∀ y ∈ J, ∀ v ∈ Ioo x y,
      v * deriv (deriv f) v < max (x * deriv (deriv f) x) (y * deriv (deriv f) y))
    (hm : IsLocalMaxOn (fun q : ProbabilityVector ι => ∑ a, f (q.coord a)) (Feasible h) p)
    (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hk : 0 < p.coord k) : p.coord i = p.coord k := by
  apply repeated_size_criterion_of_localMax p hc hf (hasSum_fintype _).summable hp hJ hq
    (by simpa only [tsum_fintype] using hm) i j k l hij hkl hijv hklv hi hk

/-- The four-coordinate criterion applied to actual ℓ¹ local maximizers, on any alphabet. -/
theorem no_two_repeated_sizes_embedded (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (e : Fin 4 ↪ ι) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y)
    (hbase : (fun i => p.coord (e i)) = repeatedFourBase x y) : False := by
  have hy : 0 < y := hx.trans hxy
  have h2 : p.coord (e 2) = y := by simpa [repeatedFourBase] using congr_fun hbase 2
  have h3 : p.coord (e 3) = y := by simpa [repeatedFourBase] using congr_fun hbase 3
  have hij : e 2 ≠ e 3 := e.injective.ne (by decide : (2 : Fin 4) ≠ 3)
  have hyI : y ∈ negativeCurvatureInterval t := by
    have hi := repeated_size_mem_negativeCurvatureInterval p ht hp (e 2) (e 3) hij
      (h3.trans h2.symm) (by simpa only [h2] using hy)
    simpa only [h2] using hi
  have hfd : Differentiable ℝ (missingMassTerm t) := by unfold missingMassTerm; fun_prop
  have hdfd : Differentiable ℝ (deriv (missingMassTerm t)) := by
    have heq : deriv (missingMassTerm t) = fun u =>
        ((t : ℝ) + 1) * (1 - u) ^ t - (t : ℝ) * (1 - u) ^ (t - 1) :=
      funext (deriv_missingMassTerm t ht)
    rw [heq]
    fun_prop
  have hlocal := localMaxOn_embedded_coordinates p hp e
  have hcoord (i : Fin 4) : p.coord (e i) = repeatedFourBase x y i := congr_fun hbase i
  simp only [hcoord] at hlocal
  apply not_localMax_repeatedFour_of_strict_quasiconvex hx hxy
    (fun _ => Eventually.of_forall (fun u => (hfd u).hasDerivAt))
    (fun i => (hdfd (repeatedFourBase x y i)).hasDerivAt)
    hdfd.continuous.continuousOn hdfd.differentiableOn _ hlocal
  intro v hv
  exact weightedCurvature_strict_quasiconvex t ht hv.1 hv.2 hyI.2.1 hyI.2.2

theorem no_two_ordered_repeated_sizes (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hikv : p.coord i < p.coord k) : False := by
  have hik : i ≠ k := by intro he; subst k; exact (lt_irrefl _ hikv)
  have hil : i ≠ l := by intro he; subst l; rw [hklv] at hikv; exact lt_irrefl _ hikv
  have hjk : j ≠ k := by intro he; subst k; rw [hijv] at hikv; exact lt_irrefl _ hikv
  have hjl : j ≠ l := by intro he; subst l; rw [← hklv, hijv] at hikv; exact lt_irrefl _ hikv
  let e : Fin 4 ↪ ι := ⟨![i, j, k, l], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩
  apply no_two_repeated_sizes_embedded p ht hp e hi hikv
  funext a
  change p.coord (![i, j, k, l] a) = repeatedFourBase (p.coord i) (p.coord k) a
  fin_cases a <;> simp [repeatedFourBase, hijv, hklv]

/-- At most one distinct positive size can be repeated at an actual local maximum.
There is no finite-support assumption. -/
theorem repeated_positive_sizes_eq (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hijv : p.coord j = p.coord i) (hklv : p.coord l = p.coord k)
    (hi : 0 < p.coord i) (hk : 0 < p.coord k) : p.coord i = p.coord k := by
  rcases lt_trichotomy (p.coord i) (p.coord k) with hlt | heq | hgt
  · exact (no_two_ordered_repeated_sizes p ht hp i j k l hij hkl hijv hklv hi hlt).elim
  · exact heq
  · exact (no_two_ordered_repeated_sizes p ht hp k l i j hkl hij hklv hijv hk hgt).elim

end ProbabilityVector
end
end EntropyConstrainedMissingMass
