import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Semiring

/-! Entropy branch calculus from §5.2 of the manuscript. -/

namespace EntropyConstrainedMissingMass

noncomputable section

open Set

/-- Entropy of the exceptional mass `z` and `m` equal masses `(1-z)/m`. -/
def branchEntropy (m z : ℝ) : ℝ :=
  -z * Real.log z - (1 - z) * Real.log ((1 - z) / m)

theorem branchEntropy_eq_negMulLog {m : ℝ} (hm : m ≠ 0) (z : ℝ) :
    branchEntropy m z = Real.negMulLog z + Real.negMulLog (1 - z) +
      (1 - z) * Real.log m := by
  by_cases hz : 1 - z = 0
  · simp [branchEntropy, Real.negMulLog, hz]
  · rw [branchEntropy, Real.log_div hz hm]
    simp only [Real.negMulLog]
    ring

theorem continuous_branchEntropy {m : ℝ} (hm : m ≠ 0) :
    Continuous (branchEntropy m) := by
  change Continuous (fun z => branchEntropy m z)
  simp_rw [branchEntropy_eq_negMulLog hm]
  fun_prop

@[simp] theorem branchEntropy_zero (m : ℝ) : branchEntropy m 0 = Real.log m := by
  simp [branchEntropy, Real.log_inv]

@[simp] theorem branchEntropy_one (m : ℝ) : branchEntropy m 1 = 0 := by
  simp [branchEntropy]

theorem branchEntropy_uniform {m : ℝ} (hm : 0 < m) :
    branchEntropy m (1 / (m + 1)) = Real.log (m + 1) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hm1 : m + 1 ≠ 0 := by positivity
  have hq : (1 - 1 / (m + 1)) / m = 1 / (m + 1) := by field_simp; ring
  rw [branchEntropy, hq]
  simp only [one_div, Real.log_inv]
  ring

theorem hasDerivAt_branchEntropy {m z : ℝ} (hm : 0 < m)
    (hz : 0 < z) (hz1 : z < 1) :
    HasDerivAt (branchEntropy m) (Real.log ((1 - z) / (m * z))) z := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : 1 - z ≠ 0 := by linarith
  have h := ((Real.hasDerivAt_negMulLog hz0).add
    ((Real.hasDerivAt_negMulLog h1z).comp z ((hasDerivAt_id z).const_sub 1))).add
      (((hasDerivAt_id z).const_sub 1).mul_const (Real.log m))
  have heq : branchEntropy m = fun x => Real.negMulLog x + Real.negMulLog (1 - x) +
      (1 - x) * Real.log m := funext (branchEntropy_eq_negMulLog hm0)
  rw [heq]
  convert h using 1
  · rfl
  · rw [Real.log_div h1z (mul_ne_zero hm0 hz0), Real.log_mul hm0 hz0]
    ring

theorem deriv_branchEntropy {m z : ℝ} (hm : 0 < m) (hz : 0 < z) (hz1 : z < 1) :
    deriv (branchEntropy m) z = Real.log ((1 - z) / (m * z)) :=
  (hasDerivAt_branchEntropy hm hz hz1).deriv

/-- The light entropy branch is strictly increasing, including its endpoints. -/
theorem strictMonoOn_branchEntropy {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (branchEntropy m) (Icc 0 (1 / (m + 1))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_branchEntropy (ne_of_gt hm)).continuousOn
  intro z hz
  rw [interior_Icc] at hz
  have hm1 : 0 < m + 1 := by positivity
  have htop : 1 / (m + 1) < 1 := (div_lt_one hm1).2 (by linarith)
  rw [deriv_branchEntropy hm hz.1 (lt_trans hz.2 htop)]
  apply Real.log_pos
  apply (one_lt_div (mul_pos hm hz.1)).2
  have hzmul := (lt_div_iff₀ hm1).1 hz.2
  nlinarith

/-- The heavy entropy branch is strictly decreasing, including its endpoints. -/
theorem strictAntiOn_branchEntropy {m : ℝ} (hm : 0 < m) :
    StrictAntiOn (branchEntropy m) (Icc (1 / (m + 1)) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_branchEntropy (ne_of_gt hm)).continuousOn
  intro z hz
  rw [interior_Icc] at hz
  have hm1 : 0 < m + 1 := by positivity
  have hz0 : 0 < z := lt_trans (by positivity : 0 < 1 / (m + 1)) hz.1
  rw [deriv_branchEntropy hm hz0 hz.2]
  apply Real.log_neg (div_pos (sub_pos.mpr hz.2) (mul_pos hm hz0))
  apply (div_lt_one (mul_pos hm hz0)).2
  have hzmul := (div_lt_iff₀ hm1).1 hz.1
  nlinarith

/-- Every entropy between the light endpoint and the maximum has one light root. -/
theorem existsUnique_light_entropy_root {m h : ℝ} (hm : 0 < m)
    (hlo : Real.log m ≤ h) (hhi : h < Real.log (m + 1)) :
    ∃! z, z ∈ Ico 0 (1 / (m + 1)) ∧ branchEntropy m z = h := by
  have htop : 0 ≤ 1 / (m + 1) := by positivity
  have hv : h ∈ Icc (branchEntropy m 0) (branchEntropy m (1 / (m + 1))) := by
    simpa only [branchEntropy_zero, branchEntropy_uniform hm, mem_Icc] using And.intro hlo hhi.le
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc htop
    (continuous_branchEntropy (ne_of_gt hm)).continuousOn hv
  have hzlt : z < 1 / (m + 1) := by
    apply lt_of_le_of_ne hz.2
    intro he
    rw [he, branchEntropy_uniform hm] at heq
    exact (ne_of_lt hhi) heq.symm
  refine ⟨z, ⟨⟨hz.1, hzlt⟩, heq⟩, ?_⟩
  intro y hy
  exact (strictMonoOn_branchEntropy hm).injOn ⟨hy.1.1, hy.1.2.le⟩ hz
    (hy.2.trans heq.symm)

/-- Every positive entropy below the maximum has one interior heavy root. -/
theorem existsUnique_heavy_entropy_root {m h : ℝ} (hm : 0 < m)
    (hlo : 0 < h) (hhi : h < Real.log (m + 1)) :
    ∃! z, z ∈ Ioo (1 / (m + 1)) 1 ∧ branchEntropy m z = h := by
  have htop : 1 / (m + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hv : h ∈ Icc (branchEntropy m 1) (branchEntropy m (1 / (m + 1))) := by
    simpa only [branchEntropy_one, branchEntropy_uniform hm, mem_Icc] using And.intro hlo.le hhi.le
  obtain ⟨z, hz, heq⟩ := intermediate_value_Icc' htop
    (continuous_branchEntropy (ne_of_gt hm)).continuousOn hv
  have hzgt : 1 / (m + 1) < z := by
    apply lt_of_le_of_ne hz.1
    intro he
    rw [← he, branchEntropy_uniform hm] at heq
    exact (ne_of_lt hhi) heq.symm
  have hzlt : z < 1 := by
    apply lt_of_le_of_ne hz.2
    intro he
    rw [he, branchEntropy_one] at heq
    exact (ne_of_gt hlo) heq.symm
  refine ⟨z, ⟨⟨hzgt, hzlt⟩, heq⟩, ?_⟩
  intro y hy
  exact (strictAntiOn_branchEntropy hm).injOn ⟨hy.1.1.le, hy.1.2.le⟩ hz
    (hy.2.trans heq.symm)

/-- The support index used for entropy-matched candidates. -/
def entropySupportIndex (h : ℝ) : ℕ := ⌊Real.exp h⌋₊

theorem entropySupportIndex_pos {h : ℝ} (hh : 0 ≤ h) : 0 < entropySupportIndex h := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_exp_iff.mpr hh

theorem entropySupportIndex_log_bounds {h : ℝ} (hh : 0 ≤ h) :
    Real.log (entropySupportIndex h : ℝ) ≤ h ∧
      h < Real.log ((entropySupportIndex h : ℝ) + 1) := by
  have hk : 0 < (entropySupportIndex h : ℝ) :=
    Nat.cast_pos.mpr (entropySupportIndex_pos hh)
  constructor
  · apply (Real.log_le_iff_le_exp hk).2
    exact Nat.floor_le (Real.exp_pos h).le
  · apply (Real.lt_log_iff_exp_lt (by positivity)).2
    exact Nat.lt_floor_add_one (Real.exp h)

/-- The precise light-root existence statement with `k = floor (exp h)`. -/
theorem existsUnique_light_candidate_parameter {h : ℝ} (hh : 0 < h) :
    ∃! a, a ∈ Ico 0 (1 / ((entropySupportIndex h : ℝ) + 1)) ∧
      branchEntropy (entropySupportIndex h) a = h := by
  obtain ⟨hlo, hhi⟩ := entropySupportIndex_log_bounds hh.le
  exact existsUnique_light_entropy_root
    (Nat.cast_pos.mpr (entropySupportIndex_pos hh.le)) hlo hhi

/-- The precise heavy-root existence statement for each integer `m ≥ floor (exp h)`. -/
theorem existsUnique_heavy_candidate_parameter {h : ℝ} (hh : 0 < h) {m : ℕ}
    (hm : entropySupportIndex h ≤ m) :
    ∃! z, z ∈ Ioo (1 / ((m : ℝ) + 1)) 1 ∧ branchEntropy m z = h := by
  have hmpos : 0 < m := lt_of_lt_of_le (entropySupportIndex_pos hh.le) hm
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  apply existsUnique_heavy_entropy_root hmreal hh
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have hk : Real.exp h < (entropySupportIndex h : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.exp h)
  have hcast : (entropySupportIndex h : ℝ) ≤ m := Nat.cast_le.mpr hm
  linarith

/-- On the light branch, the endpoint entropy occurs exactly at zero exceptional mass. -/
theorem light_entropy_eq_log_iff {m a : ℝ} (hm : 0 < m)
    (ha : a ∈ Icc 0 (1 / (m + 1))) :
    branchEntropy m a = Real.log m ↔ a = 0 := by
  constructor
  · intro heq
    apply (strictMonoOn_branchEntropy hm).injOn ha ⟨le_refl 0, by positivity⟩
    simpa only [branchEntropy_zero] using heq
  · intro heq
    simp [heq]

/-- Away from its zero endpoint, the light branch has one strictly smaller positive mass. -/
theorem light_parameter_mass_order {m a : ℝ} (hm : 0 < m)
    (ha : a ∈ Ioo 0 (1 / (m + 1))) :
    0 < a ∧ a < (1 - a) / m := by
  refine ⟨ha.1, (lt_div_iff₀ hm).2 ?_⟩
  have hmul := (lt_div_iff₀ (by positivity : 0 < m + 1)).1 ha.2
  nlinarith

/-- On the heavy branch, every repeated mass is positive and smaller than the exceptional mass. -/
theorem heavy_parameter_mass_order {m z : ℝ} (hm : 0 < m)
    (hz : z ∈ Ioo (1 / (m + 1)) 1) :
    0 < (1 - z) / m ∧ (1 - z) / m < z := by
  refine ⟨div_pos (sub_pos.mpr hz.2) hm, (div_lt_iff₀ hm).2 ?_⟩
  have hmul := (div_lt_iff₀ (by positivity : 0 < m + 1)).1 hz.1
  nlinarith

end

end EntropyConstrainedMissingMass
