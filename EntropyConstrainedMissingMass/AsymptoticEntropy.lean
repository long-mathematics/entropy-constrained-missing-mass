import EntropyConstrainedMissingMass.BranchEntropy
import EntropyConstrainedMissingMass.CertificateBounds
import Mathlib.Analysis.Asymptotics.Defs

/-! Exact heavy-tail identities and the quantitative entropy correction at small tail mass. -/

open Filter Set
open scoped Topology Asymptotics
namespace EntropyConstrainedMissingMass
noncomputable section

/-- The entropy correction A(L) of Section 6; its value at zero is immaterial to the right limit. -/
def entropyTailCorrection (L : ℝ) : ℝ := -(1 - L) / L * Real.log (1 - L)

/-- The entropy identity expressed using total light mass L. -/
theorem heavy_tail_entropy (m L : ℝ) :
    branchEntropy m (1 - L) = -(1 - L) * Real.log (1 - L) - L * Real.log (L / m) := by
  unfold branchEntropy
  rw [show 1 - (1 - L) = L by ring]

/-- The objective identity expressed using total light mass L. -/
theorem heavy_tail_objective (m L : ℝ) (t : ℕ) :
    branchObjective m t (1 - L) = (1 - L) * L ^ t + L * (1 - L / m) ^ t := by
  unfold branchObjective
  rw [show 1 - (1 - L) = L by ring]

/-- Exact separation of the logarithmic entropy term and its bounded correction. -/
theorem heavy_tail_entropy_correction (m L : ℝ) (hm : m ≠ 0) (hL : L ≠ 0) :
    branchEntropy m (1 - L) = L * (Real.log (m / L) + entropyTailCorrection L) := by
  rw [heavy_tail_entropy, Real.log_div hm hL, Real.log_div hL hm]
  unfold entropyTailCorrection
  field_simp
  ring

/-- A quantitative Taylor bound valid on the whole open unit interval. -/
theorem entropyTailCorrection_remainder_bound (L : ℝ) (hL : 0 < L) (hL1 : L < 1) :
    |entropyTailCorrection L - (1 - L / 2)| ≤ (3 / 2 : ℝ) * L ^ 2 := by
  have hlog := Real.abs_log_sub_add_sum_range_le (x := L)
    (by rw [abs_of_pos hL]; exact hL1) 2
  norm_num [Finset.sum_range_succ] at hlog
  rw [abs_of_pos hL] at hlog
  have hfactor : 0 ≤ (1 - L) / L := div_nonneg (by linarith) hL.le
  have hmul := mul_le_mul_of_nonneg_left hlog hfactor
  have hcancel : (1 - L) / L * (L ^ 3 / (1 - L)) = L ^ 2 := by
    field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hL1)]
  rw [hcancel, ← abs_of_nonneg hfactor, ← abs_mul] at hmul
  have hid : entropyTailCorrection L - (1 - L / 2) =
      -((1 - L) / L * (L + L ^ 2 / 2 + Real.log (1 - L))) - L ^ 2 / 2 := by
    unfold entropyTailCorrection
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |-((1 - L) / L * (L + L ^ 2 / 2 + Real.log (1 - L)))| + |L ^ 2 / 2| := abs_sub _ _
    _ ≤ L ^ 2 + L ^ 2 / 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ L ^ 2 / 2)]
      linarith only [hmul]
    _ = (3 / 2 : ℝ) * L ^ 2 := by ring

/-- The literal right-sided big-O expansion A(L)=1-L/2+O(L²). -/
theorem entropyTailCorrection_expansion :
    (fun L : ℝ => entropyTailCorrection L - (1 - L / 2)) =O[𝓝[>] (0 : ℝ)]
      (fun L => L ^ 2) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨3 / 2, ?_⟩
  have he : ∀ᶠ L : ℝ in 𝓝[>] (0 : ℝ), L < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he] with L hL hL1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg L)] using
    entropyTailCorrection_remainder_bound L hL hL1

/-- The correction is positive and at most one, uniformly on the open unit interval. -/
theorem entropyTailCorrection_bounds (L : ℝ) (hL : 0 < L) (hL1 : L < 1) :
    0 < entropyTailCorrection L ∧ entropyTailCorrection L ≤ 1 := by
  have hlog : Real.log (1 - L) < 0 := Real.log_neg (by linarith) (by linarith)
  constructor
  · unfold entropyTailCorrection
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by linarith) hL) hlog
  · have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - L by linarith)
    have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (1 - L) / L by positivity)
    have hid : (1 - L) / L * (1 - (1 - L)⁻¹) = -1 := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hL1)]
      ring
    rw [hid] at hmul
    unfold entropyTailCorrection
    rw [neg_div, neg_mul]
    linarith only [hmul]

/-- The normalized entropy equation used to invert the lower-bound candidate. -/
theorem heavy_tail_entropy_inversion (m L h : ℝ) (hm : 0 < m) (hL : 0 < L) (hh : 0 < h)
    (he : branchEntropy m (1 - L) = h) :
    h / L = Real.log (m / h) + Real.log (h / L) + entropyTailCorrection L := by
  have he' := heavy_tail_entropy_correction m L (ne_of_gt hm) (ne_of_gt hL)
  have hid : Real.log (m / h) + Real.log (h / L) = Real.log (m / L) := by
    rw [← Real.log_mul (ne_of_gt (div_pos hm hh)) (ne_of_gt (div_pos hh hL))]
    congr 1
    field_simp
  rw [hid]
  apply (div_eq_iff (ne_of_gt hL)).mpr
  rw [← he, he']
  ring

end
end EntropyConstrainedMissingMass
