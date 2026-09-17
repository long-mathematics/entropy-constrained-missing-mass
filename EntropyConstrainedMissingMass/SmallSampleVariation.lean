import EntropyConstrainedMissingMass.RepeatedPairVariation
import EntropyConstrainedMissingMass.SmallSampleScalar
import EntropyConstrainedMissingMass.CandidateVectors

/-! Actual second-variation exclusion of heavy candidates for sample sizes one and two. -/
namespace EntropyConstrainedMissingMass
noncomputable section

def repeatedPairHessian (t : ℕ) (q z : ℝ) : ℝ :=
  weightedCurvature t q + (deriv (missingMassTerm t) q - deriv (missingMassTerm t) z) /
    (Real.log z - Real.log q)

theorem repeatedPairHessian_one {q r : ℝ} (hq : 0 < q) (hr : 1 < r) :
    repeatedPairHessian 1 q (r * q) = 2 * q * ((r - 1) / Real.log r - 1) := by
  rw [repeatedPairHessian, weightedCurvature_one,
    deriv_missingMassTerm 1 (by omega), deriv_missingMassTerm 1 (by omega),
    Real.log_mul (by linarith : r ≠ 0) (ne_of_gt hq)]
  norm_num
  ring

theorem repeatedPairHessian_one_pos {q r : ℝ} (hq : 0 < q) (hr : 1 < r) :
    0 < repeatedPairHessian 1 q (r * q) := by
  rw [repeatedPairHessian_one hq hr]
  exact mul_pos (mul_pos (by norm_num) hq) (sub_pos.mpr (logarithmic_mean_ratio_gt_one hr))

theorem repeatedPairHessian_two {m r : ℝ} (hm : 2 ≤ m) (hr : 1 < r) :
    repeatedPairHessian 2 (1 / (m + r)) (r * (1 / (m + r))) =
      smallSampleNumerator m r / ((m + r) ^ 2 * Real.log r) := by
  have hd : m + r ≠ 0 := by linarith
  have hq : 0 < 1 / (m + r) := by positivity
  rw [repeatedPairHessian, weightedCurvature_eq 2 (by omega),
    deriv_missingMassTerm 2 (by omega), deriv_missingMassTerm 2 (by omega),
    Real.log_mul (by linarith : r ≠ 0) (ne_of_gt hq)]
  norm_num
  unfold smallSampleNumerator
  have hl : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  field_simp
  ring

theorem repeatedPairHessian_two_pos {m r : ℝ} (hm : 2 ≤ m) (hr : 1 < r) :
    0 < repeatedPairHessian 2 (1 / (m + r)) (r * (1 / (m + r))) := by
  rw [repeatedPairHessian_two hm hr]
  exact div_pos (smallSampleNumerator_pos hm hr)
    (mul_pos (sq_pos_of_pos (by linarith)) (Real.log_pos hr))

namespace ProbabilityVector

theorem repeatedPairHessian_nonpos_of_localMax {ι : Type*} (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (e : Fin 3 ↪ ι)
    {q z : ℝ} (hq : 0 < q) (hqz : q < z)
    (hbase : (fun i => p.coord (e i)) = repeatedPairBase q z) :
    repeatedPairHessian t q z ≤ 0 := by
  have h := p.repeated_pair_weighted_bound ht hp e hq hqz hbase
  unfold repeatedPairHessian weightedCurvature
  have he : (deriv (missingMassTerm t) q - deriv (missingMassTerm t) z) /
      (Real.log z - Real.log q) =
      -((deriv (missingMassTerm t) z - deriv (missingMassTerm t) q) /
        (Real.log z - Real.log q)) := by ring
  rw [he]
  linarith

/-- A heavy atom and at least two repeated light atoms cannot be locally optimal for t=1,2. -/
theorem not_localMax_heavy_smallSamples {ι : Type*} (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : t = 1 ∨ t = 2) (e : Fin 3 ↪ ι)
    {q z m : ℝ} (hq : 0 < q) (hqz : q < z) (hm : 2 ≤ m) (hmass : z + m * q = 1)
    (hbase : (fun i => p.coord (e i)) = repeatedPairBase q z) :
    ¬ LocalMaximizer t h p := by
  intro hp
  let r := z / q
  have hr : 1 < r := (one_lt_div hq).mpr hqz
  have hz : z = r * q := by dsimp [r]; field_simp
  have hden : m + r ≠ 0 := by linarith
  have he : q = 1 / (m + r) := by
    apply (eq_div_iff hden).mpr
    rw [hz] at hmass
    nlinarith only [hmass]
  have hn := p.repeatedPairHessian_nonpos_of_localMax (show 1 ≤ t by omega) hp e hq hqz hbase
  rcases ht with rfl | rfl
  · rw [hz] at hn
    exact (not_lt_of_ge hn) (repeatedPairHessian_one_pos hq hr)
  · rw [hz, he] at hn
    exact (not_lt_of_ge hn) (repeatedPairHessian_two_pos hm hr)

/-- The exclusion applies to the actual candidate distribution, under every zero insertion. -/
theorem not_localMax_heavy_candidate_smallSamples {ι : Type*} {t m : ℕ} {h z : ℝ}
    (ht : t = 1 ∨ t = 2) (hm : 2 ≤ m) (hz : z ∈ Set.Ioo 0 1)
    (hheavy : (1 - z) / (m : ℝ) < z) (e : Fin (m + 1) ↪ ι) :
    ¬ LocalMaximizer t h (zeroExtend e (candidateVector m z (by omega) ⟨hz.1.le, hz.2.le⟩)) := by
  let a : Fin 3 ↪ Fin (m + 1) := ⟨![⟨1, by omega⟩, ⟨2, by omega⟩, 0], by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let q := (1 - z) / (m : ℝ)
  have hq : 0 < q := div_pos (sub_pos.mpr hz.2) (Nat.cast_pos.mpr (by omega))
  apply not_localMax_heavy_smallSamples _ ht (a.trans e) hq hheavy
    (by exact_mod_cast hm) (m := (m : ℝ))
  · dsimp [q]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  · funext i
    change (zeroExtend e (candidateVector m z (by omega) ⟨hz.1.le, hz.2.le⟩)).coord (e (a i)) =
      repeatedPairBase q z i
    rw [coord_zeroExtend_apply]
    change candidateCoord m z (a i) = repeatedPairBase q z i
    fin_cases i <;> rfl

end ProbabilityVector
end
end EntropyConstrainedMissingMass
