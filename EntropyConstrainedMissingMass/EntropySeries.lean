import EntropyConstrainedMissingMass.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The entropy–missing-mass series identity, including infinite entropy. -/

namespace EntropyConstrainedMissingMass

/-- The atomwise logarithm series, with the zero atom included. -/
theorem hasSum_missingMassTerm_div {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    HasSum (fun n : ℕ => missingMassTerm (n + 1) u / (n + 1)) (Real.negMulLog u) := by
  rcases eq_or_lt_of_le h0 with hu | hu
  · subst u
    simp [missingMassTerm]
  · have habs : |1 - u| < 1 := by rw [abs_of_nonneg (sub_nonneg.mpr h1)]; linarith
    have hs := (Real.hasSum_pow_div_log_of_abs_lt_one habs).mul_left u
    convert hs using 1 <;> simp [missingMassTerm, Real.negMulLog, mul_div_assoc]

namespace ProbabilityVector
variable {ι κ : Type*}

/-- Manuscript Lemma `lem:entropy-series`, with equality in the extended nonnegative reals. -/
theorem entropy_series (p : ProbabilityVector ι) :
    p.entropy = ∑' n : ℕ, ENNReal.ofReal (p.objective (n + 1) / (n + 1)) := by
  unfold entropy
  calc
    (∑' i, ENNReal.ofReal (Real.negMulLog (p.coord i))) =
        ∑' i, ∑' n : ℕ, ENNReal.ofReal (missingMassTerm (n + 1) (p.coord i) / (n + 1)) := by
      apply tsum_congr
      intro i
      have hs := hasSum_missingMassTerm_div (p.coord_nonneg i) (p.coord_le_one i)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg
        (missingMassTerm_nonneg _ (p.coord_nonneg i) (p.coord_le_one i)) (by positivity)) hs.summable,
        hs.tsum_eq]
    _ = ∑' n : ℕ, ∑' i, ENNReal.ofReal (missingMassTerm (n + 1) (p.coord i) / (n + 1)) :=
      ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => div_nonneg
        (missingMassTerm_nonneg _ (p.coord_nonneg i) (p.coord_le_one i)) (by positivity))
        ((p.objective_summable (n + 1)).div_const _), tsum_div_const]
      rfl

/-- Finite entropy is exactly summability of the nonnegative weighted missing masses. -/
theorem entropy_ne_top_iff_objective_series_summable (p : ProbabilityVector ι) :
    p.entropy ≠ ⊤ ↔ Summable (fun n : ℕ => p.objective (n + 1) / (n + 1)) := by
  rw [p.entropy_series]
  constructor
  · intro h
    have hn : ∀ n : ℕ, 0 ≤ p.objective (n + 1) / (n + 1) :=
      fun n => div_nonneg (p.objective_nonneg _) (by positivity)
    simpa only [ENNReal.toReal_ofReal (hn _)] using ENNReal.summable_toReal h
  · intro h
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => div_nonneg (p.objective_nonneg _) (by positivity)) h]
    exact ENNReal.ofReal_ne_top

/-- The real-valued series sums to entropy when the entropy is finite. -/
theorem hasSum_objective_div_entropy (p : ProbabilityVector ι) (h : p.entropy ≠ ⊤) :
    HasSum (fun n : ℕ => p.objective (n + 1) / (n + 1)) p.entropy.toReal := by
  have hs := p.entropy_ne_top_iff_objective_series_summable.mp h
  convert hs.hasSum using 1
  rw [p.entropy_series, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => div_nonneg (p.objective_nonneg _) (by positivity)) hs,
    ENNReal.toReal_ofReal (tsum_nonneg (fun n => div_nonneg (p.objective_nonneg _) (by positivity)))]

/-- Equal finite entropies force the weighted difference series to sum to zero. -/
theorem hasSum_objective_sub_div_zero (p : ProbabilityVector ι) (q : ProbabilityVector κ)
    (hp : p.entropy ≠ ⊤) (heq : p.entropy = q.entropy) :
    HasSum (fun n : ℕ => (p.objective (n + 1) - q.objective (n + 1)) / (n + 1)) 0 := by
  have hq : q.entropy ≠ ⊤ := heq ▸ hp
  have hs := (p.hasSum_objective_div_entropy hp).sub (q.hasSum_objective_div_entropy hq)
  simpa only [sub_div, heq, sub_self] using hs

/-- The difference series in Lemma `lem:entropy-series` converges absolutely. -/
theorem summable_abs_objective_sub_div (p : ProbabilityVector ι) (q : ProbabilityVector κ)
    (hp : p.entropy ≠ ⊤) (heq : p.entropy = q.entropy) :
    Summable (fun n : ℕ => |(p.objective (n + 1) - q.objective (n + 1)) / (n + 1)|) :=
  (p.hasSum_objective_sub_div_zero q hp heq).summable.abs

end ProbabilityVector
end EntropyConstrainedMissingMass
