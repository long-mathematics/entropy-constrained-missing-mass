import EntropyConstrainedMissingMass.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Uniform tail control for entropy-bounded probability vectors sorted in decreasing order.
Indexing starts at zero, so the atom at index `n` is bounded by `1 / (n + 1)`. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector

/-- A decreasing probability sequence has its `n`th atom at most `1/(n+1)`. -/
theorem coord_le_recip_of_antitone (p : ProbabilityVector ℕ) (hp : Antitone p.coord) (n : ℕ) :
    p.coord n ≤ 1 / ((n : ℝ) + 1) := by
  have hsum : ((n : ℝ) + 1) * p.coord n ≤ 1 := by
    calc
      ((n : ℝ) + 1) * p.coord n = ∑ _i ∈ Finset.range (n + 1), p.coord n := by simp
      _ ≤ ∑ i ∈ Finset.range (n + 1), p.coord i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hp (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ ≤ ∑' i, p.coord i := p.summable_coord.sum_le_tsum _ (fun i _ => p.coord_nonneg i)
      _ = 1 := p.tsum_coord
  exact (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hsum)

/-- An entropy budget controls the actual real entropy sum. -/
theorem tsum_entropy_le_of_feasible {ι : Type*} (p : ProbabilityVector ι) {h : ℝ}
    (hh : 0 ≤ h) (hp : p.entropy ≤ ENNReal.ofReal h) :
    (∑' i, Real.negMulLog (p.coord i)) ≤ h := by
  have hfinite : p.entropy ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  simpa only [p.entropy_toReal hfinite, ENNReal.toReal_ofReal hh] using ht

/-- If an atom is at most `1/a`, its entropy contribution is at least `u log a`. -/
theorem mul_log_le_negMulLog {u a : ℝ} (hu : 0 ≤ u) (_ha : 0 < a) (hbound : u ≤ 1 / a) :
    u * Real.log a ≤ Real.negMulLog u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  · have hlog := Real.log_le_log hu hbound
    rw [one_div, Real.log_inv] at hlog
    have := mul_le_mul_of_nonneg_left hlog hu.le
    simp only [Real.negMulLog]
    nlinarith

/-- Uniform entropy tail estimate. The tail begins at index `N`, with zero-based indices. -/
theorem sorted_tail_le (p : ProbabilityVector ℕ) (hp : Antitone p.coord) {h : ℝ}
    (hh : 0 ≤ h) (hbudget : p.entropy ≤ ENNReal.ofReal h) (N : ℕ) (hN : 1 ≤ N) :
    (∑' i : {n : ℕ // N ≤ n}, p.coord i) ≤ h / Real.log ((N : ℝ) + 1) := by
  have hlog : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by exact_mod_cast Nat.lt_succ_of_le hN)
  have hfinite : p.entropy ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
  have hsEntropy := p.entropy_ne_top_iff.mp hfinite
  have hterm : ∀ i : {n : ℕ // N ≤ n},
      p.coord i * Real.log ((N : ℝ) + 1) ≤ Real.negMulLog (p.coord i) := by
    intro i
    apply mul_log_le_negMulLog (p.coord_nonneg i) (by positivity)
    exact (hp i.property).trans (p.coord_le_recip_of_antitone hp N)
  apply (le_div_iff₀ hlog).mpr
  calc
    (∑' i : {n : ℕ // N ≤ n}, p.coord i) * Real.log ((N : ℝ) + 1) =
        ∑' i : {n : ℕ // N ≤ n}, p.coord i * Real.log ((N : ℝ) + 1) := by rw [tsum_mul_right]
    _ ≤ ∑' i : {n : ℕ // N ≤ n}, Real.negMulLog (p.coord i) :=
      ((p.summable_coord.subtype (N ≤ ·)).mul_right _).tsum_le_tsum hterm
        (hsEntropy.subtype (N ≤ ·))
    _ ≤ ∑' i, Real.negMulLog (p.coord i) :=
      hsEntropy.tsum_subtype_le _ _ p.entropy_term_nonneg
    _ ≤ h := p.tsum_entropy_le_of_feasible hh hbudget

/-- The common upper bound in the sorted tail estimate tends to zero. -/
theorem tendsto_entropy_tail_bound (h : ℝ) :
    Filter.Tendsto (fun N : ℕ => h / Real.log ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
  exact (Real.tendsto_log_atTop.comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)).const_div_atTop h

/-- Entropy sublevels of sorted probability sequences have uniformly vanishing ℓ¹ tails. -/
theorem uniform_sorted_tail {h ε : ℝ} (hh : 0 ≤ h) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : ProbabilityVector ℕ,
      Antitone p.coord → p.entropy ≤ ENNReal.ofReal h →
      (∑' i : {k : ℕ // n ≤ k}, |p.coord i|) < ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_entropy_tail_bound h).eventually_lt_const hε)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn p hp hbudget
  simp only [abs_of_nonneg (p.coord_nonneg _)]
  exact (p.sorted_tail_le hp hh hbudget n ((le_max_right N 1).trans hn)).trans_lt
    (hN n ((le_max_left N 1).trans hn))

end EntropyConstrainedMissingMass.ProbabilityVector
