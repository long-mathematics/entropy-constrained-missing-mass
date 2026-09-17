import EntropyConstrainedMissingMass.OccupancyExtrema

/-! The singleton estimator itself, as a statistic on actual IID samples. -/
open MeasureTheory Set
namespace EntropyConstrainedMissingMass
noncomputable section
open ProbabilityVector

/-- The observed singleton count divided by the sample size. -/
def singletonEstimator {n : ℕ} (x : Fin n → ℕ) : ℝ :=
  (singletonCountNat x : ℝ) / (n : ℝ)

def expectedSingletonEstimator (p : ProbabilityVector ℕ) (n : ℕ) : ℝ :=
  ∫ x : Fin n → ℕ, singletonEstimator x ∂p.sampleLaw n

@[simp] theorem expectedSingletonEstimator_eq (p : ProbabilityVector ℕ) {n : ℕ}
    (hn : 0 < n) : expectedSingletonEstimator p n = p.objective (n-1) := by
  unfold expectedSingletonEstimator singletonEstimator
  rw [integral_div, p.integral_singletonCount]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

/-- The largest expectation of the singleton estimator is exactly `B_(n-1)`,
and this largest value is attained by an actual entropy-feasible law. -/
theorem singleton_estimator_expectation_max {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 ≤ h) :
    IsGreatest ((fun p : ProbabilityVector ℕ => expectedSingletonEstimator p n) '' Feasible h)
      (optimalValue (n-1) h) := by
  simpa only [expectedSingletonEstimator_eq _ hn,expectedDiscovery_eq] using
    discovery_expectation_max (n-1) hh

/-- All equality cases are exactly the original missing-mass maximizers. -/
theorem singleton_estimator_optimizer_iff (p : ProbabilityVector ℕ) {n : ℕ}
    (hn : 0 < n) (h : ℝ) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h →
      expectedSingletonEstimator q n ≤ expectedSingletonEstimator p n) ↔
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h →
      q.objective (n-1) ≤ p.objective (n-1)) := by
  simp only [expectedSingletonEstimator_eq _ hn]

/-- The complete finite-candidate equality classification for the estimator. -/
theorem singleton_estimator_optimizer_iff_finite_candidate (p : ProbabilityVector ℕ)
    {n : ℕ} (hn : 2 ≤ n) {h : ℝ} (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h →
      expectedSingletonEstimator q n ≤ expectedSingletonEstimator p n) ↔
    (LightCandidateForm h p ∨ CutoffHeavyCandidateForm (n-1) h p) ∧
      p.objective (n-1) = finiteCandidateMaximum (n-1) h :=
  (singleton_estimator_optimizer_iff p (by omega) h).trans
    (p.globalMax_iff_finite_candidate (by omega) hh)

end
end EntropyConstrainedMissingMass
