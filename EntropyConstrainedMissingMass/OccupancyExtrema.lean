import EntropyConstrainedMissingMass.OccupancySampling

/-! Exact extrema of IID occupancy expectations, with all optimizing laws classified. -/
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass
noncomputable section
open ProbabilityVector

def expectedSingletons (p : ProbabilityVector ℕ) (n : ℕ) : ℝ :=
  ∫ x : Fin n → ℕ, (singletonCountNat x : ℝ) ∂p.sampleLaw n

def expectedDiscovery (p : ProbabilityVector ℕ) (t : ℕ) : ℝ :=
  ∫ x : Fin (t+1) → ℕ, (distinctCount x : ℝ) -
    (distinctCount (fun j : Fin t => x j.succ) : ℝ) ∂p.sampleLaw (t+1)

def expectedCoverage (p : ProbabilityVector ℕ) (t : ℕ) : ℝ :=
  ∫ x : Fin t → ℕ, p.coverage x ∂p.sampleLaw t

@[simp] theorem expectedSingletons_eq (p : ProbabilityVector ℕ) (n : ℕ) :
    expectedSingletons p n = (n : ℝ)*p.objective (n-1) := p.integral_singletonCount n

@[simp] theorem expectedDiscovery_eq (p : ProbabilityVector ℕ) (t : ℕ) :
    expectedDiscovery p t = p.objective t := p.integral_distinctCount_increment t

@[simp] theorem expectedCoverage_eq (p : ProbabilityVector ℕ) (t : ℕ) :
    expectedCoverage p t = 1-p.objective t := p.integral_coverage t

/-- The maximum singleton expectation, interpreted as an actual attained greatest value. -/
theorem singleton_expectation_max (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    IsGreatest ((fun p : ProbabilityVector ℕ => expectedSingletons p n) '' Feasible h)
      ((n : ℝ)*optimalValue (n-1) h) := by
  obtain ⟨p,_,hp,hmax⟩ := exists_global_maximizer_countable (n-1) h hh
  constructor
  · refine ⟨p,hp,?_⟩
    change expectedSingletons p n = _
    rw [expectedSingletons_eq,optimalValue_eq_of_globalMax p (n-1) hp hmax]
  · rintro _ ⟨q,hq,rfl⟩
    change expectedSingletons q n ≤ _
    rw [expectedSingletons_eq]
    exact mul_le_mul_of_nonneg_left (objective_le_optimalValue q (n-1) hq) (Nat.cast_nonneg n)

theorem discovery_expectation_max (t : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    IsGreatest ((fun p : ProbabilityVector ℕ => expectedDiscovery p t) '' Feasible h) (optimalValue t h) := by
  obtain ⟨p,_,hp,hmax⟩ := exists_global_maximizer_countable t h hh
  constructor
  · exact ⟨p,hp,(expectedDiscovery_eq p t).trans (optimalValue_eq_of_globalMax p t hp hmax).symm⟩
  · rintro _ ⟨q,hq,rfl⟩
    change expectedDiscovery q t ≤ _
    rw [expectedDiscovery_eq]
    exact objective_le_optimalValue q t hq

theorem coverage_expectation_min (t : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    IsLeast ((fun p : ProbabilityVector ℕ => expectedCoverage p t) '' Feasible h) (1-optimalValue t h) := by
  obtain ⟨p,_,hp,hmax⟩ := exists_global_maximizer_countable t h hh
  constructor
  · refine ⟨p,hp,?_⟩
    change expectedCoverage p t = _
    rw [expectedCoverage_eq,optimalValue_eq_of_globalMax p t hp hmax]
  · rintro _ ⟨q,hq,rfl⟩
    change _ ≤ expectedCoverage q t
    rw [expectedCoverage_eq]
    exact sub_le_sub_left (objective_le_optimalValue q t hq) 1

/-- The singleton optimization has precisely the original objective maximizers. -/
theorem singleton_optimizer_iff (p : ProbabilityVector ℕ) {n : ℕ} (hn : 0 < n) (h : ℝ) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedSingletons q n ≤ expectedSingletons p n) ↔
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → q.objective (n-1) ≤ p.objective (n-1)) := by
  simp only [expectedSingletons_eq,mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hn : (0 : ℝ) < n)]

theorem discovery_optimizer_iff (p : ProbabilityVector ℕ) (t : ℕ) (h : ℝ) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedDiscovery q t ≤ expectedDiscovery p t) ↔
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → q.objective t ≤ p.objective t) := by
  simp only [expectedDiscovery_eq]

theorem coverage_optimizer_iff (p : ProbabilityVector ℕ) (t : ℕ) (h : ℝ) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedCoverage p t ≤ expectedCoverage q t) ↔
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → q.objective t ≤ p.objective t) := by
  simp only [expectedCoverage_eq,sub_le_sub_iff_left]

/-- All singleton ties correspond exactly to the finite candidate list at index `n-1`. -/
theorem singleton_optimizer_iff_finite_candidate (p : ProbabilityVector ℕ) {n : ℕ} (hn : 2 ≤ n)
    {h : ℝ} (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedSingletons q n ≤ expectedSingletons p n) ↔
    (LightCandidateForm h p ∨ CutoffHeavyCandidateForm (n-1) h p) ∧
      p.objective (n-1) = finiteCandidateMaximum (n-1) h :=
  (singleton_optimizer_iff p (by omega) h).trans (p.globalMax_iff_finite_candidate (by omega) hh)

theorem discovery_optimizer_iff_finite_candidate (p : ProbabilityVector ℕ) {t : ℕ} (ht : 1 ≤ t)
    {h : ℝ} (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedDiscovery q t ≤ expectedDiscovery p t) ↔
    (LightCandidateForm h p ∨ CutoffHeavyCandidateForm t h p) ∧ p.objective t = finiteCandidateMaximum t h :=
  (discovery_optimizer_iff p t h).trans (p.globalMax_iff_finite_candidate ht hh)

theorem coverage_optimizer_iff_finite_candidate (p : ProbabilityVector ℕ) {t : ℕ} (ht : 1 ≤ t)
    {h : ℝ} (hh : 0 < h) :
    (p ∈ Feasible h ∧ ∀ q : ProbabilityVector ℕ, q ∈ Feasible h → expectedCoverage p t ≤ expectedCoverage q t) ↔
    (LightCandidateForm h p ∨ CutoffHeavyCandidateForm t h p) ∧ p.objective t = finiteCandidateMaximum t h :=
  (coverage_optimizer_iff p t h).trans (p.globalMax_iff_finite_candidate ht hh)

end
end EntropyConstrainedMissingMass
