import EntropyConstrainedMissingMass.ObjectiveContinuity
import EntropyConstrainedMissingMass.ObjectiveStationarity
import Mathlib.Analysis.Calculus.MeanValue

/-! The manuscript's Lipschitz constant is the attained maximum of `|f_t'|`
on the closed unit interval. The resulting bound holds for arbitrary alphabets
with their genuine ℓ¹ metric. -/

namespace EntropyConstrainedMissingMass

/-- The absolute derivative attains a finite real maximum on `[0,1]`. -/
theorem exists_max_abs_deriv_missingMassTerm (t : ℕ) (ht : 1 ≤ t) :
    ∃ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      |deriv (missingMassTerm t) v| ≤ |deriv (missingMassTerm t) u| := by
  exact isCompact_Icc.exists_isMaxOn ⟨0, by simp⟩
    (continuous_deriv_missingMassTerm t ht).abs.continuousOn

/-- A point where `|f_t'|` has its maximum. -/
noncomputable def derivativeMaxPoint (t : ℕ) (ht : 1 ≤ t) : ℝ :=
  (exists_max_abs_deriv_missingMassTerm t ht).choose

theorem derivativeMaxPoint_mem (t : ℕ) (ht : 1 ≤ t) :
    derivativeMaxPoint t ht ∈ Set.Icc (0 : ℝ) 1 :=
  (exists_max_abs_deriv_missingMassTerm t ht).choose_spec.1

/-- The finite maximum `L_t = max_{0 ≤ u ≤ 1} |f_t'(u)|`. -/
noncomputable def derivativeLipschitzConstant (t : ℕ) (ht : 1 ≤ t) : ℝ :=
  |deriv (missingMassTerm t) (derivativeMaxPoint t ht)|

theorem derivativeLipschitzConstant_nonneg (t : ℕ) (ht : 1 ≤ t) :
    0 ≤ derivativeLipschitzConstant t ht := abs_nonneg _

theorem abs_deriv_missingMassTerm_le (t : ℕ) (ht : 1 ≤ t) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (missingMassTerm t) u| ≤ derivativeLipschitzConstant t ht :=
  (exists_max_abs_deriv_missingMassTerm t ht).choose_spec.2 u hu

/-- The mean-value estimate with exactly the maximum derivative constant. -/
theorem missingMassTerm_lipschitz_derivativeMax (t : ℕ) (ht : 1 ≤ t) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |missingMassTerm t x - missingMassTerm t y| ≤
      derivativeLipschitzConstant t ht * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u (_ : u ∈ Set.Icc (0 : ℝ) 1) =>
        (hasDerivAt_missingMassTerm t ht u).differentiableAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using
        abs_deriv_missingMassTerm_le t ht hu)
      (convex_Icc (0 : ℝ) 1) hy hx

namespace ProbabilityVector
variable {ι : Type*}

/-- The exact manuscript ℓ¹ estimate, without a finite-support restriction. -/
theorem objective_dist_le_derivativeMax (p q : ProbabilityVector ι)
    (t : ℕ) (ht : 1 ≤ t) :
    |p.objective t - q.objective t| ≤ derivativeLipschitzConstant t ht * dist p q := by
  have hs := (p.objective_summable t).sub (q.objective_summable t)
  have hd := (p.summable_coord.sub q.summable_coord).abs
  have hn : Summable (fun i => ‖missingMassTerm t (p.coord i) -
      missingMassTerm t (q.coord i)‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  rw [objective, objective, ← (p.objective_summable t).tsum_sub (q.objective_summable t)]
  calc
    |∑' i, (missingMassTerm t (p.coord i) - missingMassTerm t (q.coord i))| ≤
      ∑' i, |missingMassTerm t (p.coord i) - missingMassTerm t (q.coord i)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, derivativeLipschitzConstant t ht * |p.coord i - q.coord i| :=
      hs.abs.tsum_le_tsum (fun i => missingMassTerm_lipschitz_derivativeMax t ht
        ⟨p.coord_nonneg i, p.coord_le_one i⟩ ⟨q.coord_nonneg i, q.coord_le_one i⟩)
        (hd.mul_left _)
    _ = derivativeLipschitzConstant t ht * dist p q := by
      rw [tsum_mul_left, p.dist_eq_tsum q]

theorem objective_lipschitz_derivativeMax (t : ℕ) (ht : 1 ≤ t) :
    LipschitzWith ⟨derivativeLipschitzConstant t ht,
      derivativeLipschitzConstant_nonneg t ht⟩
      (fun p : ProbabilityVector ι => p.objective t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change |p.objective t - q.objective t| ≤ derivativeLipschitzConstant t ht * dist p q
  exact p.objective_dist_le_derivativeMax q t ht

end ProbabilityVector

/-- An attained real constant simultaneously bounds every scalar difference and
all probability-vector objective differences on any alphabet. -/
theorem exists_attained_objective_lipschitz_constant (ι : Type*)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∃ u ∈ Set.Icc (0 : ℝ) 1, L = |deriv (missingMassTerm t) u|) ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv (missingMassTerm t) u| ≤ L) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |missingMassTerm t x - missingMassTerm t y| ≤ L * |x - y|) ∧
      (∀ p q : ProbabilityVector ι, |p.objective t - q.objective t| ≤ L * dist p q) := by
  refine ⟨derivativeLipschitzConstant t ht, derivativeLipschitzConstant_nonneg t ht,
    ⟨derivativeMaxPoint t ht, derivativeMaxPoint_mem t ht, rfl⟩, ?_, ?_, ?_⟩
  · exact fun _ hu => abs_deriv_missingMassTerm_le t ht hu
  · exact fun _ hx _ hy => missingMassTerm_lipschitz_derivativeMax t ht hx hy
  · exact fun p q => p.objective_dist_le_derivativeMax q t ht

end EntropyConstrainedMissingMass
