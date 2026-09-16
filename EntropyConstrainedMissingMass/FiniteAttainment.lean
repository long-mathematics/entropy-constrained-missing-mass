import EntropyConstrainedMissingMass.EntropyTopology
import EntropyConstrainedMissingMass.ObjectiveContinuity
import EntropyConstrainedMissingMass.Support
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Attainment on a finite alphabet by compactness of the actual ℓ¹ simplex. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι : Type*}

/-- The point mass at a specified symbol, used to witness feasibility for every h≥0. -/
noncomputable def pointMass (i : ι) : ProbabilityVector ι := by
  classical
  exact ofHasSum (fun j => if j = i then 1 else 0) (by intro j; split_ifs <;> norm_num)
    (hasSum_ite_eq i 1)

@[simp] theorem coord_pointMass_self (i : ι) : (pointMass i).coord i = 1 := by
  classical
  simp [pointMass]

@[simp] theorem coord_pointMass_of_ne (i j : ι) (hji : j ≠ i) :
    (pointMass i).coord j = 0 := by
  classical
  simp [pointMass, hji]

@[simp] theorem entropy_pointMass (i : ι) : (pointMass i).entropy = 0 := by
  apply (pointMass i).entropy_eq_zero_iff.mpr
  exact ⟨i, by simp, fun j hj => by simp [hj]⟩

theorem pointMass_feasible (i : ι) (h : ℝ) : pointMass i ∈ (Feasible h : Set (ProbabilityVector ι)) := by
  simp [Feasible]

theorem feasible_nonempty [Nonempty ι] (h : ℝ) :
    (Feasible h : Set (ProbabilityVector ι)).Nonempty :=
  ⟨pointMass (Classical.choice inferInstance), pointMass_feasible _ h⟩

section Finite
variable [Fintype ι]

/-- The finite probability simplex is closed in its ambient ℓ¹ space. -/
theorem isClosed_simplex : IsClosed
    {p : lp (fun _ : ι => ℝ) 1 | (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1} := by
  have hnonneg : IsClosed {p : lp (fun _ : ι => ℝ) 1 | ∀ i, 0 ≤ p i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous
  have hsum : Continuous (fun p : lp (fun _ : ι => ℝ) 1 => ∑' i, p i) := by
    simp only [tsum_fintype]
    exact continuous_finsetSum _ (fun i _ => (lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous)
  exact hnonneg.inter (isClosed_eq hsum continuous_const)

theorem isCompact_simplex : IsCompact
    {p : lp (fun _ : ι => ℝ) 1 | (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1} := by
  let : FiniteDimensional ℝ (lp (fun _ : ι => ℝ) 1) :=
    (lpPiLpₗᵢ (fun _ : ι => ℝ) ℝ (p := 1)).symm.toLinearEquiv.finiteDimensional
  apply (isCompact_closedBall (0 : lp (fun _ : ι => ℝ) 1) 1).of_isClosed_subset isClosed_simplex
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right,
    lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs,
    abs_of_nonneg (hp.1 _), hp.2, le_refl]

noncomputable instance compactSpace : CompactSpace (ProbabilityVector ι) :=
  isCompact_iff_compactSpace.mp isCompact_simplex

theorem isCompact_feasible (h : ℝ) : IsCompact (Feasible h : Set (ProbabilityVector ι)) :=
  (isClosed_feasible h).isCompact

/-- The finite-alphabet attainment assertion of the main theorem, including h=0.
The conclusion is a genuine maximum over all feasible vectors. -/
theorem exists_global_maximizer_finite [Nonempty ι] (t : ℕ) (h : ℝ) (_hh : 0 ≤ h) :
    ∃ p : ProbabilityVector ι, p ∈ Feasible h ∧
      ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t := by
  exact (isCompact_feasible h).exists_isMaxOn (feasible_nonempty h)
    (continuous_objective t).continuousOn

end Finite
end EntropyConstrainedMissingMass.ProbabilityVector
