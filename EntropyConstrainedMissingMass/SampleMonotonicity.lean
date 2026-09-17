import EntropyConstrainedMissingMass.FiniteClassification

/-! Strict decrease of the actual optimized missing mass in integer sample size. -/
namespace EntropyConstrainedMissingMass
namespace ProbabilityVector
variable {ι : Type*}

theorem objective_succ_lt_of_entropy_ne_zero (p : ProbabilityVector ι) (t : ℕ) (hp : p.entropy ≠ 0) :
    p.objective (t+1) < p.objective t := by
  have hle (i : ι) : missingMassTerm (t+1) (p.coord i) ≤ missingMassTerm t (p.coord i) := by
    unfold missingMassTerm
    rw [pow_succ]
    have hn : 0 ≤ p.coord i*(1-p.coord i)^t := mul_nonneg (p.coord_nonneg i)
      (pow_nonneg (sub_nonneg.mpr (p.coord_le_one i)) _)
    nlinarith [p.coord_nonneg i]
  obtain ⟨i,hi⟩ := p.exists_coord_pos
  have hi1 : p.coord i < 1 := by
    apply lt_of_le_of_ne (p.coord_le_one i)
    intro he
    exact hp (p.entropy_eq_zero_iff.mpr ⟨i,he,fun j hj => p.coord_eq_zero_of_coord_eq_one he hj⟩)
  have hlt : missingMassTerm (t+1) (p.coord i) < missingMassTerm t (p.coord i) := by
    unfold missingMassTerm
    rw [pow_succ]
    have hpos : 0 < p.coord i*(1-p.coord i)^t := mul_pos hi (pow_pos (sub_pos.mpr hi1) _)
    nlinarith
  exact Summable.tsum_lt_tsum hle hlt (p.objective_summable (t+1)) (p.objective_summable t)

end ProbabilityVector

/-- Strict monotonicity also includes the comparison from zero to one samples. -/
theorem optimalValue_succ_lt (t : ℕ) {h : ℝ} (hh : 0 < h) :
    optimalValue (t+1) h < optimalValue t h := by
  obtain ⟨p,_,hp,hmax⟩ := ProbabilityVector.exists_global_maximizer_countable (t+1) h hh.le
  have hlocal : ProbabilityVector.LocalMaximizer (t+1) h p :=
    ⟨hp,(show IsMaxOn (fun q => q.objective (t+1)) (ProbabilityVector.Feasible h) p from hmax).isLocalMaxOn⟩
  have he := p.entropy_saturation_of_localMax (by omega : 1 ≤ t+1) hlocal
  rw [optimalValue_eq_of_globalMax p (t+1) hp hmax]
  exact (p.objective_succ_lt_of_entropy_ne_zero t (by rw [he]; exact (ENNReal.ofReal_pos.mpr hh).ne')).trans_le
    (objective_le_optimalValue p t hp)

theorem strictAnti_optimalValue {h : ℝ} (hh : 0 < h) : StrictAnti (fun t : ℕ => optimalValue t h) :=
  strictAnti_nat_of_succ_lt (fun t => optimalValue_succ_lt t hh)

theorem optimalValue_pos (t : ℕ) {h : ℝ} (hh : 0 < h) : 0 < optimalValue t h := by
  have hn : 0 ≤ optimalValue (t+1) h := (ProbabilityVector.objective_nonneg (canonicalLight h hh) _).trans
    (objective_le_optimalValue _ _ (canonicalLight_feasible hh))
  exact hn.trans_lt (optimalValue_succ_lt t hh)

end EntropyConstrainedMissingMass
