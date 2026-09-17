import EntropyConstrainedMissingMass.FinitePerturbation
import EntropyConstrainedMissingMass.Quasiconvexity
import EntropyConstrainedMissingMass.ScalarLocalMax

/-! Actual finite-coordinate perturbations at repeated atom sizes. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology ENNReal

theorem negMulLog_symmetric_pair_le {a ε : ℝ} (hε : |ε| ≤ a) :
    Real.negMulLog (a + ε) + Real.negMulLog (a - ε) ≤ 2 * Real.negMulLog a := by
  have he := abs_le.mp hε
  have h := Real.concaveOn_negMulLog.2
    (show a + ε ∈ Ici 0 by change 0 ≤ a + ε; linarith)
    (show a - ε ∈ Ici 0 by change 0 ≤ a - ε; linarith)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have heq : (1 / 2 : ℝ) • (a + ε) + (1 / 2 : ℝ) • (a - ε) = a := by
    simp only [smul_eq_mul]
    ring
  rw [heq] at h
  simp only [smul_eq_mul] at h
  linarith

theorem second_derivative_symmetric_pair {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (a : ℝ) (hdf : DifferentiableAt ℝ (deriv f) a) :
    deriv (deriv (fun ε => f (a + ε) + f (a - ε))) 0 = 2 * deriv (deriv f) a := by
  have hfirst (ε : ℝ) : HasDerivAt (fun e => f (a + e) + f (a - e))
      (deriv f (a + ε) - deriv f (a - ε)) ε := by
    convert ((hf (a + ε)).hasDerivAt.comp ε ((hasDerivAt_id ε).const_add a)).add
      ((hf (a - ε)).hasDerivAt.comp ε ((hasDerivAt_id ε).const_sub a)) using 1
    · rfl
    · ring
  have heq : deriv (fun ε => f (a + ε) + f (a - ε)) =
      fun ε => deriv f (a + ε) - deriv f (a - ε) := funext (fun ε => (hfirst ε).deriv)
  rw [heq]
  have hp : HasDerivAt (deriv f) (deriv (deriv f) a) (a + 0) := by simpa using hdf.hasDerivAt
  have hm : HasDerivAt (deriv f) (deriv (deriv f) a) (a - 0) := by simpa using hdf.hasDerivAt
  have hd := (hp.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add a)).sub
    (hm.comp 0 ((hasDerivAt_id (0 : ℝ)).const_sub a))
  convert hd.deriv using 1
  · rfl
  · ring

/-- Cauchy's mean-value theorem realizes the logarithmic secant slope as `u f''(u)`.
This gives the same contradiction as the manuscript's weighted-integral average. -/
theorem exists_weighted_second_derivative_eq_log_secant {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hc : ContinuousOn (deriv f) (Icc x y))
    (hd : DifferentiableOn ℝ (deriv f) (Ioo x y)) :
    ∃ v ∈ Ioo x y, v * deriv (deriv f) v =
      (deriv f y - deriv f x) / (Real.log y - Real.log x) := by
  have hlogc : ContinuousOn Real.log (Icc x y) := by
    intro u hu
    exact (Real.continuousAt_log (ne_of_gt (hx.trans_le hu.1))).continuousWithinAt
  have hlogd : DifferentiableOn ℝ Real.log (Ioo x y) := by
    intro u hu
    exact (Real.differentiableAt_log (ne_of_gt (hx.trans hu.1))).differentiableWithinAt
  obtain ⟨v, hv, heq⟩ := exists_ratio_deriv_eq_ratio_slope (deriv f) hxy hc hd
    Real.log hlogc hlogd
  have hv0 : v ≠ 0 := ne_of_gt (hx.trans hv.1)
  have hL : Real.log y - Real.log x ≠ 0 := ne_of_gt (sub_pos.mpr (Real.log_lt_log hx hxy))
  refine ⟨v, hv, ?_⟩
  rw [Real.deriv_log] at heq
  apply (eq_div_iff hL).2
  have heq' := congrArg (fun r : ℝ => r * v) heq
  simp only [mul_assoc, inv_mul_cancel₀ hv0, mul_one] at heq'
  nlinarith only [heq']

/-- Strict quasiconvexity excludes the two second-variation endpoint inequalities. -/
theorem not_both_weighted_second_derivative_bounds {f : ℝ → ℝ} {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hc : ContinuousOn (deriv f) (Icc x y))
    (hd : DifferentiableOn ℝ (deriv f) (Ioo x y))
    (hq : ∀ v ∈ Ioo x y, v * deriv (deriv f) v <
      max (x * deriv (deriv f) x) (y * deriv (deriv f) y)) :
    ¬(x * deriv (deriv f) x ≤ (deriv f y - deriv f x) / (Real.log y - Real.log x) ∧
      y * deriv (deriv f) y ≤ (deriv f y - deriv f x) / (Real.log y - Real.log x)) := by
  obtain ⟨v, hv, heq⟩ := exists_weighted_second_derivative_eq_log_secant hx hxy hc hd
  intro hb
  have hstrict := hq v hv
  rw [heq] at hstrict
  exact (not_lt_of_ge (max_le hb.1 hb.2)) hstrict

namespace ProbabilityVector
variable {ι : Type*}
local instance repeatedSizeDecidableEq : DecidableEq ι := Classical.decEq ι

def repeatedPairValues (p : ProbabilityVector ι) (i : ι) (ε : ℝ) (k : ι) : ℝ :=
  if k = i then p.coord i + ε else p.coord i - ε

theorem repeatedPairValues_nonneg (p : ProbabilityVector ι) {i j : ι} {ε : ℝ}
    (hε : |ε| ≤ p.coord i) (k : ι) (_hk : k ∈ ({i, j} : Finset ι)) :
    0 ≤ repeatedPairValues p i ε k := by
  have hab := abs_le.mp hε
  unfold repeatedPairValues
  split_ifs <;> linarith

theorem sum_repeatedPairValues (p : ProbabilityVector ι) {i j : ι} (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) :
    ∑ k ∈ ({i, j} : Finset ι), repeatedPairValues p i ε k =
      ∑ k ∈ ({i, j} : Finset ι), p.coord k := by
  simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]

/-- Split a repeated pair symmetrically; outside the nonnegative range leave the vector unchanged. -/
def perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) : ProbabilityVector ι :=
  if hε : |ε| ≤ p.coord i then
    p.replaceFinite {i, j} (repeatedPairValues p i ε)
      (repeatedPairValues_nonneg p hε) (sum_repeatedPairValues p hij heq ε)
  else p

theorem dist_perturbRepeatedPair_le (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) :
    dist (perturbRepeatedPair p i j hij heq ε) p ≤ 2 * |ε| := by
  unfold perturbRepeatedPair
  split_ifs with hε
  · rw [dist_replaceFinite]
    simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
    linarith
  · simp

theorem tendsto_perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) :
    Tendsto (perturbRepeatedPair p i j hij heq) (𝓝 0) (𝓝 p) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (dist_perturbRepeatedPair_le p i j hij heq)
  simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
    ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).abs)

theorem entropy_perturbRepeatedPair_le (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) (hp : p.entropy ≠ ⊤) :
    (perturbRepeatedPair p i j hij heq ε).entropy ≤ p.entropy := by
  unfold perturbRepeatedPair
  split_ifs with hε
  · apply (ENNReal.toReal_le_toReal (entropy_replaceFinite_ne_top _ _ _ _ _ hp) hp).mp
    rw [entropy_toReal_replaceFinite _ _ _ _ _ hp]
    have hs := negMulLog_symmetric_pair_le hε
    simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
    linarith
  · exact le_rfl

theorem objective_perturbRepeatedPair (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (ε : ℝ) (hε : |ε| ≤ p.coord i) (t : ℕ) :
    (perturbRepeatedPair p i j hij heq ε).objective t = p.objective t +
      missingMassTerm t (p.coord i + ε) + missingMassTerm t (p.coord i - ε) -
        2 * missingMassTerm t (p.coord i) := by
  rw [perturbRepeatedPair, dite_eq_left hε, objective_replaceFinite]
  simp [Finset.sum_pair hij, repeatedPairValues, hij.symm, heq]
  ring

/-- Local maximality in the actual ℓ¹ space passes to the symmetric pair variation. -/
theorem localMax_symmetric_pair_of_repeated (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (hp : LocalMaximizer t h p) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (hi : 0 < p.coord i) :
    IsLocalMax (fun ε : ℝ => missingMassTerm t (p.coord i + ε) +
      missingMassTerm t (p.coord i - ε)) 0 := by
  have hfin := finite_entropy_of_feasible hp.1
  have hlocal : {q : ProbabilityVector ι | q.objective t ≤ p.objective t} ∈ 𝓝[Feasible h] p := hp.2
  obtain ⟨u, hu, hule⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlocal
  have hq := (tendsto_perturbRepeatedPair p i j hij heq).eventually hu
  have habs : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < p.coord i := by
    exact (continuous_abs.tendsto (0 : ℝ)).eventually (by simpa using eventually_lt_nhds hi)
  filter_upwards [hq, habs] with ε hεu hε
  have hfeas : perturbRepeatedPair p i j hij heq ε ∈ Feasible h :=
    (entropy_perturbRepeatedPair_le p i j hij heq ε hfin).trans hp.1
  have hobj : (perturbRepeatedPair p i j hij heq ε).objective t ≤ p.objective t :=
    hule ⟨hεu, hfeas⟩
  rw [objective_perturbRepeatedPair p i j hij heq ε hε.le t] at hobj
  simp only [add_zero, sub_zero]
  linarith

/-- An actually repeated positive coordinate at an ℓ¹ local maximum has nonpositive curvature. -/
theorem repeated_size_second_derivative_nonpos (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (hi : 0 < p.coord i) :
    deriv (deriv (missingMassTerm t)) (p.coord i) ≤ 0 := by
  by_cases ht1 : t = 1
  · subst t
    have hw := weightedCurvature_one (p.coord i)
    unfold weightedCurvature at hw
    nlinarith
  have ht2 : 2 ≤ t := by omega
  have hd : Differentiable ℝ (missingMassTerm t) := by
    unfold missingMassTerm
    fun_prop
  have hpair := localMax_symmetric_pair_of_repeated p hp i j hij heq hi
  have hc : ContinuousAt (fun ε : ℝ => missingMassTerm t (p.coord i + ε) +
      missingMassTerm t (p.coord i - ε)) 0 := by
    unfold missingMassTerm
    fun_prop
  have hsecond := second_derivative_nonpos_of_localMax hc hpair
  rw [second_derivative_symmetric_pair hd (p.coord i)
    (hasDerivAt_deriv_missingMassTerm t ht2 (p.coord i)).differentiableAt] at hsecond
  linarith

theorem repeated_size_le_half (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) : p.coord i ≤ 1 / 2 := by
  have hs := p.summable_coord.sum_le_tsum ({i, j} : Finset ι) (fun k _ => p.coord_nonneg k)
  rw [p.tsum_coord] at hs
  simp only [Finset.sum_pair hij, heq] at hs
  linarith

theorem repeated_size_mem_negativeCurvatureInterval (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (i j : ι) (hij : i ≠ j)
    (heq : p.coord j = p.coord i) (hi : 0 < p.coord i) :
    p.coord i ∈ negativeCurvatureInterval t := by
  have hhalf := repeated_size_le_half p i j hij heq
  have hi1 : p.coord i < 1 := by linarith
  refine ⟨hi, hi1, ?_⟩
  by_cases ht1 : t = 1
  · subst t
    norm_num
    exact hi1.le
  have ht2 : 2 ≤ t := by omega
  exact (deriv2_missingMassTerm_nonpos_iff t ht2 hi1).mp
    (repeated_size_second_derivative_nonpos p ht hp i j hij heq hi)

end ProbabilityVector
end
end EntropyConstrainedMissingMass
