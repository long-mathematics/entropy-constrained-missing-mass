import EntropyConstrainedMissingMass.Probability

/-! Coarsening arbitrary alphabets by adding the masses in each fiber.
No countability or finite-support assumption is needed. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector

noncomputable section
open scoped ENNReal
open Set
variable {ι κ : Type*}

/-- Push a probability vector forward by any map, merging all atoms in each fiber. -/
def pushforward (p : ProbabilityVector ι) (f : ι → κ) : ProbabilityVector κ :=
  ofHasSum (fun j => ∑' i : f ⁻¹' {j}, p.coord i)
    (fun _j => tsum_nonneg (fun i => p.coord_nonneg i))
    (p.hasSum_coord.tsum_fiberwise f)

@[simp] theorem coord_pushforward (p : ProbabilityVector ι) (f : ι → κ) (j : κ) :
    (p.pushforward f).coord j = ∑' i : f ⁻¹' {j}, p.coord i := rfl

theorem coord_pushforward_of_fiber_eq_singleton (p : ProbabilityVector ι) (f : ι → κ)
    (j : κ) (i : ι) (hf : f ⁻¹' {j} = {i}) : (p.pushforward f).coord j = p.coord i := by
  rw [coord_pushforward, hf]
  simp

theorem coord_le_pushforward (p : ProbabilityVector ι) (f : ι → κ) (i : ι) :
    p.coord i ≤ (p.pushforward f).coord (f i) := by
  exact (p.summable_coord.subtype (fun k => f k = f i)).le_tsum ⟨i, rfl⟩
    (fun k _ => p.coord_nonneg k)

theorem coord_le_pushforward_of_mem (p : ProbabilityVector ι) (f : ι → κ)
    {j : κ} (i : f ⁻¹' {j}) : p.coord i ≤ (p.pushforward f).coord j := by
  have hi : f i = j := i.property
  simpa only [hi] using p.coord_le_pushforward f i

/-- Merging the atoms of one fiber cannot increase its entropy contribution. -/
theorem negMulLog_pushforward_le (p : ProbabilityVector ι) (f : ι → κ) (j : κ)
    (hp : p.entropy ≠ ⊤) :
    Real.negMulLog ((p.pushforward f).coord j) ≤
      ∑' i : f ⁻¹' {j}, Real.negMulLog (p.coord i) := by
  let a := (p.pushforward f).coord j
  have hs := p.summable_coord.subtype (fun i => f i = j)
  have he := (p.entropy_ne_top_iff.mp hp).subtype (fun i => f i = j)
  calc
    Real.negMulLog a = ∑' i : f ⁻¹' {j}, p.coord i * (-Real.log a) := by
      rw [tsum_mul_right]
      change Real.negMulLog a = a * (-Real.log a)
      simp [Real.negMulLog]
    _ ≤ ∑' i : f ⁻¹' {j}, Real.negMulLog (p.coord i) := by
      apply Summable.tsum_le_tsum _ (hs.mul_right _) he
      intro i
      by_cases hi : p.coord i = 0
      · simp [hi]
      have hi0 : 0 < p.coord i := lt_of_le_of_ne (p.coord_nonneg i) (Ne.symm hi)
      have hlog := Real.log_le_log hi0 (p.coord_le_pushforward_of_mem f i)
      have hmul := mul_le_mul_of_nonneg_left (neg_le_neg hlog) (p.coord_nonneg i)
      simpa only [a, Function.comp_apply, Real.negMulLog, mul_neg, neg_mul] using hmul

/-- Extended entropy cannot increase under any merging of coordinates. -/
theorem entropy_pushforward_le (p : ProbabilityVector ι) (f : ι → κ) :
    (p.pushforward f).entropy ≤ p.entropy := by
  by_cases hp : p.entropy = ⊤
  · simp [hp]
  simp only [entropy]
  rw [← ENNReal.tsum_fiberwise (fun i => ENNReal.ofReal (Real.negMulLog (p.coord i))) f]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun i : f ⁻¹' {j} => p.entropy_term_nonneg i)
    ((p.entropy_ne_top_iff.mp hp).subtype (fun i => f i = j))]
  exact ENNReal.ofReal_le_ofReal (p.negMulLog_pushforward_le f j hp)

theorem finite_entropy_pushforward (p : ProbabilityVector ι) (f : ι → κ)
    (hp : p.entropy ≠ ⊤) : (p.pushforward f).entropy ≠ ⊤ :=
  ne_top_of_le_ne_top hp (p.entropy_pushforward_le f)

theorem feasible_pushforward (p : ProbabilityVector ι) (f : ι → κ) {h : ℝ}
    (hp : p ∈ Feasible h) : p.pushforward f ∈ Feasible h :=
  (p.entropy_pushforward_le f).trans hp

/-- Merging one fiber cannot increase its missing-mass contribution. -/
theorem missingMassTerm_pushforward_le (p : ProbabilityVector ι) (f : ι → κ) (j : κ)
    (t : ℕ) :
    missingMassTerm t ((p.pushforward f).coord j) ≤
      ∑' i : f ⁻¹' {j}, missingMassTerm t (p.coord i) := by
  let a := (p.pushforward f).coord j
  have hs := p.summable_coord.subtype (fun i => f i = j)
  have ho := (p.objective_summable t).subtype (fun i => f i = j)
  calc
    missingMassTerm t a = ∑' i : f ⁻¹' {j}, p.coord i * (1 - a) ^ t := by
      rw [tsum_mul_right]
      rfl
    _ ≤ ∑' i : f ⁻¹' {j}, missingMassTerm t (p.coord i) := by
      apply Summable.tsum_le_tsum _ (hs.mul_right _) ho
      intro i
      apply mul_le_mul_of_nonneg_left _ (p.coord_nonneg i)
      apply pow_le_pow_left₀ (sub_nonneg.mpr ((p.pushforward f).coord_le_one j))
      exact sub_le_sub_left (p.coord_le_pushforward_of_mem f i) 1

/-- Missing mass cannot increase under any merging of coordinates, for all natural sample sizes. -/
theorem objective_pushforward_le (p : ProbabilityVector ι) (f : ι → κ) (t : ℕ) :
    (p.pushforward f).objective t ≤ p.objective t := by
  have hs := (p.objective_summable t).hasSum.tsum_fiberwise f
  simp only [objective]
  rw [← hs.tsum_eq]
  exact Summable.tsum_le_tsum (fun j => p.missingMassTerm_pushforward_le f j t)
    ((p.pushforward f).objective_summable t) hs.summable

end
end EntropyConstrainedMissingMass.ProbabilityVector
