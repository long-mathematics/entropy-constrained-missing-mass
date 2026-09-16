import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Order.LocalExtr

/-! Probability vectors with their genuine ℓ¹ metric, extended entropy, and missing mass.
The index type is arbitrary: in particular finite and countably infinite types are covered.
No finite support or entropy summability is part of the probability-vector definition. -/

open scoped ENNReal

namespace EntropyConstrainedMissingMass

/-- Nonnegative unit-mass elements of ℓ¹, with the induced metric. -/
def ProbabilityVector (ι : Type*) :=
  {p : lp (fun _ : ι => ℝ) 1 // (∀ i, 0 ≤ p i) ∧ (∑' i, p i) = 1}

namespace ProbabilityVector

variable {ι : Type*}

noncomputable instance : MetricSpace (ProbabilityVector ι) := inferInstanceAs (MetricSpace (Subtype _))

noncomputable def coord (p : ProbabilityVector ι) (i : ι) : ℝ := p.val i

@[simp] theorem coord_nonneg (p : ProbabilityVector ι) (i : ι) : 0 ≤ p.coord i := p.property.1 i

@[simp] theorem tsum_coord (p : ProbabilityVector ι) : (∑' i, p.coord i) = 1 := p.property.2

theorem summable_coord (p : ProbabilityVector ι) : Summable p.coord :=
  p.val.property.summable_of_one

theorem coord_le_one (p : ProbabilityVector ι) (i : ι) : p.coord i ≤ 1 := by
  rw [← p.tsum_coord]
  exact p.summable_coord.le_tsum i (fun j _ => p.coord_nonneg j)

/-- The ℓ¹ representation accepts every nonnegative real probability series. -/
noncomputable def ofHasSum (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    ProbabilityVector ι :=
  ⟨⟨p, memℓp_gen (by simpa [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hs.summable)⟩,
    hn, hs.tsum_eq⟩

@[simp] theorem coord_ofHasSum (p : ι → ℝ) (hn : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    (ofHasSum p hn hs).coord = p := rfl

theorem hasSum_coord (p : ProbabilityVector ι) : HasSum p.coord 1 := by
  simpa using p.summable_coord.hasSum

/-- The induced metric is exactly the manuscript's sum of absolute coordinate differences. -/
theorem dist_eq_tsum (p q : ProbabilityVector ι) :
    dist p q = ∑' i, |p.coord i - q.coord i| := by
  change dist p.val q.val = _
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal)]
  simp [coord, Real.norm_eq_abs]

theorem tsum_abs_coord (p : ProbabilityVector ι) : (∑' i, |p.coord i|) = 1 := by
  simpa only [abs_of_nonneg (p.coord_nonneg _)] using p.tsum_coord

/-- Extended entropy prevents divergent real series from being assigned the value zero. -/
noncomputable def entropy (p : ProbabilityVector ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (p.coord i))

theorem entropy_term_nonneg (p : ProbabilityVector ι) (i : ι) :
    0 ≤ Real.negMulLog (p.coord i) :=
  Real.negMulLog_nonneg (p.coord_nonneg i) (p.coord_le_one i)

theorem entropy_ne_top_iff (p : ProbabilityVector ι) :
    p.entropy ≠ ⊤ ↔ Summable (fun i => Real.negMulLog (p.coord i)) := by
  constructor
  · intro h
    have hs := ENNReal.summable_toReal h
    simpa [ENNReal.toReal_ofReal, p.entropy_term_nonneg] using hs
  · intro h
    rw [entropy, ← ENNReal.ofReal_tsum_of_nonneg p.entropy_term_nonneg h]
    exact ENNReal.ofReal_ne_top

theorem entropy_eq_ofReal_tsum (p : ProbabilityVector ι)
    (h : p.entropy ≠ ⊤) :
    p.entropy = ENNReal.ofReal (∑' i, Real.negMulLog (p.coord i)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg p.entropy_term_nonneg
    (p.entropy_ne_top_iff.mp h)).symm

theorem entropy_toReal (p : ProbabilityVector ι) (h : p.entropy ≠ ⊤) :
    p.entropy.toReal = ∑' i, Real.negMulLog (p.coord i) := by
  rw [p.entropy_eq_ofReal_tsum h, ENNReal.toReal_ofReal (tsum_nonneg p.entropy_term_nonneg)]

end ProbabilityVector

/-- A single atom's contribution after `t` samples; `t=0` is useful for identities. -/
def missingMassTerm (t : ℕ) (u : ℝ) : ℝ := u * (1 - u) ^ t

theorem missingMassTerm_nonneg (t : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 ≤ missingMassTerm t u :=
  mul_nonneg h0 (pow_nonneg (sub_nonneg.mpr h1) _)

theorem missingMassTerm_le (t : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    missingMassTerm t u ≤ u := by
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (sub_nonneg.mpr h1) (sub_le_self _ h0)) h0).trans_eq (mul_one u)

namespace ProbabilityVector
variable {ι : Type*}

theorem objective_summable (p : ProbabilityVector ι) (t : ℕ) :
    Summable (fun i => missingMassTerm t (p.coord i)) :=
  .of_nonneg_of_le
    (fun i => missingMassTerm_nonneg t (p.coord_nonneg i) (p.coord_le_one i))
    (fun i => missingMassTerm_le t (p.coord_nonneg i) (p.coord_le_one i)) p.summable_coord

noncomputable def objective (p : ProbabilityVector ι) (t : ℕ) : ℝ :=
  ∑' i, missingMassTerm t (p.coord i)

theorem objective_nonneg (p : ProbabilityVector ι) (t : ℕ) : 0 ≤ p.objective t :=
  tsum_nonneg (fun i => missingMassTerm_nonneg t (p.coord_nonneg i) (p.coord_le_one i))

theorem objective_le_one (p : ProbabilityVector ι) (t : ℕ) : p.objective t ≤ 1 := by
  rw [← p.tsum_coord]
  exact (p.objective_summable t).tsum_le_tsum
    (fun i => missingMassTerm_le t (p.coord_nonneg i) (p.coord_le_one i)) p.summable_coord

@[simp] theorem objective_zero (p : ProbabilityVector ι) : p.objective 0 = 1 := by
  simp [objective, missingMassTerm]

/-- Feasibility uses extended entropy and a real budget, without any support restriction. -/
def Feasible (h : ℝ) : Set (ProbabilityVector ι) := {p | p.entropy ≤ ENNReal.ofReal h}

/-- This uses the ℓ¹ metric, not the pointwise product topology or stationarity. -/
def LocalMaximizer (t : ℕ) (h : ℝ) (p : ProbabilityVector ι) : Prop :=
  p ∈ Feasible h ∧ IsLocalMaxOn (fun q => q.objective t) (Feasible h) p

theorem finite_entropy_of_feasible {p : ProbabilityVector ι} {h : ℝ}
    (hp : p ∈ Feasible h) : p.entropy ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp

end ProbabilityVector
end EntropyConstrainedMissingMass
