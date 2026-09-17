import EntropyConstrainedMissingMass.TwoSizeReduction
import EntropyConstrainedMissingMass.EntropyCurvature
import EntropyConstrainedMissingMass.CountableAttainment

/-! The manuscript's main two-size, finite-support, attainment, and saturation theorem. -/
namespace EntropyConstrainedMissingMass
noncomputable section

namespace TripleGeometry

/-- No local maximum can contain an ordered triple of distinct positive masses. -/
theorem not_localMax_three_sizes {ι : Type*} {h : ℝ} (p : ProbabilityVector ι)
    (t : ℕ) (ht : 1 ≤ t) (e : Fin 3 ↪ ι) (h0 : 0 < p.coord (e 0))
    (h01 : p.coord (e 0) < p.coord (e 1)) (h12 : p.coord (e 1) < p.coord (e 2)) :
    ¬ ProbabilityVector.LocalMaximizer t h p := by
  rcases t with _ | _ | n
  · omega
  · exact not_localMax_three_sizes_one p e h0 h01 h12
  · exact not_localMax_three_sizes_of_curvature_bound p n e h0 h01 h12
      (Curvature.entropy_curvature_bound _ _ _ h0 (h0.trans h01) (h0.trans (h01.trans h12)))

end TripleGeometry
namespace ProbabilityVector
variable {ι : Type*}

/-- At most two positive atom sizes, without assuming finite support or a finite alphabet. -/
theorem two_sizes_of_localMax (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p.coord i = 0 ∨ p.coord i = a ∨ p.coord i = b := by
  apply p.exists_two_sizes_of_no_ordered_triple
  intro e h0 h01 h12
  exact TripleGeometry.not_localMax_three_sizes p t ht e h0 h01 h12 hp

/-- Finite support is a conclusion for arbitrary alphabets, not a hypothesis. -/
theorem finite_support_of_localMax (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) : (Function.support p.coord).Finite := by
  obtain ⟨a, b, ha, hb, hc⟩ := p.two_sizes_of_localMax ht hp
  exact p.finite_support_of_two_sizes ha hb hc

/-- Every local maximum saturates entropy on any infinite alphabet. -/
theorem entropy_saturation_of_localMax [Infinite ι] (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) : p.entropy = ENNReal.ofReal h :=
  p.entropy_saturation_of_finite_support ht hp (p.finite_support_of_localMax ht hp)

theorem entropy_toReal_saturation_of_localMax [Infinite ι] (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hh : 0 ≤ h) (hp : LocalMaximizer t h p) : p.entropy.toReal = h := by
  rw [p.entropy_saturation_of_localMax ht hp, ENNReal.toReal_ofReal hh]

/-- Theorem `thm:main`, with the infinite-alphabet saturation clause separately reusable. -/
theorem main_theorem [Countable ι] [Nonempty ι] (t : ℕ) (h : ℝ) (ht : 1 ≤ t) (hh : 0 ≤ h) :
    (∀ p : ProbabilityVector ι, LocalMaximizer t h p →
      (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ i, p.coord i = 0 ∨ p.coord i = a ∨ p.coord i = b) ∧
      (Function.support p.coord).Finite) ∧
    (∃ p : ProbabilityVector ι, p ∈ Feasible h ∧
      ∀ q : ProbabilityVector ι, q ∈ Feasible h → q.objective t ≤ p.objective t) ∧
    (Infinite ι → ∀ p : ProbabilityVector ι, LocalMaximizer t h p →
      p.entropy = ENNReal.ofReal h ∧ p.entropy.toReal = h) := by
  refine ⟨fun p hp => ⟨p.two_sizes_of_localMax ht hp, p.finite_support_of_localMax ht hp⟩,
    exists_global_maximizer t h hh, ?_⟩
  intro hι p hp
  let := hι
  exact ⟨p.entropy_saturation_of_localMax ht hp, p.entropy_toReal_saturation_of_localMax ht hh hp⟩

end ProbabilityVector
end
end EntropyConstrainedMissingMass
