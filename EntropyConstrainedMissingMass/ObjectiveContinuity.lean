import EntropyConstrainedMissingMass.Probability
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! An explicit ℓ¹ Lipschitz bound, valid also for countable alphabets.
This uses an algebraic estimate instead of choosing the maximum of a derivative. -/

namespace EntropyConstrainedMissingMass

theorem abs_pow_sub_pow_le_on_unit (t : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |x ^ t - y ^ t| ≤ t * |x - y| := by
  have hmax : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  have hmax1 : max |x| |y| ≤ 1 := by
    rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]
    exact max_le hx.2 hy.2
  calc
    |x ^ t - y ^ t| ≤ |x - y| * t * max |x| |y| ^ (t - 1) := abs_pow_sub_pow_le x y t
    _ ≤ |x - y| * t * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ hmax hmax1) (by positivity)
    _ = t * |x - y| := by ring

theorem missingMassTerm_lipschitz (t : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    |missingMassTerm t x - missingMassTerm t y| ≤ (t + 1) * |x - y| := by
  have hp := abs_pow_sub_pow_le_on_unit t
    (show 1 - x ∈ Set.Icc 0 1 by constructor <;> linarith [hx.1, hx.2])
    (show 1 - y ∈ Set.Icc 0 1 by constructor <;> linarith [hy.1, hy.2])
  have hsub : |1 - x - (1 - y)| = |x - y| := by
    rw [show 1 - x - (1 - y) = -(x - y) by ring, abs_neg]
  rw [hsub] at hp
  have hpow : |(1 - x) ^ t| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) _)]
    exact pow_le_one₀ (sub_nonneg.mpr hx.2) (by linarith [hx.1])
  have hyabs : |y| ≤ 1 := by simpa [abs_of_nonneg hy.1] using hy.2
  calc
    |missingMassTerm t x - missingMassTerm t y| =
      |(x - y) * (1 - x) ^ t + y * ((1 - x) ^ t - (1 - y) ^ t)| := by
        congr 1
        unfold missingMassTerm
        ring
    _ ≤ |x - y| * |(1 - x) ^ t| + |y| * |(1 - x) ^ t - (1 - y) ^ t| := by
      simpa only [abs_mul] using abs_add_le ((x - y) * (1 - x) ^ t)
        (y * ((1 - x) ^ t - (1 - y) ^ t))
    _ ≤ |x - y| * 1 + 1 * (t * |x - y|) := by gcongr
    _ = (t + 1) * |x - y| := by ring

namespace ProbabilityVector
variable {ι : Type*}

theorem objective_dist_le (p q : ProbabilityVector ι) (t : ℕ) :
    |p.objective t - q.objective t| ≤ (t + 1) * dist p q := by
  have hs := (p.objective_summable t).sub (q.objective_summable t)
  have hd := (p.summable_coord.sub q.summable_coord).abs
  have hn : Summable (fun i => ‖missingMassTerm t (p.coord i) - missingMassTerm t (q.coord i)‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  rw [objective, objective, ← (p.objective_summable t).tsum_sub (q.objective_summable t)]
  calc
    |∑' i, (missingMassTerm t (p.coord i) - missingMassTerm t (q.coord i))| ≤
      ∑' i, |missingMassTerm t (p.coord i) - missingMassTerm t (q.coord i)| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i, ((t : ℝ) + 1) * |p.coord i - q.coord i| :=
      hs.abs.tsum_le_tsum (fun i => missingMassTerm_lipschitz t
        ⟨p.coord_nonneg i, p.coord_le_one i⟩ ⟨q.coord_nonneg i, q.coord_le_one i⟩)
        (hd.mul_left _)
    _ = (t + 1) * dist p q := by rw [tsum_mul_left, p.dist_eq_tsum q]

theorem objective_lipschitz (t : ℕ) :
    LipschitzWith (t + 1) (fun p : ProbabilityVector ι => p.objective t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [Real.dist_eq, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using
    p.objective_dist_le q t

theorem continuous_objective (t : ℕ) :
    Continuous (fun p : ProbabilityVector ι => p.objective t) :=
  (objective_lipschitz t).continuous

end ProbabilityVector
end EntropyConstrainedMissingMass
