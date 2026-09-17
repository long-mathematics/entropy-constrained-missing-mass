import EntropyConstrainedMissingMass.ZeroCrossing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

/-- A zero weighted moment and a positive tail require a negative positive integer value. -/
theorem exists_negative_integer_of_zero_series {f : ℝ → ℝ}
    (hs : HasSum (fun n : ℕ => f (n + 1) / (n + 1)) 0)
    (hp : ∀ᶠ x in atTop, 0 < f x) : ∃ n : ℕ, f (n + 1) < 0 := by
  by_contra hn
  have hn' : ∀ n : ℕ, 0 ≤ f (n + 1) := by simpa only [not_exists, not_lt] using hn
  obtain ⟨R, hR⟩ := eventually_atTop.mp hp
  obtain ⟨n, hnR⟩ := exists_nat_gt R
  have hpos : 0 < f (n + 1) := hR _ (by linarith)
  have hsum := hs.summable.tsum_pos (fun n => div_nonneg (hn' n) (by positivity)) n
    (div_pos hpos (by positivity))
  rw [hs.tsum_eq] at hsum
  exact lt_irrefl _ hsum

/-- The coefficient of the largest positive base determines the eventual sign. -/
theorem eventually_pos_four_term (A B C D a b c d : ℝ)
    (hD : 0 < D) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (had : a < d) (hbd : b < d) (hcd : c < d) :
    ∀ᶠ x : ℝ in atTop, 0 < A * a ^ x - B * b ^ x - C * c ^ x + D * d ^ x := by
  have hd : 0 < d := ha.trans had
  have hr (v : ℝ) (hv : 0 < v) (hvd : v < d) :
      Tendsto (fun x : ℝ => (v / d) ^ x) atTop (𝓝 0) :=
    tendsto_rpow_atTop_of_base_lt_one _ (by linarith [div_pos hv hd]) ((div_lt_one hd).mpr hvd)
  have ht : Tendsto (fun x : ℝ => A * (a / d) ^ x - B * (b / d) ^ x -
      C * (c / d) ^ x + D) atTop (𝓝 D) := by
    simpa using (((hr a ha had).const_mul A).sub ((hr b hb hbd).const_mul B)).sub
      ((hr c hc hcd).const_mul C) |>.add_const D
  filter_upwards [ht.eventually (Ioi_mem_nhds hD)] with x hx
  have he : (A * a ^ x - B * b ^ x - C * c ^ x + D * d ^ x) / d ^ x =
      A * (a / d) ^ x - B * (b / d) ^ x - C * (c / d) ^ x + D := by
    rw [add_div, sub_div, sub_div]
    simp only [Real.div_rpow ha.le hd.le, Real.div_rpow hb.le hd.le, Real.div_rpow hc.le hd.le]
    field_simp [(Real.rpow_pos_of_pos hd x).ne']
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hd x)).mp (by rwa [he])

end
end EntropyConstrainedMissingMass
