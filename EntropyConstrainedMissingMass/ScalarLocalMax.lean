import Mathlib.Analysis.Calculus.DerivativeTest

namespace EntropyConstrainedMissingMass
open Filter
open scoped Topology

/-- A continuous scalar function has nonpositive second derivative at a local maximum. -/
theorem second_derivative_nonpos_of_localMax {f : ℝ → ℝ} {a : ℝ}
    (hc : ContinuousAt f a) (hm : IsLocalMax f a) : deriv (deriv f) a ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) a := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hm, hmin] with x hx hy
    exact le_antisymm hx hy
  have hz := heq.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  linarith

end EntropyConstrainedMissingMass
