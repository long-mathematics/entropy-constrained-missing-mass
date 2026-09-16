import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The final algebraic step of the entropy-curvature estimate

This module proves the two rational identities at the end of Appendix A and
their strict inequality consequence. The analytic lower bound on curvature is
an explicit hypothesis here; its integral proof is a separate obligation.
-/

namespace EntropyConstrainedMissingMass

/-- Appendix A's completion of the square, with `d = 1 - 3*r` and
`j = v + 3/2`. -/
theorem curvature_square_identity (r v : ℝ) (hd : 1 - 3 * r ≠ 0) :
    (8 / 15 : ℝ) * (v + 3 / 2) +
        (1 - 2 * r * (v + 3 / 2)) ^ 2 / (1 - 3 * r) -
        (36 - 48 * r) / 25 =
      (2 * r * v - 3 * (1 - 3 * r) / 5) ^ 2 / (1 - 3 * r) +
        (8 / 15 : ℝ) * (1 - 3 * r) * v := by
  field_simp
  ring

/-- The final strict remainder in Appendix A. -/
theorem curvature_strict_remainder_identity (r : ℝ) :
    (1 + r) * ((36 - 48 * r) / 25) - (16 / 15 : ℝ) =
      4 * (1 - 3 * r) * (12 * r + 7) / 75 := by
  ring

/-- The normalized rational inequality needed for the nonuniform case. -/
theorem curvature_normalized_strict (r j : ℝ)
    (hr : 0 < r) (hrthird : r < 1 / 3) (hj : 3 / 2 ≤ j) :
    (16 : ℝ) / (15 * (1 + r)) <
      (8 / 15 : ℝ) * j + (1 - 2 * r * j) ^ 2 / (1 - 3 * r) := by
  have hd : 0 < 1 - 3 * r := by linarith
  have hv : 0 ≤ j - 3 / 2 := by linarith
  have hsq := curvature_square_identity r (j - 3 / 2) (ne_of_gt hd)
  have hnonneg :
      0 ≤ (2 * r * (j - 3 / 2) - 3 * (1 - 3 * r) / 5) ^ 2 /
          (1 - 3 * r) + (8 / 15 : ℝ) * (1 - 3 * r) * (j - 3 / 2) := by
    positivity
  have hlow : (36 - 48 * r) / 25 ≤
      (8 / 15 : ℝ) * j + (1 - 2 * r * j) ^ 2 / (1 - 3 * r) := by
    simp only [sub_add_cancel] at hsq
    linarith only [hsq, hnonneg]
  have hrem := curvature_strict_remainder_identity r
  have hpos : 0 < 4 * (1 - 3 * r) * (12 * r + 7) / 75 := by positivity
  have hmiddle : (16 : ℝ) / (15 * (1 + r)) < (36 - 48 * r) / 25 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 15 * (1 + r))).2
    nlinarith
  exact lt_of_lt_of_le hmiddle hlow

/-- Scaling the normalized inequality back to the variables of Appendix A.
The displayed integral lower bound is assumed, not postulated as an axiom. -/
theorem entropy_curvature_strict_of_lower_bound (S m I1 K : ℝ)
    (hS : 0 < S) (hm : 0 < m) (hmS : m < S / 3)
    (hI1 : 3 / 2 ≤ S * I1)
    (hK : (8 / 15 : ℝ) * I1 + (1 - 2 * m * I1) ^ 2 / (S - 3 * m) ≤ K) :
    (16 : ℝ) / (15 * (S + m)) < K := by
  have hD : 0 < S - 3 * m := by linarith
  have hr : 0 < m / S := div_pos hm hS
  have hrthird : m / S < 1 / 3 := by
    apply (div_lt_iff₀ hS).2
    linarith
  have hnd : 0 < 1 - 3 * (m / S) := by linarith
  have hn := curvature_normalized_strict (m / S) (S * I1) hr hrthird hI1
  have hscale :
      (8 / 15 : ℝ) * (S * I1) +
          (1 - 2 * (m / S) * (S * I1)) ^ 2 / (1 - 3 * (m / S)) =
        S * ((8 / 15 : ℝ) * I1 + (1 - 2 * m * I1) ^ 2 / (S - 3 * m)) := by
    field_simp
  have htarget :
      ((16 : ℝ) / (15 * (1 + m / S))) / S = (16 : ℝ) / (15 * (S + m)) := by
    field_simp
  have hdiv := div_lt_div_of_pos_right hn hS
  rw [hscale, htarget, mul_div_cancel_left₀ _ (ne_of_gt hS)] at hdiv
  exact lt_of_lt_of_le hdiv hK

/-- The uniform-triple algebraic endpoint, after the integrals are evaluated. -/
theorem entropy_curvature_uniform_endpoint (a : ℝ) :
    (4 : ℝ) / (15 * a) = 16 / (15 * (3 * a + a)) := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp
    ring

end EntropyConstrainedMissingMass
