import EntropyConstrainedMissingMass.Probability
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Scalar continuity, differentiation, and the strict atom-splitting inequality
for the missing-mass objective. -/

namespace EntropyConstrainedMissingMass

/-- Each single-atom contribution is a polynomial, hence globally continuous. -/
theorem continuous_missingMassTerm (t : ℕ) : Continuous (missingMassTerm t) := by
  unfold missingMassTerm
  fun_prop

/-- The first derivative in the form used for branch calculations. -/
theorem hasDerivAt_missingMassTerm (t : ℕ) (ht : 1 ≤ t) (u : ℝ) :
    HasDerivAt (missingMassTerm t)
      (((t : ℝ) + 1) * (1 - u) ^ t - (t : ℝ) * (1 - u) ^ (t - 1)) u := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  convert (hasDerivAt_id u).mul (((hasDerivAt_id u).const_sub 1).fun_pow (n + 1)) using 1
  · rfl
  · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul, id_eq]
    rw [pow_succ]
    ring

/-- The explicit first derivative of the scalar objective. -/
theorem deriv_missingMassTerm (t : ℕ) (ht : 1 ≤ t) (u : ℝ) :
    deriv (missingMassTerm t) u =
      ((t : ℝ) + 1) * (1 - u) ^ t - (t : ℝ) * (1 - u) ^ (t - 1) :=
  (hasDerivAt_missingMassTerm t ht u).deriv

/-- The second derivative, valid globally for sample sizes at least two. -/
theorem hasDerivAt_deriv_missingMassTerm (t : ℕ) (ht : 2 ≤ t) (u : ℝ) :
    HasDerivAt (deriv (missingMassTerm t))
      ((t : ℝ) * (1 - u) ^ (t - 2) * (((t : ℝ) + 1) * u - 2)) u := by
  have hfun : deriv (missingMassTerm t) = fun v : ℝ =>
      ((t : ℝ) + 1) * (1 - v) ^ t - (t : ℝ) * (1 - v) ^ (t - 1) := by
    funext v
    exact deriv_missingMassTerm t (by omega) v
  rw [hfun]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  convert ((((hasDerivAt_id u).const_sub 1).fun_pow (2 + n)).const_mul
      (((2 + n : ℕ) : ℝ) + 1)).sub
    ((((hasDerivAt_id u).const_sub 1).fun_pow (2 + n - 1)).const_mul
      ((2 + n : ℕ) : ℝ)) using 1
  · rfl
  · have hn1 : 2 + n - 1 = n + 1 := by omega
    have hn2 : 2 + n - 2 = n := by omega
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, hn1, hn2,
      Nat.add_sub_cancel, id_eq]
    rw [pow_succ]
    ring

/-- The explicit second derivative displayed in the manuscript. -/
theorem deriv_deriv_missingMassTerm (t : ℕ) (ht : 2 ≤ t) (u : ℝ) :
    deriv (deriv (missingMassTerm t)) u =
      (t : ℝ) * (1 - u) ^ (t - 2) * (((t : ℝ) + 1) * u - 2) :=
  (hasDerivAt_deriv_missingMassTerm t ht u).deriv

/-- Splitting a positive atom into two positive atoms strictly increases
missing mass whenever at least one sample is taken. -/
theorem missingMassTerm_split_strict (t : ℕ) (ht : 1 ≤ t) (a ε : ℝ)
    (hε : 0 < ε) (hεa : ε < a) (ha : a ≤ 1) :
    missingMassTerm t a < missingMassTerm t (a - ε) + missingMassTerm t ε := by
  have hbase : 0 ≤ 1 - a := by linarith
  have habase : 1 - a < 1 - (a - ε) := by linarith
  have hεbase : 1 - a < 1 - ε := by linarith
  have hp1 := pow_lt_pow_left₀ habase hbase (by omega : t ≠ 0)
  have hp2 := pow_lt_pow_left₀ hεbase hbase (by omega : t ≠ 0)
  have h1 := mul_lt_mul_of_pos_left hp1 (by linarith : 0 < a - ε)
  have h2 := mul_lt_mul_of_pos_left hp2 hε
  unfold missingMassTerm
  nlinarith

end EntropyConstrainedMissingMass
