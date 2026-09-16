import EntropyConstrainedMissingMass.CoefficientPartialFractions

/-! The zero-index Turán convention and the exact decreasing-ratio consequences. -/

namespace EntropyConstrainedMissingMass

theorem homogeneous3_turan_all (x y z : ℝ) (n : ℕ) :
    homogeneous3 x y z n ^ 2 - previousHomogeneous3 x y z n * homogeneous3 x y z (n + 1) =
      homogeneous3 (x * y) (x * z) (y * z) n := by
  cases n with
  | zero => simp [previousHomogeneous3]
  | succ n => exact homogeneous3_turan x y z n

theorem homogeneous3_turan_nonneg {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ homogeneous3 x y z n ^ 2 - previousHomogeneous3 x y z n * homogeneous3 x y z (n + 1) := by
  rw [homogeneous3_turan_all]
  exact homogeneous3_nonneg (mul_nonneg hx hy) (mul_nonneg hx hz) (mul_nonneg hy hz) n

/-- The sequence here starts at source ratio h₁/h₀. -/
theorem homogeneous3_ratio_antitone {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    Antitone (fun n => homogeneous3 x y z (n + 1) / homogeneous3 x y z n) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [div_le_div_iff₀ (homogeneous3_pos_of_ne_zero hx hy hz hne (n + 1))
    (homogeneous3_pos_of_ne_zero hx hy hz hne n)]
  simpa only [Nat.add_assoc, pow_two, mul_comm] using homogeneous3_log_concave hx hy hz n

theorem homogeneous3_ratio_strictAnti {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    StrictAnti (fun n => homogeneous3 x y z (n + 1) / homogeneous3 x y z n) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [div_lt_div_iff₀ (homogeneous3_pos hx.le hy.le hz (n + 1))
    (homogeneous3_pos hx.le hy.le hz n)]
  simpa only [Nat.add_assoc, pow_two, mul_comm] using homogeneous3_strict_log_concave hx hy hz n

end EntropyConstrainedMissingMass
