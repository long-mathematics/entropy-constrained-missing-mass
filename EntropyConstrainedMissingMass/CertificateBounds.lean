import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Rational enclosures for the branch objective

Appendix D bounds the objective of an entropy root using only a bracket for
that root. The inequalities here apply to any point in the closed bracket,
all real multiplicities at least one, and all natural sample sizes.
-/

namespace EntropyConstrainedMissingMass

/-- The missing-mass objective of one exceptional atom and an equimass block,
extended algebraically to real multiplicities. -/
noncomputable def branchObjective (m : ℝ) (t : ℕ) (z : ℝ) : ℝ :=
  z * (1 - z) ^ t + (1 - z) * (1 - (1 - z) / m) ^ t

/-- Appendix D's lower and upper rational enclosures of the branch objective. -/
theorem objective_certificate (m a z b : ℝ) (t : ℕ)
    (hm : 1 ≤ m) (ha : 0 ≤ a) (haz : a ≤ z) (hzb : z ≤ b) (hb : b ≤ 1) :
    a * (1 - b) ^ t + (1 - b) * (1 - (1 - a) / m) ^ t ≤
        branchObjective m t z ∧
      branchObjective m t z ≤
        b * (1 - a) ^ t + (1 - a) * (1 - (1 - b) / m) ^ t := by
  have hmpos : 0 < m := by linarith
  have hz : 0 ≤ z := ha.trans haz
  have hbzero : 0 ≤ b := hz.trans hzb
  have hza : z ≤ 1 := hzb.trans hb
  have hab : a ≤ b := haz.trans hzb
  have haone : a ≤ 1 := hab.trans hb
  have hbasea : 0 ≤ 1 - (1 - a) / m := by
    have : (1 - a) / m ≤ 1 := (div_le_one hmpos).2 (by linarith)
    linarith
  have hbaseaz : 1 - (1 - a) / m ≤ 1 - (1 - z) / m := by
    have : (1 - z) / m ≤ (1 - a) / m :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hmpos)
    linarith
  have hbasezb : 1 - (1 - z) / m ≤ 1 - (1 - b) / m := by
    have : (1 - b) / m ≤ (1 - z) / m :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hmpos)
    linarith
  have hbasez : 0 ≤ 1 - (1 - z) / m := hbasea.trans hbaseaz
  have hpaz := pow_le_pow_left₀ hbasea hbaseaz t
  have hpzb := pow_le_pow_left₀ hbasez hbasezb t
  have hpheavylo : (1 - b) ^ t ≤ (1 - z) ^ t :=
    pow_le_pow_left₀ (by linarith) (by linarith) t
  have hpheavyhi : (1 - z) ^ t ≤ (1 - a) ^ t :=
    pow_le_pow_left₀ (by linarith) (by linarith) t
  constructor
  · exact add_le_add
      (mul_le_mul haz hpheavylo (by positivity) hz)
      (mul_le_mul (by linarith : 1 - b ≤ 1 - z) hpaz
        (pow_nonneg hbasea t) (by linarith))
  · exact add_le_add
      (mul_le_mul hzb hpheavyhi (by positivity) hbzero)
      (mul_le_mul (by linarith : 1 - z ≤ 1 - a) hpzb
        (pow_nonneg hbasez t) (by linarith))

/-- The integer-multiplicity version used by the exact rational certificates. -/
theorem objective_certificate_nat (m t : ℕ) (a z b : ℝ)
    (hm : 1 ≤ m) (ha : 0 ≤ a) (haz : a ≤ z) (hzb : z ≤ b) (hb : b ≤ 1) :
    a * (1 - b) ^ t + (1 - b) * (1 - (1 - a) / (m : ℝ)) ^ t ≤
        branchObjective (m : ℝ) t z ∧
      branchObjective (m : ℝ) t z ≤
        b * (1 - a) ^ t + (1 - a) * (1 - (1 - b) / (m : ℝ)) ^ t := by
  exact objective_certificate (m : ℝ) a z b t (by exact_mod_cast hm) ha haz hzb hb

end EntropyConstrainedMissingMass
