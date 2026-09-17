import EntropyConstrainedMissingMass.Quasiconvexity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The explicit radical roots used in the exceptional-atom proof. -/
namespace EntropyConstrainedMissingMass
noncomputable section

def curvatureRootMinus (t : ℝ) : ℝ := (2*t - Real.sqrt (2*t*(t-1))) / (t*(t+1))
def curvatureRootPlus (t : ℝ) : ℝ := (2*t + Real.sqrt (2*t*(t-1))) / (t*(t+1))

theorem curvature_roots_order {t : ℝ} (ht : 1 < t) :
    0 < curvatureRootMinus t ∧ curvatureRootMinus t < 2/(t+1) ∧
      2/(t+1) < curvatureRootPlus t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t+1 := by linarith
  have harg : 0 < 2*t*(t-1) := by positivity
  have hs := Real.sqrt_pos.2 harg
  have hsq := Real.sq_sqrt harg.le
  have hlt : Real.sqrt (2*t*(t-1)) < 2*t := by nlinarith
  have hden : 0 < t*(t+1) := mul_pos ht0 ht1
  dsimp [curvatureRootMinus, curvatureRootPlus]
  refine ⟨div_pos (by linarith) hden, ?_, ?_⟩
  · apply (div_lt_div_iff₀ hden ht1).2
    nlinarith [mul_pos hs ht1]
  · apply (div_lt_div_iff₀ ht1 hden).2
    nlinarith [mul_pos hs ht1]

theorem curvature_quadratic_factor {t : ℕ} (ht : 2 ≤ t) (u : ℝ) :
    curvatureDerivativeQuadratic t u = (t : ℝ)*((t : ℝ)+1)*
      (u-curvatureRootMinus t)*(u-curvatureRootPlus t) := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1 : ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have hs := Real.sq_sqrt (show 0 ≤ 2*(t : ℝ)*((t : ℝ)-1) by positivity)
  dsimp [curvatureDerivativeQuadratic, curvatureRootMinus, curvatureRootPlus]
  field_simp
  simp only [mul_comm (t : ℝ) 2] at *
  nlinarith [hs]

theorem curvature_quadratic_roots {t : ℕ} (ht : 2 ≤ t) :
    curvatureDerivativeQuadratic t (curvatureRootMinus t) = 0 ∧
      curvatureDerivativeQuadratic t (curvatureRootPlus t) = 0 := by
  simp [curvature_quadratic_factor ht]

end
end EntropyConstrainedMissingMass
