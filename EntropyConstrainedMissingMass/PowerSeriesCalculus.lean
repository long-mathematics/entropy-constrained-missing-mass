import EntropyConstrainedMissingMass.CoefficientGeneratingFunctions
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Coefficientwise differentiation of formal power series. Every resulting finite
coefficient identity is an ordinary real derivative statement. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

/-- A formal series of derivatives, defined by actual scalar derivatives of each coefficient. -/
def HasCoeffDerivAt (F : ℝ → PowerSeries ℝ) (D : PowerSeries ℝ) (a : ℝ) : Prop :=
  ∀ n : ℕ, HasDerivAt (fun r => coeff n (F r)) (coeff n D) a

namespace HasCoeffDerivAt
variable {F G : ℝ → PowerSeries ℝ} {D E : PowerSeries ℝ} {a : ℝ}

theorem const (F : PowerSeries ℝ) (a : ℝ) : HasCoeffDerivAt (fun _ => F) 0 a := by
  intro n
  simpa using hasDerivAt_const a (coeff n F)

theorem unique (hD : HasCoeffDerivAt F D a) (hE : HasCoeffDerivAt F E a) : D = E := by
  apply PowerSeries.ext
  intro n
  exact (hD n).unique (hE n)

theorem add (hF : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a) :
    HasCoeffDerivAt (fun r => F r + G r) (D + E) a := by
  intro n
  simp only [map_add]
  exact (hF n).fun_add (hG n)

theorem sub (hF : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a) :
    HasCoeffDerivAt (fun r => F r - G r) (D - E) a := by
  intro n
  simp only [map_sub]
  exact (hF n).fun_sub (hG n)

/-- Product differentiation is a finite Leibniz sum at each coefficient. -/
theorem mul (hF : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a) :
    HasCoeffDerivAt (fun r => F r * G r) (D * G a + F a * E) a := by
  intro n
  simp only [map_add, coeff_mul]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum (fun p (_ : p ∈ Finset.antidiagonal n) => (hF p.1).mul (hG p.2))

theorem congr_of_eventuallyEq (hF : HasCoeffDerivAt F D a)
    (hGF : G =ᶠ[nhds a] F) : HasCoeffDerivAt G D a := by
  intro n
  exact (hF n).congr_of_eventuallyEq (hGF.mono (fun _ h => congrArg (coeff n) h))

/-- A scalar coefficient can be differentiated inside the constant-series embedding. -/
theorem C {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d a) :
    HasCoeffDerivAt (fun r => PowerSeries.C (f r)) (PowerSeries.C d) a := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hf
  · simpa [coeff_C, hn] using hasDerivAt_const a (0 : ℝ)

/-- Inverse differentiation needs only an actual local inverse identity. -/
theorem of_inverse (hQ : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a)
    (hinv : ∀ᶠ r in nhds a, F r * G r = 1) :
    E = -D * (G a) ^ 2 := by
  have hprod : D * G a + F a * E = 0 :=
    (hQ.mul hG).unique ((const 1 a).congr_of_eventuallyEq hinv)
  have hval : F a * G a = 1 := hinv.self_of_nhds
  calc
    E = (F a * G a) * E := by rw [hval, one_mul]
    _ = (D * G a + F a * E) * G a - D * (G a) ^ 2 := by ring
    _ = -D * (G a) ^ 2 := by rw [hprod]; ring

end HasCoeffDerivAt

/-- Every coefficient of the homogeneous generating series varies polynomially in its roots. -/
theorem differentiable_homogeneous3 (n : ℕ) :
    Differentiable ℝ (fun v : Fin 3 → ℝ => homogeneous3 (v 0) (v 1) (v 2) n) := by
  have h2 (n : ℕ) : Differentiable ℝ (fun v : Fin 3 → ℝ => homogeneous2 (v 0) (v 1) n) := by
    induction n with
    | zero => simp only [homogeneous2]; fun_prop
    | succ n ih =>
      simp only [homogeneous2]
      exact ((differentiable_apply 0).pow _).add ((differentiable_apply 1).mul ih)
  induction n with
  | zero => simp only [homogeneous3]; fun_prop
  | succ n ih =>
    simp only [homogeneous3]
    exact (h2 (n + 1)).add ((differentiable_apply 2).mul ih)

/-- A differentiable triple path induces actual derivatives for all generating coefficients. -/
theorem exists_hasCoeffDerivAt_homogeneousSeries (q : ℝ → (Fin 3 → ℝ)) {a : ℝ}
    (hq : DifferentiableAt ℝ q a) :
    ∃ D, HasCoeffDerivAt (fun r => homogeneousSeries (q r 0) (q r 1) (q r 2)) D a := by
  refine ⟨mk (fun n => deriv (fun r => homogeneous3 (q r 0) (q r 1) (q r 2) n) a), ?_⟩
  intro n
  simp only [coeff_homogeneousSeries, coeff_mk]
  exact ((differentiable_homogeneous3 n).differentiableAt.comp a hq).hasDerivAt

end
end EntropyConstrainedMissingMass
