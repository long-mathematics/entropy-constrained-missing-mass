import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact first and second jets of finite sums along quadratic coordinate paths. -/
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter
open scoped Topology

/-- Quadratic coordinate path with prescribed first and second coefficients. -/
def quadraticPath (a b c r : ℝ) : ℝ := a + b * r + c * r ^ 2

@[simp] theorem quadraticPath_zero (a b c : ℝ) : quadraticPath a b c 0 = a := by
  simp [quadraticPath]

theorem hasDerivAt_quadraticPath (a b c r : ℝ) :
    HasDerivAt (quadraticPath a b c) (b + 2 * c * r) r := by
  have hd := ((hasDerivAt_id r).const_mul b |>.const_add a).fun_add
    (((hasDerivAt_id r).pow 2).const_mul c)
  convert hd using 1
  · funext u
    simp [quadraticPath]
  · simp
    ring

theorem hasDerivAt_comp_quadraticPath {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : HasDerivAt f d a) :
    HasDerivAt (fun r => f (quadraticPath a b c r)) (b * d) 0 := by
  have hd : HasDerivAt f d (quadraticPath a b c 0) := by simpa using hf
  simpa only [Function.comp_def, mul_zero, zero_mul, add_zero, mul_comm] using hd.comp 0 (hasDerivAt_quadraticPath a b c 0)

/-- The second derivative includes both the Hessian and path acceleration terms. -/
theorem hasDerivAt_deriv_comp_quadraticPath {f f' : ℝ → ℝ} {a b c d₂ : ℝ}
    (hf : ∀ᶠ u in 𝓝 a, HasDerivAt f (f' u) u)
    (hf' : HasDerivAt f' d₂ a) :
    HasDerivAt (deriv (fun r => f (quadraticPath a b c r)))
      (b ^ 2 * d₂ + 2 * c * f' a) 0 := by
  have hpath := hasDerivAt_quadraticPath a b c 0
  have hlim : Tendsto (quadraticPath a b c) (𝓝 0) (𝓝 a) := by
    simpa using hpath.continuousAt.tendsto
  have hfirst : deriv (fun r => f (quadraticPath a b c r)) =ᶠ[𝓝 0]
      (fun r => f' (quadraticPath a b c r) * (b + 2 * c * r)) := by
    filter_upwards [hlim.eventually hf] with r hr
    exact (hr.comp r (hasDerivAt_quadraticPath a b c r)).deriv
  have hcomp := hasDerivAt_comp_quadraticPath (b := b) (c := c) hf'
  have hlinear : HasDerivAt (fun r : ℝ => b + 2 * c * r) (2 * c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * c)).const_add b
  have hd := hcomp.fun_mul hlinear
  have heq : (b * d₂) * (b + 2 * c * 0) + f' (quadraticPath a b c 0) * (2 * c) =
      b ^ 2 * d₂ + 2 * c * f' a := by simp; ring
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq hfirst

theorem hasDerivAt_sum_quadraticPath {ι : Type*} [Fintype ι]
    {f : ℝ → ℝ} (a b c d : ι → ℝ) (hf : ∀ i, HasDerivAt f (d i) (a i)) :
    HasDerivAt (fun r => ∑ i, f (quadraticPath (a i) (b i) (c i) r))
      (∑ i, b i * d i) 0 := by
  exact HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hasDerivAt_comp_quadraticPath (hf i))

theorem hasDerivAt_deriv_sum_quadraticPath {ι : Type*} [Fintype ι]
    {f f' : ℝ → ℝ} (a b c d₂ : ι → ℝ)
    (hf : ∀ i, ∀ᶠ u in 𝓝 (a i), HasDerivAt f (f' u) u)
    (hf' : ∀ i, HasDerivAt f' (d₂ i) (a i)) :
    HasDerivAt (deriv (fun r => ∑ i, f (quadraticPath (a i) (b i) (c i) r)))
      (∑ i, ((b i) ^ 2 * d₂ i + 2 * c i * f' (a i))) 0 := by
  classical
  have hlim (i : ι) : Tendsto (quadraticPath (a i) (b i) (c i)) (𝓝 0) (𝓝 (a i)) := by
    simpa using (hasDerivAt_quadraticPath (a i) (b i) (c i) 0).continuousAt.tendsto
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i, HasDerivAt f (f' (quadraticPath (a i) (b i) (c i) r))
      (quadraticPath (a i) (b i) (c i) r) :=
    eventually_all.mpr (fun i => (hlim i).eventually (hf i))
  have heq : deriv (fun r => ∑ i, f (quadraticPath (a i) (b i) (c i) r)) =ᶠ[𝓝 0]
      (fun r => ∑ i, deriv (fun u => f (quadraticPath (a i) (b i) (c i) u)) r) := by
    filter_upwards [hev] with r hr
    exact (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
      ((hr i).comp r (hasDerivAt_quadraticPath (a i) (b i) (c i) r)).differentiableAt.hasDerivAt)).deriv
  exact (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    hasDerivAt_deriv_comp_quadraticPath (b := b i) (c := c i) (hf i) (hf' i))).congr_of_eventuallyEq heq

end
end EntropyConstrainedMissingMass
