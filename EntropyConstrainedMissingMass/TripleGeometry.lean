import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Elementary symmetric coordinates for three atoms: the actual differential, its
Vandermonde determinant, and smooth local inverses at distinct triples. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass.TripleGeometry

abbrev Triple := Fin 3 → ℝ

/-- The elementary symmetric map, with coordinates `(S,E,P)`. -/
def symmetricMap (x : Triple) : Triple :=
  ![x 0 + x 1 + x 2, x 0 * x 1 + x 0 * x 2 + x 1 * x 2, x 0 * x 1 * x 2]

/-- Its Jacobian, with columns corresponding to the three atom masses. -/
def jacobian (x : Triple) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 1; x 1 + x 2, x 0 + x 2, x 0 + x 1; x 1 * x 2, x 0 * x 2, x 0 * x 1]

noncomputable def differential (x : Triple) : Triple →L[ℝ] Triple :=
  (Matrix.toLin' (jacobian x)).toContinuousLinearMap

/-- The Jacobian determinant is the nonzero Vandermonde product at distinct roots. -/
theorem det_jacobian (x : Triple) :
    (jacobian x).det = (x 0 - x 1) * (x 0 - x 2) * (x 1 - x 2) := by
  simp [Matrix.det_fin_three, jacobian]
  ring

theorem det_jacobian_ne_zero (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    (jacobian x).det ≠ 0 := by
  rw [det_jacobian]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h01.ne) (sub_ne_zero.mpr (h01.trans h12).ne))
    (sub_ne_zero.mpr h12.ne)

/-- The symmetric coordinate map is smooth everywhere. -/
theorem contDiff_symmetricMap : ContDiff ℝ ⊤ symmetricMap := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [symmetricMap] <;> fun_prop

/-- The actual Fréchet derivative is the displayed Jacobian. -/
theorem hasFDerivAt_symmetricMap (x : Triple) : HasFDerivAt symmetricMap (differential x) x := by
  let e : Fin 3 → Triple →L[ℝ] ℝ := fun i => ContinuousLinearMap.proj i
  let d : Fin 3 → Triple →L[ℝ] ℝ :=
    ![e 0 + e 1 + e 2,
      (x 0 • e 1 + x 1 • e 0) + (x 0 • e 2 + x 2 • e 0) + (x 1 • e 2 + x 2 • e 1),
      (x 0 * x 1) • e 2 + x 2 • (x 0 • e 1 + x 1 • e 0)]
  have hd : HasFDerivAt symmetricMap (ContinuousLinearMap.pi d) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((hasFDerivAt_apply 0 x).add (hasFDerivAt_apply 1 x)).add (hasFDerivAt_apply 2 x)
    · exact (((hasFDerivAt_apply 0 x).mul (hasFDerivAt_apply 1 x)).add
        ((hasFDerivAt_apply 0 x).mul (hasFDerivAt_apply 2 x))).add
        ((hasFDerivAt_apply 1 x).mul (hasFDerivAt_apply 2 x))
    · exact ((hasFDerivAt_apply 0 x).mul (hasFDerivAt_apply 1 x)).mul (hasFDerivAt_apply 2 x)
  convert hd using 1
  ext v i
  fin_cases i <;>
    simp [differential, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      jacobian, d, e] <;> ring

/-- The derivative becomes a continuous linear equivalence at a strictly increasing triple. -/
noncomputable def differentialEquiv (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    Triple ≃L[ℝ] Triple :=
  ((jacobian x).toLinearEquiv' ((jacobian x).invertibleOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (det_jacobian_ne_zero x h01 h12)))).toContinuousLinearEquiv

@[simp] theorem differentialEquiv_coe (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    (differentialEquiv x h01 h12 : Triple →L[ℝ] Triple) = differential x := by
  ext v i
  rfl

theorem hasFDerivAt_symmetricMap_equiv (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasFDerivAt symmetricMap (differentialEquiv x h01 h12 : Triple →L[ℝ] Triple) x := by
  rw [differentialEquiv_coe]
  exact hasFDerivAt_symmetricMap x

/-- The actual smooth local roots as functions of the three symmetric coordinates. -/
noncomputable def localRoots (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) : Triple → Triple :=
  contDiff_symmetricMap.contDiffAt.localInverse (hasFDerivAt_symmetricMap_equiv x h01 h12) (by simp)

@[simp] theorem localRoots_image (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    localRoots x h01 h12 (symmetricMap x) = x :=
  ContDiffAt.localInverse_apply_image _ _ _

theorem contDiffAt_localRoots (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ContDiffAt ℝ ⊤ (localRoots x h01 h12) (symmetricMap x) :=
  ContDiffAt.to_localInverse _ _ _

theorem eventually_localRoots_left_inverse (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ y in nhds x, localRoots x h01 h12 (symmetricMap y) = y := by
  exact (contDiff_symmetricMap.contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_symmetricMap_equiv x h01 h12) (by simp)).eventually_left_inverse

theorem eventually_localRoots_right_inverse (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ c in nhds (symmetricMap x), symmetricMap (localRoots x h01 h12 c) = c := by
  exact (contDiff_symmetricMap.contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_symmetricMap_equiv x h01 h12) (by simp)).eventually_right_inverse

/-- Small symmetric-coordinate changes preserve strict ordering and positive atom masses. -/
theorem eventually_localRoots_positive_ordered (x : Triple) (h0 : 0 < x 0)
    (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    ∀ᶠ c in nhds (symmetricMap x),
      0 < localRoots x h01 h12 c 0 ∧ localRoots x h01 h12 c 0 < localRoots x h01 h12 c 1 ∧
        localRoots x h01 h12 c 1 < localRoots x h01 h12 c 2 := by
  have hopen : IsOpen {y : Triple | 0 < y 0 ∧ y 0 < y 1 ∧ y 1 < y 2} :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) (continuous_apply 2)))
  have ht : Filter.Tendsto (localRoots x h01 h12) (nhds (symmetricMap x)) (nhds x) := by
    simpa only [localRoots_image] using (contDiffAt_localRoots x h01 h12).continuousAt.tendsto
  exact ht.eventually (hopen.mem_nhds ⟨h0, h01, h12⟩)

/-- The local inverse has the inverse of the displayed differential as its actual derivative. -/
theorem hasFDerivAt_localRoots (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) :
    HasFDerivAt (localRoots x h01 h12)
      ((differentialEquiv x h01 h12).symm : Triple →L[ℝ] Triple) (symmetricMap x) := by
  exact (contDiff_symmetricMap.contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_symmetricMap_equiv x h01 h12) (by simp)).to_localInverse.hasFDerivAt

/-- The derivative of the root polynomial evaluated at each of its three roots. -/
def rootDenom (x : Triple) : Triple :=
  ![(x 0 - x 1) * (x 0 - x 2), (x 1 - x 0) * (x 1 - x 2), (x 2 - x 0) * (x 2 - x 1)]

theorem rootDenom_ne_zero (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (i : Fin 3) :
    rootDenom x i ≠ 0 := by
  fin_cases i <;> dsimp [rootDenom]
  · exact mul_ne_zero (sub_ne_zero.mpr h01.ne) (sub_ne_zero.mpr (h01.trans h12).ne)
  · exact mul_ne_zero (sub_ne_zero.mpr h01.ne.symm) (sub_ne_zero.mpr h12.ne)
  · exact mul_ne_zero (sub_ne_zero.mpr (h01.trans h12).ne.symm) (sub_ne_zero.mpr h12.ne.symm)

def rootPolynomial (c : Triple) (u : ℝ) : ℝ := u ^ 3 - c 0 * u ^ 2 + c 1 * u - c 2

theorem rootPolynomial_apply_root (x : Triple) (i : Fin 3) :
    rootPolynomial (symmetricMap x) (x i) = 0 := by
  fin_cases i <;> dsimp [rootPolynomial, symmetricMap] <;> ring

theorem rootDenom_eq (x : Triple) (i : Fin 3) :
    rootDenom x i = 3 * (x i) ^ 2 - 2 * symmetricMap x 0 * x i + symmetricMap x 1 := by
  fin_cases i <;> dsimp [rootDenom, symmetricMap] <;> ring

/-- The cubic really has derivative `W′(u)` at each root. -/
theorem hasDerivAt_rootPolynomial (x : Triple) (i : Fin 3) :
    HasDerivAt (rootPolynomial (symmetricMap x)) (rootDenom x i) (x i) := by
  convert ((((hasDerivAt_id (x i)).pow 3).sub
    (((hasDerivAt_id (x i)).pow 2).const_mul (symmetricMap x 0))).add
    ((hasDerivAt_id (x i)).const_mul (symmetricMap x 1))).sub_const (symmetricMap x 2) using 1
  · rfl
  · rw [rootDenom_eq]
    norm_num
    ring

/-- Algebraic inverse differential, before division by `W′`. -/
theorem rootDenom_mul_eq_differential (x v : Triple) (i : Fin 3) :
    rootDenom x i * v i = (x i) ^ 2 * differential x v 0 - x i * differential x v 1 + differential x v 2 := by
  fin_cases i <;>
    simp [rootDenom, differential, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, jacobian] <;> ring

/-- The inverse differential's rows are `(u², -u, 1)/W′(u)`. -/
theorem inverse_differential_apply (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (w : Triple) (i : Fin 3) :
    (differentialEquiv x h01 h12).symm w i =
      ((x i) ^ 2 * w 0 - x i * w 1 + w 2) / rootDenom x i := by
  apply (eq_div_iff (rootDenom_ne_zero x h01 h12 i)).mpr
  have h := rootDenom_mul_eq_differential x ((differentialEquiv x h01 h12).symm w) i
  have hd : differential x ((differentialEquiv x h01 h12).symm w) = w := by
    rw [← differentialEquiv_coe x h01 h12]
    exact (differentialEquiv x h01 h12).apply_symm_apply w
  rw [hd] at h
  simpa only [mul_comm] using h

/-- The `E`-column of the inverse differential is `-u/W′(u)`. -/
theorem inverse_differential_E (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (i : Fin 3) :
    (differentialEquiv x h01 h12).symm ![0, 1, 0] i = -(x i) / rootDenom x i := by
  rw [inverse_differential_apply]
  simp

/-- The `P`-column of the inverse differential is `1/W′(u)`. -/
theorem inverse_differential_P (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (i : Fin 3) :
    (differentialEquiv x h01 h12).symm ![0, 0, 1] i = 1 / rootDenom x i := by
  rw [inverse_differential_apply]
  simp

/-- Every root has the predicted actual directional derivative in symmetric coordinates. -/
theorem hasDerivAt_localRoots_direction (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (w : Triple) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => localRoots x h01 h12 (symmetricMap x + r • w) i)
      (((x i) ^ 2 * w 0 - x i * w 1 + w 2) / rootDenom x i) 0 := by
  have hpath : HasDerivAt (fun r : ℝ => symmetricMap x + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (symmetricMap x)
  have hc := (hasFDerivAt_apply i (localRoots x h01 h12 (symmetricMap x))).comp (symmetricMap x)
    (hasFDerivAt_localRoots x h01 h12)
  have hc' : HasFDerivAt (fun c => localRoots x h01 h12 c i)
      ((ContinuousLinearMap.proj i).comp (differentialEquiv x h01 h12).symm.toContinuousLinearMap)
      ((fun r : ℝ => symmetricMap x + r • w) 0) := by simpa [Function.comp_def] using hc
  simpa [Function.comp_def, inverse_differential_apply] using hc'.comp_hasDerivAt 0 hpath

/-- The manuscript's root derivative `u_E=-u/W′(u)` as a scalar derivative. -/
theorem hasDerivAt_localRoots_E (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => localRoots x h01 h12 (symmetricMap x + r • ![0, 1, 0]) i)
      (-(x i) / rootDenom x i) 0 := by
  simpa using hasDerivAt_localRoots_direction x h01 h12 ![0, 1, 0] i

/-- The manuscript's root derivative `u_P=1/W′(u)` as a scalar derivative. -/
theorem hasDerivAt_localRoots_P (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => localRoots x h01 h12 (symmetricMap x + r • ![0, 0, 1]) i)
      (1 / rootDenom x i) 0 := by
  simpa using hasDerivAt_localRoots_direction x h01 h12 ![0, 0, 1] i

/-- The first partial-fraction identity used for the entropy derivative in `P`. -/
theorem partial_fractions_one (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (s : ℝ) (hs : ∀ i, s + x i ≠ 0) :
    (∑ i : Fin 3, 1 / ((s + x i) * rootDenom x i)) =
      1 / ((s + x 0) * (s + x 1) * (s + x 2)) := by
  have h02 := h01.trans h12
  simp [Fin.sum_univ_succ, rootDenom]
  field_simp [hs 0, hs 1, hs 2, sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne,
    sub_ne_zero.mpr h12.ne, sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm,
    sub_ne_zero.mpr h12.ne.symm]
  ring

/-- The second partial-fraction identity used for the entropy derivative in `E`. -/
theorem partial_fractions_root (x : Triple) (h01 : x 0 < x 1) (h12 : x 1 < x 2)
    (s : ℝ) (hs : ∀ i, s + x i ≠ 0) :
    (∑ i : Fin 3, x i / ((s + x i) * rootDenom x i)) =
      -s / ((s + x 0) * (s + x 1) * (s + x 2)) := by
  have h02 := h01.trans h12
  simp [Fin.sum_univ_succ, rootDenom]
  field_simp [hs 0, hs 1, hs 2, sub_ne_zero.mpr h01.ne, sub_ne_zero.mpr h02.ne,
    sub_ne_zero.mpr h12.ne, sub_ne_zero.mpr h01.ne.symm, sub_ne_zero.mpr h02.ne.symm,
    sub_ne_zero.mpr h12.ne.symm]
  ring

end EntropyConstrainedMissingMass.TripleGeometry
