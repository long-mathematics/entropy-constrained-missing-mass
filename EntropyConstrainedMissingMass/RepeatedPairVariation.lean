import EntropyConstrainedMissingMass.RepeatedFourVariation

/-! The entropy-compensated repeated-pair variation with one other atom. -/
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open Filter Set
open scoped Topology

def repeatedPairBase (q z : ℝ) : Fin 3 → ℝ := ![q, q, z]
def repeatedPairPath (q z c ε : ℝ) (i : Fin 3) : ℝ :=
  quadraticPath (repeatedPairBase q z i) (![1, -1, 0] i) (![c, c, -2 * c] i) ε

@[simp] theorem repeatedPairPath_zero (q z c : ℝ) : repeatedPairPath q z c 0 = repeatedPairBase q z := by
  ext i
  simp [repeatedPairPath]

theorem repeatedPairPath_sum (q z c ε : ℝ) :
    ∑ i, repeatedPairPath q z c ε i = ∑ i, repeatedPairBase q z i := by
  simp [repeatedPairPath, repeatedPairBase, quadraticPath, Fin.sum_univ_succ]
  ring

theorem continuous_repeatedPairPath (q z c : ℝ) : Continuous (repeatedPairPath q z c) := by
  apply continuous_pi
  intro i
  unfold repeatedPairPath quadraticPath
  fun_prop

theorem repeatedPairPath_eventually_nonneg {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (c : ℝ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i, 0 ≤ repeatedPairPath q z c ε i := by
  apply eventually_all.mpr
  intro i
  have hpos : 0 < repeatedPairPath q z c 0 i := by
    rw [repeatedPairPath_zero]
    fin_cases i <;> simp [repeatedPairBase] <;> assumption
  exact (((continuous_apply i).comp (continuous_repeatedPairPath q z c)).continuousAt.eventually
    (Ioi_mem_nhds hpos)).mono (fun _ h => h.le)

theorem hasDerivAt_repeatedPair_sum {f : ℝ → ℝ} (q z c : ℝ)
    (hf : ∀ i, HasDerivAt f (deriv f (repeatedPairBase q z i)) (repeatedPairBase q z i)) :
    HasDerivAt (fun ε => ∑ i, f (repeatedPairPath q z c ε i)) 0 0 := by
  have hd := hasDerivAt_sum_quadraticPath (repeatedPairBase q z)
    (![1, -1, 0]) (![c, c, -2 * c]) (fun i => deriv f (repeatedPairBase q z i)) hf
  convert hd using 1
  · rfl
  · simp [repeatedPairBase, Fin.sum_univ_succ]

theorem hasDerivAt_deriv_repeatedPair_sum {f : ℝ → ℝ} (q z c : ℝ)
    (hf : ∀ i, ∀ᶠ u in 𝓝 (repeatedPairBase q z i), HasDerivAt f (deriv f u) u)
    (hdf : ∀ i, HasDerivAt (deriv f) (deriv (deriv f) (repeatedPairBase q z i))
      (repeatedPairBase q z i)) :
    HasDerivAt (deriv (fun ε => ∑ i, f (repeatedPairPath q z c ε i)))
      (2 * deriv (deriv f) q + 4 * c * (deriv f q - deriv f z)) 0 := by
  have hd := hasDerivAt_deriv_sum_quadraticPath (repeatedPairBase q z)
    (![1, -1, 0]) (![c, c, -2 * c]) (fun i => deriv (deriv f) (repeatedPairBase q z i)) hf hdf
  convert hd using 1
  · rfl
  · simp [repeatedPairBase, Fin.sum_univ_succ]
    ring

theorem repeatedPairBase_pos {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (i : Fin 3) :
    0 < repeatedPairBase q z i := by fin_cases i <;> simp [repeatedPairBase] <;> assumption

theorem repeatedPair_entropy_second_deriv {q z : ℝ} (hq : 0 < q) (hz : 0 < z) (c : ℝ) :
    HasDerivAt (deriv (fun ε => ∑ i, Real.negMulLog (repeatedPairPath q z c ε i)))
      (-2 / q + 4 * c * (Real.log z - Real.log q)) 0 := by
  have hd := hasDerivAt_deriv_repeatedPair_sum q z c
    (fun i => eventually_hasDerivAt_negMulLog_at_pos (repeatedPairBase_pos hq hz i))
    (fun i => (hasDerivAt_deriv_negMulLog_at_pos (repeatedPairBase_pos hq hz i)).differentiableAt.hasDerivAt)
  convert hd using 1
  rw [(hasDerivAt_deriv_negMulLog_at_pos hq).deriv,
    Real.deriv_negMulLog (ne_of_gt hq), Real.deriv_negMulLog (ne_of_gt hz)]
  ring

theorem repeatedPair_entropy_localMax {q z : ℝ} (hq : 0 < q) (hqz : q < z)
    (c : ℝ) (hc : c < 1 / (2 * q * (Real.log z - Real.log q))) :
    IsLocalMax (fun ε => ∑ i, Real.negMulLog (repeatedPairPath q z c ε i)) 0 := by
  have hz := hq.trans hqz
  have hL : 0 < Real.log z - Real.log q := sub_pos.mpr (Real.log_lt_log hq hqz)
  have hmul := (lt_div_iff₀ (mul_pos (mul_pos (by norm_num) hq) hL)).mp hc
  have hd := repeatedPair_entropy_second_deriv hq hz c
  have hfirst := hasDerivAt_repeatedPair_sum q z c (fun i =>
    (Real.differentiableAt_negMulLog (ne_of_gt (repeatedPairBase_pos hq hz i))).hasDerivAt)
  apply isLocalMax_of_deriv_deriv_neg _ hfirst.deriv hfirst.continuousAt
  rw [hd.deriv]
  have heq : -2 / q + 4 * c * (Real.log z - Real.log q) =
      (-2 + 4 * c * (Real.log z - Real.log q) * q) / q := by field_simp
  rw [heq]
  exact div_neg_of_neg_of_pos (by nlinarith) hq

namespace ProbabilityVector

/-- The second-order multiplier bound for a repeated pair and any larger atom,
derived using strictly entropy-decreasing quadratic paths. -/
theorem repeated_pair_weighted_bound {ι : Type*} (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (e : Fin 3 ↪ ι) {q z : ℝ}
    (hq : 0 < q) (hqz : q < z) (hbase : (fun i => p.coord (e i)) = repeatedPairBase q z) :
    q * deriv (deriv (missingMassTerm t)) q ≤
      (deriv (missingMassTerm t) z - deriv (missingMassTerm t) q) / (Real.log z - Real.log q) := by
  have hz := hq.trans hqz
  have hL : 0 < Real.log z - Real.log q := sub_pos.mpr (Real.log_lt_log hq hqz)
  have hfd : Differentiable ℝ (missingMassTerm t) := by unfold missingMassTerm; fun_prop
  have hdfd : Differentiable ℝ (deriv (missingMassTerm t)) := by
    have heq := funext (deriv_missingMassTerm t ht)
    rw [heq]
    fun_prop
  have hcoord (i : Fin 3) : p.coord (e i) = repeatedPairBase q z i := congr_fun hbase i
  have hnear (c : ℝ) (hc : c < 1 / (2 * q * (Real.log z - Real.log q))) :
      2 * deriv (deriv (missingMassTerm t)) q +
        4 * c * (deriv (missingMassTerm t) q - deriv (missingMassTerm t) z) ≤ 0 := by
    have hfirst := hasDerivAt_repeatedPair_sum q z c (fun i => (hfd _).hasDerivAt)
    have hsecond := hasDerivAt_deriv_repeatedPair_sum q z c
      (fun _ => Eventually.of_forall (fun u => (hfd u).hasDerivAt)) (fun i => (hdfd _).hasDerivAt)
    have hmax : IsLocalMax (fun ε => ∑ i, missingMassTerm t (repeatedPairPath q z c ε i)) 0 := by
      apply localMax_of_embedded_path p hp e (repeatedPairPath q z c) 0
      · intro i
        rw [repeatedPairPath_zero, hcoord]
      · intro i
        simpa only [hcoord, Function.comp_def, repeatedPairPath_zero] using ((continuous_apply i).comp (continuous_repeatedPairPath q z c)).tendsto 0
      · filter_upwards [repeatedPairPath_eventually_nonneg hq hz c] with ε he
        exact ⟨he, by simp only [hcoord, repeatedPairPath_sum]⟩
      · have he := repeatedPair_entropy_localMax hq hqz c hc
        change ∀ᶠ ε in 𝓝 (0 : ℝ), (∑ i, Real.negMulLog (repeatedPairPath q z c ε i)) ≤
          ∑ i, Real.negMulLog (repeatedPairPath q z c 0 i) at he
        simpa only [hcoord, repeatedPairPath_zero] using he
    have hle := second_derivative_nonpos_of_localMax hfirst.continuousAt hmax
    rwa [hsecond.deriv] at hle
  have hcrit := nonpos_at_of_forall_lt (by fun_prop) hnear
  apply weighted_bound_of_affine_nonpos hq hL
  convert hcrit using 1
  ring

end ProbabilityVector
end
end EntropyConstrainedMissingMass
