import EntropyConstrainedMissingMass.Probability
import EntropyConstrainedMissingMass.ObjectiveCalculus
import EntropyConstrainedMissingMass.Support

/-! Splitting into an unused coordinate: genuine ℓ¹ perturbations of probability vectors. -/

namespace EntropyConstrainedMissingMass

noncomputable section
open Set Filter
open scoped Topology ENNReal

/-- The real entropy gained by replacing mass `a` by `a-ε` and `ε`. -/
def splitEntropyIncrement (a ε : ℝ) : ℝ :=
  Real.negMulLog (a - ε) + Real.negMulLog ε - Real.negMulLog a

theorem continuous_splitEntropyIncrement (a : ℝ) : Continuous (splitEntropyIncrement a) := by
  unfold splitEntropyIncrement
  fun_prop

@[simp] theorem splitEntropyIncrement_zero (a : ℝ) : splitEntropyIncrement a 0 = 0 := by
  simp [splitEntropyIncrement]

theorem tendsto_splitEntropyIncrement_zero (a : ℝ) :
    Tendsto (splitEntropyIncrement a) (𝓝 0) (𝓝 0) := by
  simpa only [splitEntropyIncrement_zero] using (continuous_splitEntropyIncrement a).tendsto 0

theorem splitEntropyIncrement_pos {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    0 < splitEntropyIncrement a ε := by
  have hleft : 0 < a - ε := sub_pos.mpr hεa
  have hl1 : 0 < Real.log a - Real.log (a - ε) :=
    sub_pos.mpr (Real.log_lt_log hleft (by linarith))
  have hl2 : 0 < Real.log a - Real.log ε :=
    sub_pos.mpr (Real.log_lt_log hε hεa)
  have heq : splitEntropyIncrement a ε =
      (a - ε) * (Real.log a - Real.log (a - ε)) + ε * (Real.log a - Real.log ε) := by
    simp only [splitEntropyIncrement, Real.negMulLog]
    ring
  rw [heq]
  exact add_pos (mul_pos hleft hl1) (mul_pos hε hl2)

namespace ProbabilityVector
variable {ι : Type*}

/-- Subtract from coordinate `i` and put the removed mass at coordinate `j`. -/
def splitCoord (p : ProbabilityVector ι) (i j : ι) (ε : ℝ) : ι → ℝ := by
  classical
  exact Function.update (Function.update p.coord i (p.coord i - ε)) j ε

theorem splitCoord_i (p : ProbabilityVector ι) {i j : ι} (hij : i ≠ j) (ε : ℝ) :
    splitCoord p i j ε i = p.coord i - ε := by
  classical
  simp [splitCoord, hij]

@[simp] theorem splitCoord_j (p : ProbabilityVector ι) (i j : ι) (ε : ℝ) :
    splitCoord p i j ε j = ε := by
  classical
  simp [splitCoord]

theorem splitCoord_other (p : ProbabilityVector ι) {i j k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) (ε : ℝ) : splitCoord p i j ε k = p.coord k := by
  classical
  simp [splitCoord, hki, hkj]

theorem hasSum_splitCoord (p : ProbabilityVector ι) {i j : ι}
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) : HasSum (splitCoord p i j ε) 1 := by
  classical
  have hs := (p.hasSum_coord.update i (p.coord i - ε)).update j ε
  convert hs using 1
  · rfl
  · simp [Function.update_of_ne hij.symm, hj]

def splitAtom (p : ProbabilityVector ι) (i j : ι) (hij : i ≠ j) (hj : p.coord j = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i) : ProbabilityVector ι :=
  ofHasSum (splitCoord p i j ε)
    (by
      intro k
      by_cases hkj : k = j
      · subst k; simpa using hε
      by_cases hki : k = i
      · subst k; rw [splitCoord_i p hij]; exact sub_nonneg.mpr hεa
      rw [splitCoord_other p hki hkj]
      exact p.coord_nonneg k)
    (hasSum_splitCoord p hij hj ε)

@[simp] theorem coord_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i) :
    (splitAtom p i j hij hj ε hε hεa).coord = splitCoord p i j ε := rfl

theorem hasSum_split_statistic (p : ProbabilityVector ι) {i j : ι}
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (f : ℝ → ℝ) (hf : f 0 = 0)
    (hs : Summable (fun k => f (p.coord k))) :
    HasSum (fun k => f (splitCoord p i j ε k))
      ((∑' k, f (p.coord k)) + f (p.coord i - ε) + f ε - f (p.coord i)) := by
  classical
  change HasSum (f ∘ splitCoord p i j ε) _
  unfold splitCoord
  rw [Function.comp_update, Function.comp_update]
  have h := (hs.hasSum.update i (f (p.coord i - ε))).update j (f ε)
  convert h using 1
  · rfl
  · simp only [Function.update_of_ne hij.symm, hj, hf]
    ring

theorem dist_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i) :
    dist (splitAtom p i j hij hj ε hε hεa) p = 2 * ε := by
  classical
  rw [dist_eq_tsum, coord_splitAtom]
  rw [tsum_eq_sum (s := {i, j}) (by
    intro k hk
    have hki : k ≠ i := by simpa using fun he => hk (by simp [he])
    have hkj : k ≠ j := by simpa using fun he => hk (by simp [he])
    rw [splitCoord_other p hki hkj]
    simp)]
  simp [Finset.sum_pair hij, splitCoord_i p hij, hj, abs_of_nonneg hε]
  ring

theorem entropy_splitAtom_ne_top (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i)
    (hp : p.entropy ≠ ⊤) : (splitAtom p i j hij hj ε hε hεa).entropy ≠ ⊤ := by
  apply (entropy_ne_top_iff _).2
  exact (hasSum_split_statistic p hij hj ε Real.negMulLog (by simp)
    (p.entropy_ne_top_iff.mp hp)).summable

theorem entropy_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i)
    (hp : p.entropy ≠ ⊤) :
    (splitAtom p i j hij hj ε hε hεa).entropy =
      ENNReal.ofReal (p.entropy.toReal + splitEntropyIncrement (p.coord i) ε) := by
  rw [entropy_eq_ofReal_tsum _ (entropy_splitAtom_ne_top p i j hij hj ε hε hεa hp)]
  congr 1
  rw [coord_splitAtom,
    (hasSum_split_statistic p hij hj ε Real.negMulLog (by simp)
      (p.entropy_ne_top_iff.mp hp)).tsum_eq,
    p.entropy_toReal hp]
  unfold splitEntropyIncrement
  ring

theorem entropy_toReal_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 < ε) (hεa : ε < p.coord i)
    (hp : p.entropy ≠ ⊤) :
    (splitAtom p i j hij hj ε hε.le hεa.le).entropy.toReal =
      p.entropy.toReal + splitEntropyIncrement (p.coord i) ε := by
  rw [entropy_splitAtom p i j hij hj ε hε.le hεa.le hp,
    ENNReal.toReal_ofReal (add_nonneg ENNReal.toReal_nonneg
      (splitEntropyIncrement_pos hε hεa).le)]

theorem entropy_lt_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 < ε) (hεa : ε < p.coord i)
    (hp : p.entropy ≠ ⊤) :
    p.entropy < (splitAtom p i j hij hj ε hε.le hεa.le).entropy := by
  apply (ENNReal.toReal_lt_toReal hp
    (entropy_splitAtom_ne_top p i j hij hj ε hε.le hεa.le hp)).mp
  rw [entropy_toReal_splitAtom p i j hij hj ε hε hεa hp]
  exact lt_add_of_pos_right _ (splitEntropyIncrement_pos hε hεa)

theorem objective_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 ≤ ε) (hεa : ε ≤ p.coord i)
    (t : ℕ) :
    (splitAtom p i j hij hj ε hε hεa).objective t = p.objective t +
      missingMassTerm t (p.coord i - ε) + missingMassTerm t ε - missingMassTerm t (p.coord i) := by
  exact (hasSum_split_statistic p hij hj ε (missingMassTerm t)
    (by simp [missingMassTerm]) (p.objective_summable t)).tsum_eq

theorem objective_lt_splitAtom (p : ProbabilityVector ι) (i j : ι)
    (hij : i ≠ j) (hj : p.coord j = 0) (ε : ℝ) (hε : 0 < ε) (hεa : ε < p.coord i)
    (t : ℕ) (ht : 1 ≤ t) :
    p.objective t < (splitAtom p i j hij hj ε hε.le hεa.le).objective t := by
  rw [objective_splitAtom]
  have hs := missingMassTerm_split_strict t ht (p.coord i) ε hε hεa (p.coord_le_one i)
  linarith

/-- An unused coordinate forces entropy saturation at a local maximum.
The hypothesis that an unused coordinate exists is explicit. -/
theorem entropy_saturation_of_zero_coord (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) {j : ι} (hj : p.coord j = 0) :
    p.entropy = ENNReal.ofReal h := by
  by_contra hne
  have hlt : p.entropy < ENNReal.ofReal h := lt_of_le_of_ne hp.1 hne
  have hfin : p.entropy ≠ ⊤ := finite_entropy_of_feasible hp.1
  have hh : 0 < h := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hlt)
  have hreal : p.entropy.toReal < h := by
    have hr := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hlt
    simpa only [ENNReal.toReal_ofReal hh.le] using hr
  obtain ⟨i, hi⟩ := p.exists_coord_pos
  have hij : i ≠ j := by intro he; subst i; simp [hj] at hi
  have hlocal : {q : ProbabilityVector ι | q.objective t ≤ p.objective t} ∈
      𝓝[Feasible h] p := hp.2
  obtain ⟨u, hu, hule⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hlocal
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hsmall : {ε : ℝ | splitEntropyIncrement (p.coord i) ε < h - p.entropy.toReal}
      ∈ 𝓝 0 :=
    (tendsto_splitEntropyIncrement_zero (p.coord i)).eventually
      (Iio_mem_nhds (sub_pos.mpr hreal))
  obtain ⟨d, hd, hdball⟩ := Metric.mem_nhds_iff.mp hsmall
  let ε := min (p.coord i) (min r d) / 4
  have hmin : 0 < min (p.coord i) (min r d) := lt_min hi (lt_min hr hd)
  have hε : 0 < ε := div_pos hmin (by norm_num)
  have hεi : ε < p.coord i := by
    have := min_le_left (p.coord i) (min r d)
    dsimp [ε]; linarith
  have hεr : 2 * ε < r := by
    have := (min_le_right (p.coord i) (min r d)).trans (min_le_left r d)
    dsimp [ε]; linarith
  have hεd : ε < d := by
    have := (min_le_right (p.coord i) (min r d)).trans (min_le_right r d)
    dsimp [ε]; linarith
  have hinc : splitEntropyIncrement (p.coord i) ε < h - p.entropy.toReal :=
    hdball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using hεd)
  let q := splitAtom p i j hij hj ε hε.le hεi.le
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_splitAtom]
    exact hεr
  have hqfeas : q ∈ Feasible h := by
    change q.entropy ≤ ENNReal.ofReal h
    rw [entropy_splitAtom p i j hij hj ε hε.le hεi.le hfin]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hqle : q.objective t ≤ p.objective t := hule ⟨hball hqball, hqfeas⟩
  exact (not_lt_of_ge hqle) (objective_lt_splitAtom p i j hij hj ε hε hεi t ht)

/-- Conditional entropy saturation on an infinite alphabet.
This theorem assumes finite support and does not establish the structural finite-support theorem. -/
theorem entropy_saturation_of_finite_support [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hp : LocalMaximizer t h p)
    (hs : (Function.support p.coord).Finite) : p.entropy = ENNReal.ofReal h := by
  obtain ⟨j, hj⟩ := hs.exists_notMem
  apply entropy_saturation_of_zero_coord p ht hp (j := j)
  exact not_ne_iff.mp hj

theorem entropy_toReal_saturation_of_finite_support [Infinite ι] (p : ProbabilityVector ι)
    {t : ℕ} {h : ℝ} (ht : 1 ≤ t) (hh : 0 ≤ h) (hp : LocalMaximizer t h p)
    (hs : (Function.support p.coord).Finite) : p.entropy.toReal = h := by
  rw [entropy_saturation_of_finite_support p ht hp hs, ENNReal.toReal_ofReal hh]

end ProbabilityVector
end
end EntropyConstrainedMissingMass
