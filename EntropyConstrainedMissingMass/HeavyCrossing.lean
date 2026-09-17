import EntropyConstrainedMissingMass.CrossingCalculus
import EntropyConstrainedMissingMass.HeavyInterpolation
import EntropyConstrainedMissingMass.CandidateVectors
import EntropyConstrainedMissingMass.EntropySeries

/-! Single crossing between distinct heavy candidates of equal entropy. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set Filter
open scoped Topology

theorem strictMonoOn_heavyRoot {h : ℝ} (hh : 0 < h) :
    StrictMonoOn (heavyRoot h) (Ioi (Real.exp h - 1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
    (fun m hm => (hasDerivAt_heavyRoot hh hm).continuousAt.continuousWithinAt)
  intro m hm
  rw [interior_Ioi] at hm
  rw [(hasDerivAt_heavyRoot hh hm).deriv]
  obtain ⟨_, hq, _, _, hs⟩ := heavy_parameters_pos hh hm
  exact div_pos hq hs

theorem strictAntiOn_heavyLight {h : ℝ} (hh : 0 < h) :
    StrictAntiOn (heavyLight h) (Ioi (Real.exp h - 1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
    (fun m hm => (hasDerivAt_heavyLight hh hm).continuousAt.continuousWithinAt)
  intro m hm
  rw [interior_Ioi] at hm
  rw [(hasDerivAt_heavyLight hh hm).deriv]
  obtain ⟨hm0, hq, _, _, hs⟩ := heavy_parameters_pos hh hm
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hq (by linarith))) (mul_pos hm0 hs)

theorem heavyValue_eq {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) (s : ℝ) :
    heavyValue h s m = heavyRoot h m * (1 - heavyRoot h m) ^ s +
      (1 - heavyRoot h m) * (1 - heavyLight h m) ^ s := by
  have hm0 := (heavy_parameters_pos hh hm).1
  unfold heavyValue realMissingMassTerm
  congr 1
  rw [← mul_assoc, heavyLight, mul_div_cancel₀ _ hm0.ne']

theorem analyticAt_heavyValue {h m : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m) (x : ℝ) :
    AnalyticAt ℝ (fun s => heavyValue h s m) x := by
  obtain ⟨_, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh hm
  simp_rw [heavyValue_eq hh hm, Real.rpow_def_of_pos (sub_pos.mpr hz1),
    Real.rpow_def_of_pos (sub_pos.mpr (hqz.trans hz1))]
  fun_prop

theorem heavy_difference_four_term {h i j : ℝ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hj : Real.exp h - 1 < j) (s : ℝ) :
    heavyValue h s j - heavyValue h s i =
      heavyRoot h j * (1 - heavyRoot h j) ^ s - heavyRoot h i * (1 - heavyRoot h i) ^ s -
      (1 - heavyRoot h i) * (1 - heavyLight h i) ^ s +
      (1 - heavyRoot h j) * (1 - heavyLight h j) ^ s := by
  rw [heavyValue_eq hh hi, heavyValue_eq hh hj]
  ring

theorem heavy_difference_zero_bound {h i j : ℝ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) :
    ZeroMultiplicityBound (fun s => heavyValue h s j - heavyValue h s i) 2 := by
  have hj := hi.trans hij
  obtain ⟨_, hqi, hqzi, hzi1, _⟩ := heavy_parameters_pos hh hi
  obtain ⟨_, hqj, hqzj, hzj1, _⟩ := heavy_parameters_pos hh hj
  have hzij := strictMonoOn_heavyRoot hh hi hj hij
  have hqji := strictAntiOn_heavyLight hh hi hj hij
  simpa only [heavy_difference_four_term hh hi hj] using four_term_zeros
    (heavyRoot h j) (heavyRoot h i) (1 - heavyRoot h i) (1 - heavyRoot h j)
    (1 - heavyRoot h j) (1 - heavyRoot h i) (1 - heavyLight h i) (1 - heavyLight h j)
    (hqj.trans hqzj) (hqi.trans hqzi) (sub_pos.mpr hzi1) (sub_pos.mpr hzj1)
    (sub_pos.mpr hzj1) (by linarith) (by linarith) (by linarith)

theorem heavy_difference_eventually_pos {h i j : ℝ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) :
    ∀ᶠ s : ℝ in atTop, 0 < heavyValue h s j - heavyValue h s i := by
  have hj := hi.trans hij
  obtain ⟨_, hqi, hqzi, hzi1, _⟩ := heavy_parameters_pos hh hi
  obtain ⟨_, hqj, hqzj, hzj1, _⟩ := heavy_parameters_pos hh hj
  have hqji := strictAntiOn_heavyLight hh hi hj hij
  simpa only [heavy_difference_four_term hh hi hj] using eventually_pos_four_term
    (heavyRoot h j) (heavyRoot h i) (1 - heavyRoot h i) (1 - heavyRoot h j)
    (1 - heavyRoot h j) (1 - heavyRoot h i) (1 - heavyLight h i) (1 - heavyLight h j)
    (sub_pos.mpr hzj1) (sub_pos.mpr hzj1) (sub_pos.mpr hzi1)
    (sub_pos.mpr (hqzi.trans hzi1)) (by linarith) (by linarith) (by linarith)

theorem heavyValue_integer_eq {h m : ℝ} (hh : 0 < h)
    (hm : Real.exp h - 1 < m) (t : ℕ) :
    heavyValue h t m = branchObjective m t (heavyRoot h m) := by
  rw [heavyValue_eq hh hm]
  simp only [Real.rpow_natCast, branchObjective, heavyLight]

theorem heavy_difference_entropy_series {h : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hj : Real.exp h - 1 < j) :
    HasSum (fun n : ℕ => (heavyValue h (n + 1) j - heavyValue h (n + 1) i) / (n + 1)) 0 := by
  have hip := heavy_parameters_pos hh hi
  have hjp := heavy_parameters_pos hh hj
  have hi0 : 0 < i := by exact_mod_cast hip.1
  have hj0 : 0 < j := by exact_mod_cast hjp.1
  have hzi : heavyRoot h i ∈ Icc 0 1 := ⟨(hip.2.1.trans hip.2.2.1).le, hip.2.2.2.1.le⟩
  have hzj : heavyRoot h j ∈ Icc 0 1 := ⟨(hjp.2.1.trans hjp.2.2.1).le, hjp.2.2.2.1.le⟩
  let p := candidateVector j (heavyRoot h j) hj0 hzj
  let q := candidateVector i (heavyRoot h i) hi0 hzi
  have hp : p.entropy = ENNReal.ofReal h := by
    rw [entropy_candidateVector, (heavyRoot_spec hh hj).2]
  have hq : q.entropy = ENNReal.ofReal h := by
    rw [entropy_candidateVector, (heavyRoot_spec hh hi).2]
  have hs := p.hasSum_objective_sub_div_zero q (hp ▸ ENNReal.ofReal_ne_top) (hp.trans hq.symm)
  convert hs using 1
  funext n
  dsimp [p, q]
  rw [objective_candidateVector, objective_candidateVector]
  simp only [Nat.cast_add, Nat.cast_one, ← heavyValue_integer_eq hh hj,
    ← heavyValue_integer_eq hh hi]

/-- Every pair of integer heavy candidates has exactly one positive simple crossing,
strictly after sample size one. Both signs and simplicity at zero are included. -/
theorem heavy_heavy_single_crossing {h : ℝ} {i j : ℕ} (hh : 0 < h)
    (hi : Real.exp h - 1 < i) (hij : i < j) :
    ∃ τ : ℝ, 1 < τ ∧
      (∀ s : ℝ, heavyValue h s j = heavyValue h s i ↔ s = 0 ∨ s = τ) ∧
      analyticOrderAt (fun s => heavyValue h s j - heavyValue h s i) 0 = 1 ∧
      analyticOrderAt (fun s => heavyValue h s j - heavyValue h s i) τ = 1 ∧
      (∀ s ∈ Ioo 0 τ, heavyValue h s j < heavyValue h s i) ∧
      (∀ s ∈ Ioi τ, heavyValue h s i < heavyValue h s j) := by
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hj := hi.trans hij'
  have hpos := heavy_difference_eventually_pos hh hi hij'
  obtain ⟨n, hn⟩ := exists_negative_integer_of_zero_series
    (f := fun s => heavyValue h s j - heavyValue h s i)
    (heavy_difference_entropy_series hh hi hj) hpos
  have h0 : heavyValue h 0 j - heavyValue h 0 i = 0 := by
    rw [heavyValue_eq hh hi, heavyValue_eq hh hj]
    simp only [Real.rpow_zero, mul_one]
    ring
  obtain ⟨τ, hnτ, hzeros, hs0, hsτ, hneg, hpos'⟩ := single_crossing_of_two_zeros
    (f := fun s => heavyValue h s j - heavyValue h s i)
    (fun x => (analyticAt_heavyValue hh hj x).sub (analyticAt_heavyValue hh hi x))
    (heavy_difference_zero_bound hh hi hij') h0 (by positivity : (0 : ℝ) < n + 1) hn hpos
  refine ⟨τ, by linarith [Nat.cast_nonneg (α := ℝ) n], ?_, hs0, hsτ, ?_, ?_⟩
  · simpa only [sub_eq_zero] using hzeros
  · intro s hs
    exact sub_neg.mp (hneg s hs)
  · intro s hs
    exact sub_pos.mp (hpos' s hs)

end
end EntropyConstrainedMissingMass
