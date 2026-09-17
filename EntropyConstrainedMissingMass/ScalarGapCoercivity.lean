import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Quantitative and filter coercivity of the scalar gap v-log(v)-1. -/
namespace EntropyConstrainedMissingMass
open Set Filter
open scoped Topology
noncomputable section

def scalarGap (v : ℝ) : ℝ := v - Real.log v - 1

theorem scalarGap_pos {v : ℝ} (hv : 0 < v) (hne : v ≠ 1) : 0 < scalarGap v := by
  have := Real.log_lt_sub_one_of_pos hv hne
  dsimp [scalarGap]
  linarith

theorem hasDerivAt_scalarGap {v : ℝ} (hv : 0 < v) :
    HasDerivAt scalarGap (1-1/v) v := by
  change HasDerivAt (fun x : ℝ => x - Real.log x - 1) _ v
  convert ((hasDerivAt_id v).sub (Real.hasDerivAt_log hv.ne')).sub_const 1 using 1
  all_goals first | rfl | simp only [one_div]

theorem scalarGap_strictMono : StrictMonoOn scalarGap (Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · intro v hv
    change 1 ≤ v at hv
    exact (hasDerivAt_scalarGap (by linarith [hv])).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ici, mem_Ioi] at hv
    have hv0 : 0 < v := by linarith [hv]
    rw [(hasDerivAt_scalarGap hv0).deriv]
    have := (div_lt_one hv0).mpr hv
    linarith

theorem scalarGap_strictAnti : StrictAntiOn scalarGap (Ioc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · intro v hv
    exact (hasDerivAt_scalarGap hv.1).continuousAt.continuousWithinAt
  · intro v hv
    rw [interior_Ioc] at hv
    rw [(hasDerivAt_scalarGap hv.1).deriv]
    have := (one_lt_div hv.1).mpr hv.2
    linarith

/-- A positive gap away from every fixed neighborhood of one, uniformly over v. -/
theorem scalarGap_coercive (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ℝ, 0 < v → scalarGap v < δ → |v-1| < ε := by
  by_cases hε1 : ε < 1
  · have hminus := scalarGap_pos (v := 1-ε) (by linarith) (by linarith)
    have hplus := scalarGap_pos (v := 1+ε) (by linarith) (by linarith)
    refine ⟨min (scalarGap (1-ε)) (scalarGap (1+ε)), lt_min hminus hplus, ?_⟩
    intro v hv hg
    apply abs_lt.mpr
    constructor
    · by_contra hn
      have hvle : v ≤ 1-ε := by linarith
      have hm := scalarGap_strictAnti.antitoneOn ⟨hv,by linarith⟩
        ⟨by linarith,by linarith⟩ hvle
      have hg' := hg.trans_le (min_le_left _ _)
      linarith
    · by_contra hn
      have hvle : 1+ε ≤ v := by linarith
      have hm := scalarGap_strictMono.monotoneOn (by change 1 ≤ 1+ε; linarith)
        (by change 1 ≤ v; linarith) hvle
      have hg' := hg.trans_le (min_le_right _ _)
      linarith
  · refine ⟨scalarGap (1+ε), scalarGap_pos (by linarith) (by linarith), ?_⟩
    intro v hv hg
    apply abs_lt.mpr
    refine ⟨by linarith, ?_⟩
    by_contra hn
    have hvle : 1+ε ≤ v := by linarith
    have hm := scalarGap_strictMono.monotoneOn (by change 1 ≤ 1+ε; linarith)
      (by change 1 ≤ v; linarith) hvle
    linarith

/-- The scalar-gap conclusion is valid along arbitrary filters, hence for every
choice of optimizers once its gap tends to zero. -/
theorem tendsto_one_of_scalarGap {α : Type*} {l : Filter α} {v : α → ℝ}
    (hv : ∀ᶠ a in l, 0 < v a) (hg : Tendsto (fun a => scalarGap (v a)) l (𝓝 0)) :
    Tendsto v l (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := scalarGap_coercive ε hε
  filter_upwards [hv, hg.eventually (gt_mem_nhds hδ)] with a ha hga
  simpa [Real.dist_eq] using hd (v a) ha hga

end
end EntropyConstrainedMissingMass
