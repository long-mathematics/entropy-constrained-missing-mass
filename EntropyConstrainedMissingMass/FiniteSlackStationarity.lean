import EntropyConstrainedMissingMass.FiniteClassification
import EntropyConstrainedMissingMass.FiniteStationarityPolynomial

/-! Full support and genuine first-order stationarity when the finite-alphabet entropy
constraint is inactive. -/
open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass.ProbabilityVector
noncomputable section
variable {ι : Type*}

/-- On a finite alphabet extended entropy is continuous, including boundary coordinates. -/
theorem continuous_entropy_finite [Fintype ι] : Continuous (fun p : ProbabilityVector ι => p.entropy) := by
  unfold entropy
  simp only [tsum_fintype]
  exact continuous_finsetSum _ (fun i _ => ENNReal.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp (continuous_coord i)))

theorem localMax_of_entropy_slack [Fintype ι] (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (hp : LocalMaximizer t h p) (hslack : p.entropy < ENNReal.ofReal h) :
    IsLocalMax (fun q : ProbabilityVector ι => q.objective t) p := by
  have hn : Feasible h ∈ 𝓝 p := Filter.mem_of_superset
    ((isOpen_lt continuous_entropy_finite continuous_const).mem_nhds hslack) (fun q hx => show q.entropy ≤ ENNReal.ofReal h from hx.le)
  have he := nhdsWithin_eq_nhds.mpr hn
  have hloc : ∀ᶠ q in 𝓝[Feasible h] p, q.objective t ≤ p.objective t := hp.2
  rw [he] at hloc
  exact hloc

/-- A zero coordinate would permit an improving split, so slack maxima have full support. -/
theorem coord_pos_of_entropy_slack (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hslack : p.entropy < ENNReal.ofReal h) (i : ι) :
    0 < p.coord i := by
  apply lt_of_le_of_ne (p.coord_nonneg i)
  intro he
  exact hslack.ne (p.entropy_saturation_of_zero_coord ht hp he.symm)

/-- The equality of atom derivatives is derived from actual local maximality
along a two-coordinate, mass-preserving path. -/
theorem deriv_eq_of_entropy_slack [Fintype ι] (p : ProbabilityVector ι) {t : ℕ} {h : ℝ}
    (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hslack : p.entropy < ENNReal.ofReal h) (i j : ι) :
    deriv (missingMassTerm t) (p.coord i) = deriv (missingMassTerm t) (p.coord j) := by
  by_cases hij : i = j
  · simp [hij]
  let e : Fin 2 ↪ ι := ⟨![i,j], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩
  let v : ℝ → Fin 2 → ℝ := fun r => ![p.coord i+r,p.coord j-r]
  have hbase (k : Fin 2) : v 0 k = p.coord (e k) := by fin_cases k <;> simp [v,e]
  have hlim (k : Fin 2) : Tendsto (fun r => v r k) (𝓝 0) (𝓝 (p.coord (e k))) := by
    rw [← hbase k]
    apply ContinuousAt.tendsto
    fin_cases k <;> dsimp [v] <;> fun_prop
  have hpos : ∀ᶠ r in 𝓝 (0 : ℝ), 0 ≤ p.coord i+r ∧ 0 ≤ p.coord j-r := by
    have hi := p.coord_pos_of_entropy_slack ht hp hslack i
    have hj := p.coord_pos_of_entropy_slack ht hp hslack j
    filter_upwards [eventually_gt_nhds (show -p.coord i < (0 : ℝ) by linarith),
      eventually_lt_nhds (show (0 : ℝ) < p.coord j from hj)] with r hr hr'
    constructor <;> linarith
  have hgood : ∀ᶠ r in 𝓝 (0 : ℝ), (∀ k, 0 ≤ v r k) ∧ ∑ k, v r k = ∑ k, p.coord (e k) := by
    filter_upwards [hpos] with r hr
    constructor
    · intro k
      fin_cases k
      · exact hr.1
      · exact hr.2
    · simp [v,e,Fin.sum_univ_two]
  have hmax := (tendsto_perturbEmbedded p e v hlim).eventually (p.localMax_of_entropy_slack hp hslack)
  have hm : IsLocalMax (fun r => missingMassTerm t (p.coord i+r) + missingMassTerm t (p.coord j-r)) 0 := by
    filter_upwards [hmax,hgood] with r hr hg
    rw [perturbEmbedded_eq _ _ _ hg.1 hg.2, objective_replaceEmbedded] at hr
    simp only [v,e,Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, sub_zero] at hr ⊢
    change p.objective t + (missingMassTerm t (p.coord i+r)+missingMassTerm t (p.coord j-r)) -
      (missingMassTerm t (p.coord i)+missingMassTerm t (p.coord j)) ≤ p.objective t at hr
    linarith
  have hd₁ := ((hasDerivAt_missingMassTerm t ht (p.coord i+0)).differentiableAt.hasDerivAt).comp 0
      ((hasDerivAt_id 0).const_add (p.coord i))
  have hd₂ := ((hasDerivAt_missingMassTerm t ht (p.coord j-0)).differentiableAt.hasDerivAt).comp 0
      ((hasDerivAt_id 0).const_sub (p.coord j))
  have hd : HasDerivAt (fun r => missingMassTerm t (p.coord i+r) + missingMassTerm t (p.coord j-r))
      (deriv (missingMassTerm t) (p.coord i) - deriv (missingMassTerm t) (p.coord j)) 0 := by
    convert hd₁.add hd₂ using 1 <;> simp [Function.comp_def, sub_eq_add_neg]
    rfl
  exact sub_eq_zero.mp (hm.hasDerivAt_eq_zero hd)

end
end EntropyConstrainedMissingMass.ProbabilityVector
