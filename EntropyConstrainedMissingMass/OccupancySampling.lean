import EntropyConstrainedMissingMass.SampleMonotonicity
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Genuine IID sampling laws and nonnegative occupancy expectations.
For discovery, sample position zero is the new observation and positions `j.succ`
are the preceding observations. This is a relabeling of the IID product coordinates. -/
open MeasureTheory Set
open scoped ENNReal
namespace EntropyConstrainedMissingMass
noncomputable section
namespace ProbabilityVector

/-- The discrete sampling law associated to the original probability vector. -/
def samplingPMF (p : ProbabilityVector ℕ) : PMF ℕ := ⟨fun i => ENNReal.ofReal (p.coord i), by
  have he : ∑' i, ENNReal.ofReal (p.coord i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg p.coord_nonneg p.summable_coord,p.tsum_coord]
    simp
  exact he ▸ ENNReal.summable.hasSum⟩

def samplingMeasure (p : ProbabilityVector ℕ) : Measure ℕ := p.samplingPMF.toMeasure

instance samplingMeasure_probability (p : ProbabilityVector ℕ) : IsProbabilityMeasure p.samplingMeasure := by
  unfold samplingMeasure
  infer_instance

/-- The product law of `n` independent samples, each with mass function `p`. -/
def sampleLaw (p : ProbabilityVector ℕ) (n : ℕ) : Measure (Fin n → ℕ) :=
  Measure.pi (fun _ => p.samplingMeasure)

instance sampleLaw_probability (p : ProbabilityVector ℕ) (n : ℕ) : IsProbabilityMeasure (p.sampleLaw n) := by
  unfold sampleLaw
  infer_instance

@[simp] theorem samplingMeasure_singleton (p : ProbabilityVector ℕ) (i : ℕ) :
    p.samplingMeasure {i} = ENNReal.ofReal (p.coord i) :=
  PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)

theorem samplingMeasure_ne (p : ProbabilityVector ℕ) (i : ℕ) :
    p.samplingMeasure ({i}ᶜ) = ENNReal.ofReal (1-p.coord i) := by
  rw [measure_compl (measurableSet_singleton _) (by simp), measure_univ,samplingMeasure_singleton,
    ENNReal.ofReal_sub 1 (p.coord_nonneg i)]
  simp

/-- Event that a specified symbol has not appeared. -/
def absentEvent (n i : ℕ) : Set (Fin n → ℕ) := {x | ∀ j, x j ≠ i}

theorem measure_absentEvent (p : ProbabilityVector ℕ) (n i : ℕ) :
    p.sampleLaw n (absentEvent n i) = ENNReal.ofReal ((1-p.coord i)^n) := by
  have he : absentEvent n i = Set.univ.pi (fun _ : Fin n => ({i} : Set ℕ)ᶜ) := by ext x; simp [absentEvent]
  rw [he,sampleLaw,Measure.pi_pi]
  simp only [samplingMeasure_ne,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.ofReal_pow (sub_nonneg.mpr (p.coord_le_one i))]

/-- The random mass of symbols unseen in the observed sample. -/
def unseenMass (p : ProbabilityVector ℕ) {n : ℕ} (x : Fin n → ℕ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (p.coord i) * (absentEvent n i).indicator 1 x

/-- The expected missing mass is the paper's objective, under the genuine IID law. -/
theorem lintegral_unseenMass (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫⁻ x, p.unseenMass x ∂p.sampleLaw n) = ENNReal.ofReal (p.objective n) := by
  unfold unseenMass
  rw [lintegral_tsum (fun i => by exact (measurable_const.mul (measurable_const.indicator
    (Set.to_countable _).measurableSet)).aemeasurable)]
  calc
    _ = ∑' i, ENNReal.ofReal (missingMassTerm n (p.coord i)) := by
      apply tsum_congr
      intro i
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator_one (Set.to_countable _).measurableSet,measure_absentEvent,
        ← ENNReal.ofReal_mul (p.coord_nonneg i)]
      rfl
    _ = ENNReal.ofReal (p.objective n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun i => missingMassTerm_nonneg n
        (p.coord_nonneg i) (p.coord_le_one i)) (p.objective_summable n)).symm

/-- Symbol `i` occurs exactly at sample position `j`. -/
def onlyAtEvent (n i : ℕ) (j : Fin n) : Set (Fin n → ℕ) :=
  {x | x j = i ∧ ∀ k, k ≠ j → x k ≠ i}

theorem measure_onlyAtEvent (p : ProbabilityVector ℕ) (n i : ℕ) (j : Fin n) :
    p.sampleLaw n (onlyAtEvent n i j) = ENNReal.ofReal (p.coord i * (1-p.coord i)^(n-1)) := by
  classical
  have he : onlyAtEvent n i j = Set.univ.pi (fun k : Fin n => if k=j then {i} else ({i} : Set ℕ)ᶜ) := by
    ext x
    simp only [onlyAtEvent,Set.mem_ofPred_eq,Set.mem_univ_pi]
    constructor
    · intro hx k
      by_cases hk : k=j
      · subst k; simpa using hx.1
      · simpa [hk] using hx.2 k hk
    · intro hx
      refine ⟨by simpa using hx j,?_⟩
      intro k hk
      simpa [hk] using hx k
  rw [he,sampleLaw,Measure.pi_pi]
  simp only [apply_ite,samplingMeasure_singleton,samplingMeasure_ne]
  rw [Finset.prod_ite]
  simp only [Finset.filter_eq',Finset.mem_univ,ite_true,Finset.card_singleton,pow_one,
    Finset.filter_ne',Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ,Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr (p.coord_le_one i)),← ENNReal.ofReal_mul (p.coord_nonneg i)]

/-- Event that a symbol occurs exactly once. -/
def singletonEvent (n i : ℕ) : Set (Fin n → ℕ) := ⋃ j : Fin n, onlyAtEvent n i j

theorem measure_singletonEvent (p : ProbabilityVector ℕ) (n i : ℕ) :
    p.sampleLaw n (singletonEvent n i) = ENNReal.ofReal ((n : ℝ)*p.coord i*(1-p.coord i)^(n-1)) := by
  classical
  have hdisj : Pairwise (fun j k : Fin n => Disjoint (onlyAtEvent n i j) (onlyAtEvent n i k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 k hjk.symm hy.1
  rw [singletonEvent,measure_iUnion hdisj (fun _ => (Set.to_countable _).measurableSet)]
  simp only [measure_onlyAtEvent,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  ring

/-- The nonnegative number of symbols appearing exactly once, as its counting sum. -/
def singletonCount {n : ℕ} (x : Fin n → ℕ) : ℝ≥0∞ :=
  ∑' i, (singletonEvent n i).indicator 1 x

/-- The singleton expectation identity for the actual product sampling measure. -/
theorem lintegral_singletonCount (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫⁻ x : Fin n → ℕ, singletonCount x ∂p.sampleLaw n) = ENNReal.ofReal ((n : ℝ)*p.objective (n-1)) := by
  unfold singletonCount
  rw [lintegral_tsum (fun i => (measurable_of_countable _).aemeasurable)]
  simp_rw [lintegral_indicator_one (Set.to_countable _).measurableSet,measure_singletonEvent]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),objective,
    ENNReal.ofReal_tsum_of_nonneg (fun i => missingMassTerm_nonneg (n-1) (p.coord_nonneg i) (p.coord_le_one i))
      (p.objective_summable (n-1)),← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro i
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  unfold missingMassTerm
  ring

/-- The probability mass covered by the observed symbols. -/
def coveredMass (p : ProbabilityVector ℕ) {n : ℕ} (x : Fin n → ℕ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (p.coord i) * (absentEvent n i)ᶜ.indicator 1 x

theorem unseenMass_add_coveredMass (p : ProbabilityVector ℕ) {n : ℕ} (x : Fin n → ℕ) :
    p.unseenMass x + p.coveredMass x = 1 := by
  classical
  unfold unseenMass coveredMass
  rw [← ENNReal.tsum_add]
  have he (i : ℕ) : ENNReal.ofReal (p.coord i)*(absentEvent n i).indicator 1 x +
      ENNReal.ofReal (p.coord i)*(absentEvent n i)ᶜ.indicator 1 x = ENNReal.ofReal (p.coord i) := by
    by_cases hx : x ∈ absentEvent n i <;> simp [hx]
  simp_rw [he]
  exact p.samplingPMF.tsum_coe

theorem lintegral_coveredMass (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫⁻ x, p.coveredMass x ∂p.sampleLaw n) = ENNReal.ofReal (1-p.objective n) := by
  have he : ENNReal.ofReal (p.objective n) + (∫⁻ x, p.coveredMass x ∂p.sampleLaw n) = 1 := by
    rw [← p.lintegral_unseenMass n,← lintegral_add_left (measurable_of_countable _)]
    simp only [p.unseenMass_add_coveredMass,lintegral_const,measure_univ,mul_one]
  rw [ENNReal.ofReal_sub 1 (p.objective_nonneg n),ENNReal.ofReal_one]
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (by simpa only [add_comm] using he)

/-- The new sample at position zero is absent from the other `n` observations. -/
def discoveryEvent (n : ℕ) : Set (Fin (n+1) → ℕ) := ⋃ i, onlyAtEvent (n+1) i 0

theorem mem_discoveryEvent {n : ℕ} (x : Fin (n+1) → ℕ) :
    x ∈ discoveryEvent n ↔ ∀ j : Fin n, x j.succ ≠ x 0 := by
  simp only [discoveryEvent,Set.mem_iUnion,onlyAtEvent,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i,hi,hrest⟩ j
    rw [hi]
    exact hrest j.succ (Fin.succ_ne_zero j)
  · intro hx
    refine ⟨x 0,rfl,?_⟩
    intro j hj
    revert hj
    refine Fin.cases ?_ (fun k => ?_) j
    · intro hj; exact (hj rfl).elim
    · intro _; exact hx k

/-- The discovery probability is precisely the original missing-mass objective. -/
theorem measure_discoveryEvent (p : ProbabilityVector ℕ) (n : ℕ) :
    p.sampleLaw (n+1) (discoveryEvent n) = ENNReal.ofReal (p.objective n) := by
  have hd : Pairwise (fun i j : ℕ => Disjoint (onlyAtEvent (n+1) i 0) (onlyAtEvent (n+1) j 0)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.1.symm.trans hj.1)
  rw [discoveryEvent,measure_iUnion hd (fun _ => (Set.to_countable _).measurableSet)]
  simp only [measure_onlyAtEvent,Nat.add_sub_cancel]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i => missingMassTerm_nonneg n
    (p.coord_nonneg i) (p.coord_le_one i)) (p.objective_summable n)).symm

/-- The indicator of discovering a previously unseen symbol. -/
def discovery {n : ℕ} (x : Fin (n+1) → ℕ) : ℝ≥0∞ := (discoveryEvent n).indicator 1 x

theorem lintegral_discovery (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫⁻ x : Fin (n+1) → ℕ, discovery x ∂p.sampleLaw (n+1)) = ENNReal.ofReal (p.objective n) := by
  change (∫⁻ x : Fin (n+1) → ℕ, (discoveryEvent n).indicator 1 x ∂p.sampleLaw (n+1)) = _
  rw [lintegral_indicator_one (Set.to_countable _).measurableSet,measure_discoveryEvent]

/-- Number of distinct observed symbols. -/
def distinctCount {n : ℕ} (x : Fin n → ℕ) : ℕ := (Finset.univ.image x).card

/-- Number of observed symbols having exactly one occurrence. -/
def singletonCountNat {n : ℕ} (x : Fin n → ℕ) : ℕ := by
  classical
  exact ((Finset.univ.image x).filter (fun i => ∃! j, x j = i)).card

theorem mem_singletonEvent {n i : ℕ} (x : Fin n → ℕ) :
    x ∈ singletonEvent n i ↔ ∃! j, x j = i := by
  simp only [singletonEvent,Set.mem_iUnion,onlyAtEvent,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j,hj,hrest⟩
    refine ⟨j,hj,?_⟩
    intro k hk
    by_contra hne
    exact hrest k hne hk
  · rintro ⟨j,hj,hunique⟩
    exact ⟨j,hj,fun k hk hki => hk (hunique k hki)⟩

/-- The counting-sum singleton variable is exactly the ordinary finite count. -/
theorem singletonCount_eq_nat {n : ℕ} (x : Fin n → ℕ) : singletonCount x = (singletonCountNat x : ℝ≥0∞) := by
  classical
  unfold singletonCount singletonCountNat
  rw [tsum_eq_sum (s := Finset.univ.image x) (by
    intro i hi
    apply Set.indicator_of_notMem
    intro hx
    obtain ⟨j,hj,_⟩ := (mem_singletonEvent x).mp hx
    exact hi (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩))]
  simp only [Set.indicator_apply,Pi.one_apply,mem_singletonEvent]
  exact Finset.sum_boole _ _

/-- Adding the new observation changes the distinct count exactly on the discovery event. -/
theorem discovery_eq_count_difference {n : ℕ} (x : Fin (n+1) → ℕ) :
    discovery x = ((distinctCount x - distinctCount (fun j : Fin n => x j.succ) : ℕ) : ℝ≥0∞) := by
  classical
  have himage : Finset.univ.image x = insert (x 0) (Finset.univ.image (fun j : Fin n => x j.succ)) := by
    ext i
    simp [Fin.exists_fin_succ,eq_comm]
  have hmem : x 0 ∉ Finset.univ.image (fun j : Fin n => x j.succ) ↔ x ∈ discoveryEvent n := by
    rw [mem_discoveryEvent]
    simp
  unfold discovery distinctCount
  rw [himage]
  by_cases hx : x ∈ discoveryEvent n
  · rw [Set.indicator_of_mem hx, Finset.card_insert_of_notMem (hmem.mpr hx)]
    simp
  · have hi : x 0 ∈ Finset.univ.image (fun j : Fin n => x j.succ) := by tauto
    rw [Set.indicator_of_notMem hx,Finset.insert_eq_of_mem hi]
    simp

/-- Ordinary real expectation of the actual singleton count. -/
theorem integral_singletonCount (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫ x : Fin n → ℕ, (singletonCountNat x : ℝ) ∂p.sampleLaw n) = (n : ℝ)*p.objective (n-1) := by
  have he := p.lintegral_singletonCount n
  have hfin : (∫⁻ x : Fin n → ℕ, singletonCount x ∂p.sampleLaw n) ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
  have hi := integral_toReal (measurable_of_countable (fun x : Fin n → ℕ => singletonCount x)).aemeasurable
    (ae_lt_top (measurable_of_countable _) hfin)
  have ho : (∫⁻ x : Fin n → ℕ, singletonCount x ∂p.sampleLaw n).toReal = (n : ℝ)*p.objective (n-1) := by
    rw [p.lintegral_singletonCount n,ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (p.objective_nonneg _))]
  simpa only [singletonCount_eq_nat,ENNReal.toReal_natCast] using hi.trans ho

/-- Ordinary expectation of the discovery indicator. -/
theorem integral_discovery (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫ x : Fin (n+1) → ℕ, (discovery x).toReal ∂p.sampleLaw (n+1)) = p.objective n := by
  rw [integral_toReal (measurable_of_countable _).aemeasurable
    (ae_lt_top (measurable_of_countable _) (by rw [lintegral_discovery]; exact ENNReal.ofReal_ne_top)),
    lintegral_discovery,ENNReal.toReal_ofReal (p.objective_nonneg n)]

/-- Ordinary real expectation of covered mass. -/
theorem integral_coveredMass (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫ x : Fin n → ℕ, (p.coveredMass x).toReal ∂p.sampleLaw n) = 1-p.objective n := by
  rw [integral_toReal (measurable_of_countable _).aemeasurable
    (ae_lt_top (measurable_of_countable _) (by rw [lintegral_coveredMass]; exact ENNReal.ofReal_ne_top)),
    lintegral_coveredMass,ENNReal.toReal_ofReal (sub_nonneg.mpr (p.objective_le_one n))]

/-- Covered mass as the ordinary finite sum over the distinct observed symbols. -/
def coverage (p : ProbabilityVector ℕ) {n : ℕ} (x : Fin n → ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.image x, p.coord i

theorem coveredMass_eq_ofReal_coverage (p : ProbabilityVector ℕ) {n : ℕ} (x : Fin n → ℕ) :
    p.coveredMass x = ENNReal.ofReal (p.coverage x) := by
  classical
  have hseen (i : ℕ) : x ∈ (absentEvent n i)ᶜ ↔ i ∈ Finset.univ.image x := by
    simp [absentEvent]
  unfold coveredMass coverage
  rw [tsum_eq_sum (s := Finset.univ.image x) (by
    intro i hi
    rw [Set.indicator_of_notMem (by simpa only [hseen] using hi),mul_zero])]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => p.coord_nonneg i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Set.indicator_of_mem ((hseen i).mpr hi)]
  simp

theorem integral_coverage (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫ x : Fin n → ℕ, p.coverage x ∂p.sampleLaw n) = 1-p.objective n := by
  have he := p.integral_coveredMass n
  have hn (x : Fin n → ℕ) : 0 ≤ p.coverage x := Finset.sum_nonneg (fun i _ => p.coord_nonneg i)
  simpa only [coveredMass_eq_ofReal_coverage,ENNReal.toReal_ofReal (hn _)] using he

/-- The discovery identity in the paper's original distinct-count notation. -/
theorem integral_distinctCount_increment (p : ProbabilityVector ℕ) (n : ℕ) :
    (∫ x : Fin (n+1) → ℕ, (distinctCount x : ℝ) -
      (distinctCount (fun j : Fin n => x j.succ) : ℝ) ∂p.sampleLaw (n+1)) = p.objective n := by
  have hc (x : Fin (n+1) → ℕ) : distinctCount (fun j : Fin n => x j.succ) ≤ distinctCount x := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨j.succ,Finset.mem_univ _,rfl⟩
  have he := p.integral_discovery n
  simpa only [discovery_eq_count_difference,ENNReal.toReal_natCast,Nat.cast_sub (hc _)] using he

end ProbabilityVector
end
end EntropyConstrainedMissingMass
