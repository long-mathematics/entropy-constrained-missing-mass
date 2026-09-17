import EntropyConstrainedMissingMass.CertificateRootData
import EntropyConstrainedMissingMass.CertificateWinners

/-! Certified failures of unimodality and entropy-monotone optimizer type, Appendix D. -/
namespace EntropyConstrainedMissingMass.Certificates
noncomputable section
open Set

theorem heavy_comparisons_0 (j : ℕ) (hj : entropySupportIndex ((11 : ℝ)/10) ≤ j)
    (hM : j ≤ candidateCutoff 3 ((11 : ℝ)/10)) (hne : j ≠ 3) :
    heavyCandidateValue 3 ((11 : ℝ)/10) j < heavyCandidateValue 3 ((11 : ℝ)/10) 3 := by
  rw [index_0] at hj
  rw [cutoff_0] at hM
  have hw := value_0_heavy_3
  interval_cases j
  · exact (hne rfl).elim
  · linarith [value_0_heavy_4.2,hw.1]
  · linarith [value_0_heavy_5.2,hw.1]

theorem heavy_maximum_0 :
    sSup ((heavyCandidateValue 3 ((11 : ℝ)/10)) '' Ici (entropySupportIndex ((11 : ℝ)/10))) =
      heavyCandidateValue 3 ((11 : ℝ)/10) 3 := by
  apply heavy_sup_eq_of_comparisons (by norm_num) (by norm_num) (by norm_num [index_0])
  intro j hj hM
  by_cases he : j = 3
  · subst j; rfl
  · exact (heavy_comparisons_0 j hj hM he).le

theorem light_comparisons_0 (j : ℕ) (hj : entropySupportIndex ((11 : ℝ)/10) ≤ j)
    (hM : j ≤ candidateCutoff 3 ((11 : ℝ)/10)) :
    heavyCandidateValue 3 ((11 : ℝ)/10) j < lightValue 3 ((11 : ℝ)/10) := by
  rw [index_0] at hj
  rw [cutoff_0] at hM
  have hw := value_0_light_3
  interval_cases j
  · linarith [value_0_heavy_3.2,hw.1]
  · linarith [value_0_heavy_4.2,hw.1]
  · linarith [value_0_heavy_5.2,hw.1]

theorem optimal_value_0 : optimalValue 3 ((11 : ℝ)/10) = lightValue 3 ((11 : ℝ)/10) :=
  optimalValue_eq_light_of_comparisons (by norm_num) (by norm_num)
    (fun j hj hM => (light_comparisons_0 j hj hM).le)

theorem unique_optimizer_0 {ι : Type*} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible ((11 : ℝ)/10) ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible ((11 : ℝ)/10) → q.objective 3 ≤ p.objective 3) ↔
        ProbabilityVector.LightCandidateForm ((11 : ℝ)/10) p :=
  p.globalMax_iff_light_of_strict_comparisons (by norm_num) (by norm_num) light_comparisons_0

theorem heavy_comparisons_1 (j : ℕ) (hj : entropySupportIndex ((6 : ℝ)/5) ≤ j)
    (hM : j ≤ candidateCutoff 3 ((6 : ℝ)/5)) (hne : j ≠ 3) :
    heavyCandidateValue 3 ((6 : ℝ)/5) j < heavyCandidateValue 3 ((6 : ℝ)/5) 3 := by
  rw [index_1] at hj
  rw [cutoff_1] at hM
  have hw := value_1_heavy_3
  interval_cases j
  · exact (hne rfl).elim
  · linarith [value_1_heavy_4.2,hw.1]
  · linarith [value_1_heavy_5.2,hw.1]

theorem heavy_maximum_1 :
    sSup ((heavyCandidateValue 3 ((6 : ℝ)/5)) '' Ici (entropySupportIndex ((6 : ℝ)/5))) =
      heavyCandidateValue 3 ((6 : ℝ)/5) 3 := by
  apply heavy_sup_eq_of_comparisons (by norm_num) (by norm_num) (by norm_num [index_1])
  intro j hj hM
  by_cases he : j = 3
  · subst j; rfl
  · exact (heavy_comparisons_1 j hj hM he).le

theorem light_loses_1 : lightValue 3 ((6 : ℝ)/5) < heavyCandidateValue 3 ((6 : ℝ)/5) 3 := by
  linarith [value_1_light_3.2,value_1_heavy_3.1]

theorem optimal_value_1 : optimalValue 3 ((6 : ℝ)/5) = heavyCandidateValue 3 ((6 : ℝ)/5) 3 := by
  apply optimalValue_eq_heavy_of_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_1]) (by norm_num [cutoff_1]) light_loses_1.le
  intro j hj hM
  by_cases he : j = 3
  · subst j; rfl
  · exact (heavy_comparisons_1 j hj hM he).le

theorem unique_optimizer_1 {ι : Type*} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible ((6 : ℝ)/5) ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible ((6 : ℝ)/5) → q.objective 3 ≤ p.objective 3) ↔
        p.HeavyCandidateAt ((6 : ℝ)/5) 3 :=
  p.globalMax_iff_heavy_of_strict_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_1]) (by norm_num [cutoff_1]) light_loses_1 heavy_comparisons_1

theorem heavy_comparisons_2 (j : ℕ) (hj : entropySupportIndex ((7 : ℝ)/5) ≤ j)
    (hM : j ≤ candidateCutoff 3 ((7 : ℝ)/5)) (hne : j ≠ 4) :
    heavyCandidateValue 3 ((7 : ℝ)/5) j < heavyCandidateValue 3 ((7 : ℝ)/5) 4 := by
  rw [index_2] at hj
  rw [cutoff_2] at hM
  have hw := value_2_heavy_4
  interval_cases j
  · exact (hne rfl).elim
  · linarith [value_2_heavy_5.2,hw.1]
  · linarith [value_2_heavy_6.2,hw.1]

theorem heavy_maximum_2 :
    sSup ((heavyCandidateValue 3 ((7 : ℝ)/5)) '' Ici (entropySupportIndex ((7 : ℝ)/5))) =
      heavyCandidateValue 3 ((7 : ℝ)/5) 4 := by
  apply heavy_sup_eq_of_comparisons (by norm_num) (by norm_num) (by norm_num [index_2])
  intro j hj hM
  by_cases he : j = 4
  · subst j; rfl
  · exact (heavy_comparisons_2 j hj hM he).le

theorem light_comparisons_2 (j : ℕ) (hj : entropySupportIndex ((7 : ℝ)/5) ≤ j)
    (hM : j ≤ candidateCutoff 3 ((7 : ℝ)/5)) :
    heavyCandidateValue 3 ((7 : ℝ)/5) j < lightValue 3 ((7 : ℝ)/5) := by
  rw [index_2] at hj
  rw [cutoff_2] at hM
  have hw := value_2_light_4
  interval_cases j
  · linarith [value_2_heavy_4.2,hw.1]
  · linarith [value_2_heavy_5.2,hw.1]
  · linarith [value_2_heavy_6.2,hw.1]

theorem optimal_value_2 : optimalValue 3 ((7 : ℝ)/5) = lightValue 3 ((7 : ℝ)/5) :=
  optimalValue_eq_light_of_comparisons (by norm_num) (by norm_num)
    (fun j hj hM => (light_comparisons_2 j hj hM).le)

theorem unique_optimizer_2 {ι : Type*} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible ((7 : ℝ)/5) ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible ((7 : ℝ)/5) → q.objective 3 ≤ p.objective 3) ↔
        ProbabilityVector.LightCandidateForm ((7 : ℝ)/5) p :=
  p.globalMax_iff_light_of_strict_comparisons (by norm_num) (by norm_num) light_comparisons_2

theorem heavy_comparisons_3 (j : ℕ) (hj : entropySupportIndex ((19 : ℝ)/8) ≤ j)
    (hM : j ≤ candidateCutoff 8 ((19 : ℝ)/8)) (hne : j ≠ 14) :
    heavyCandidateValue 8 ((19 : ℝ)/8) j < heavyCandidateValue 8 ((19 : ℝ)/8) 14 := by
  rw [index_3] at hj
  rw [cutoff_3] at hM
  have hw := value_3_heavy_14
  interval_cases j
  · linarith [value_3_heavy_10.2,hw.1]
  · linarith [value_3_heavy_11.2,hw.1]
  · linarith [value_3_heavy_12.2,hw.1]
  · linarith [value_3_heavy_13.2,hw.1]
  · exact (hne rfl).elim
  · linarith [value_3_heavy_15.2,hw.1]
  · linarith [value_3_heavy_16.2,hw.1]
  · linarith [value_3_heavy_17.2,hw.1]
  · linarith [value_3_heavy_18.2,hw.1]
  · linarith [value_3_heavy_19.2,hw.1]
  · linarith [value_3_heavy_20.2,hw.1]

theorem heavy_maximum_3 :
    sSup ((heavyCandidateValue 8 ((19 : ℝ)/8)) '' Ici (entropySupportIndex ((19 : ℝ)/8))) =
      heavyCandidateValue 8 ((19 : ℝ)/8) 14 := by
  apply heavy_sup_eq_of_comparisons (by norm_num) (by norm_num) (by norm_num [index_3])
  intro j hj hM
  by_cases he : j = 14
  · subst j; rfl
  · exact (heavy_comparisons_3 j hj hM he).le

theorem light_loses_3 : lightValue 8 ((19 : ℝ)/8) < heavyCandidateValue 8 ((19 : ℝ)/8) 14 := by
  linarith [value_3_light_10.2,value_3_heavy_14.1]

theorem optimal_value_3 : optimalValue 8 ((19 : ℝ)/8) = heavyCandidateValue 8 ((19 : ℝ)/8) 14 := by
  apply optimalValue_eq_heavy_of_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_3]) (by norm_num [cutoff_3]) light_loses_3.le
  intro j hj hM
  by_cases he : j = 14
  · subst j; rfl
  · exact (heavy_comparisons_3 j hj hM he).le

theorem unique_optimizer_3 {ι : Type*} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible ((19 : ℝ)/8) ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible ((19 : ℝ)/8) → q.objective 8 ≤ p.objective 8) ↔
        p.HeavyCandidateAt ((19 : ℝ)/8) 14 :=
  p.globalMax_iff_heavy_of_strict_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_3]) (by norm_num [cutoff_3]) light_loses_3 heavy_comparisons_3

/-- The three certified heavy entries form a strict valley, precluding unimodality. -/
theorem nonunimodal_example :
    heavyCandidateValue 8 (19/8) 11 < heavyCandidateValue 8 (19/8) 10 ∧
      heavyCandidateValue 8 (19/8) 11 < heavyCandidateValue 8 (19/8) 12 := by
  constructor <;> linarith [value_3_heavy_10.1,value_3_heavy_11.2,value_3_heavy_12.1]

/-- The displayed global optimum bracket at h=19/8. -/
theorem global_value_19_8 :
    (458686581808 : ℝ)/10^12 < optimalValue 8 (19/8) ∧
      optimalValue 8 (19/8) < (458686581809 : ℝ)/10^12 := by
  rw [optimal_value_3]
  convert value_3_heavy_14 using 1 <;> norm_num

end
end EntropyConstrainedMissingMass.Certificates
