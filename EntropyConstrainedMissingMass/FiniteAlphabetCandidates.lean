import EntropyConstrainedMissingMass.FiniteSlackStationarity

/-! Exhaustive saturated and inactive-constraint candidate forms on a fixed finite alphabet. -/
open Set
set_option backward.isDefEq.respectTransparency false
namespace EntropyConstrainedMissingMass
noncomputable section
namespace ProbabilityVector

theorem zeroExtend_trans {ι κ γ : Type*} (e : ι ↪ κ) (f : κ ↪ γ) (p : ProbabilityVector ι) :
    zeroExtend f (zeroExtend e p) = zeroExtend (e.trans f) p := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext j
  change (zeroExtend f (zeroExtend e p)).coord j = (zeroExtend (e.trans f) p).coord j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨k,rfl⟩ := hj
    rw [coord_zeroExtend_apply]
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hk
      rw [coord_zeroExtend_apply]
      exact (coord_zeroExtend_apply (e.trans f) p i).symm
    · rw [coord_zeroExtend_of_not_mem_range _ _ _ hk,
        coord_zeroExtend_of_not_mem_range _ _ _ (by
          rintro ⟨i,hi⟩; exact hk ⟨i,f.injective hi⟩)]
  · rw [coord_zeroExtend_of_not_mem_range _ _ _ hj,
      coord_zeroExtend_of_not_mem_range _ _ _ (by rintro ⟨i,hi⟩; exact hj ⟨e i,hi⟩)]

/-- Zero insertion from the actual finite alphabet to the common countable alphabet. -/
def finiteToNat {N : ℕ} (p : ProbabilityVector (Fin N)) : ProbabilityVector ℕ :=
  zeroExtend ⟨Fin.val,Fin.val_injective⟩ p

@[simp] theorem entropy_finiteToNat {N : ℕ} (p : ProbabilityVector (Fin N)) :
    p.finiteToNat.entropy = p.entropy := entropy_zeroExtend _ _

@[simp] theorem objective_finiteToNat {N : ℕ} (p : ProbabilityVector (Fin N)) (t : ℕ) :
    p.finiteToNat.objective t = p.objective t := objective_zeroExtend _ _ _

theorem uniformOnSupport_zeroExtend {ι κ : Type*} (p : ProbabilityVector ι)
    (hu : p.UniformOnSupport) (e : ι ↪ κ) : (zeroExtend e p).UniformOnSupport := by
  intro i j hi hj
  have hir : i ∈ Set.range e := by
    by_contra hn
    rw [coord_zeroExtend_of_not_mem_range _ _ _ hn] at hi
    exact (lt_irrefl _ hi)
  have hjr : j ∈ Set.range e := by
    by_contra hn
    rw [coord_zeroExtend_of_not_mem_range _ _ _ hn] at hj
    exact (lt_irrefl _ hj)
  obtain ⟨a,rfl⟩ := hir
  obtain ⟨b,rfl⟩ := hjr
  simpa only [coord_zeroExtend_apply] using hu a b (by simpa using hi) (by simpa using hj)

/-- Every saturated finite-alphabet maximum is a candidate in the truncated
countable list after zero insertion. This includes the full-support uniform
endpoint, for which the light parametrization has one additional zero atom. -/
theorem finite_candidate_complete_saturated {N t : ℕ} (p : ProbabilityVector (Fin N))
    {h : ℝ} (ht : 1 ≤ t) (hh : 0 < h) (hp : LocalMaximizer t h p)
    (he : p.entropy = ENNReal.ofReal h)
    (hmax : ∀ q : ProbabilityVector (Fin N), q ∈ Feasible h → q.objective t ≤ p.objective t) :
    LightCandidateForm h p.finiteToNat ∨ CutoffHeavyCandidateForm t h p.finiteToNat := by
  classical
  by_cases hu : p.UniformOnSupport
  · have huf := p.uniformOnSupport_zeroExtend hu ⟨Fin.val,Fin.val_injective⟩
    have hfin : (Function.support p.finiteToNat.coord).Finite := by
      apply (Set.finite_range (fun i : Fin N => (i : ℕ))).subset
      intro i hi
      by_contra hn
      exact hi (coord_zeroExtend_of_not_mem_range _ _ _ hn)
    obtain ⟨n,hn,e,hrep,hent⟩ := p.finiteToNat.uniform_form_entropy hfin huf
    have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hlog : Real.log (n : ℝ) = h :=
      (ENNReal.ofReal_eq_ofReal_iff hlogpos hh.le).mp (hent.symm.trans (by simpa using he))
    have hk : entropySupportIndex h = n := by
      unfold entropySupportIndex
      rw [← hlog, Real.exp_log (Nat.cast_pos.mpr hn)]
      exact Nat.floor_natCast n
    left
    unfold LightCandidateForm
    rw [hk]
    exact ⟨0,hn,by constructor <;> norm_num,e,⟨le_refl 0,by positivity⟩,
      by simpa only [branchEntropy_zero] using hlog,hrep⟩
  · obtain ⟨m,z,hm,hz,e,hneq,hrep⟩ := p.exceptional_form_of_localMax ht hp hu
    have hzc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le,hz.2.le⟩
    have hbranch : branchEntropy m z = h := by
      rw [hrep,entropy_zeroExtend,entropy_candidateVector] at he
      exact (ENNReal.ofReal_eq_ofReal_iff (branchEntropy_nat_nonneg hm hzc) hh.le).mp he
    have hext : p.finiteToNat = zeroExtend (e.trans ⟨Fin.val,Fin.val_injective⟩)
        (candidateVector m z hm hzc) := by
      rw [hrep]
      exact zeroExtend_trans _ _ _
    have hunif : z ≠ 1/((m : ℝ)+1) := by
      intro hzval
      apply hneq
      rw [hzval]
      field_simp
      ring
    rcases lt_or_gt_of_ne hunif with hl | hv
    · have hk := light_entropy_index hm ⟨hz.1.le,hl⟩ hbranch
      left
      unfold LightCandidateForm
      rw [hk]
      exact ⟨z,hm,hzc,e.trans ⟨Fin.val,Fin.val_injective⟩,⟨hz.1.le,hl⟩,hbranch,hext⟩
    · have hk := heavy_entropy_index hm ⟨hv,hz.2⟩ hbranch
      have hmM : m ≤ candidateCutoff t h := by
        by_contra hnot
        have hMN : candidateCutoff t h+1 ≤ N := by
          have hc := Fintype.card_le_of_injective e e.injective
          simp only [Fintype.card_fin] at hc
          omega
        let M := candidateCutoff t h
        let q : ProbabilityVector (Fin N) := zeroExtend (Fin.castLEEmb hMN)
          (candidateVector M (heavyRoot h M) (lt_of_lt_of_le (entropySupportIndex_pos hh.le)
            (index_le_candidateCutoff t h))
            ⟨(heavy_parameters_pos hh (heavy_domain_of_index (index_le_candidateCutoff t h))).2.1.le.trans
              (heavy_parameters_pos hh (heavy_domain_of_index (index_le_candidateCutoff t h))).2.2.1.le,
              (heavyRoot_spec hh (heavy_domain_of_index (index_le_candidateCutoff t h))).1.2.le⟩)
        have hq : q ∈ Feasible h := by
          simp only [q,Feasible,Set.mem_ofPred_eq,entropy_zeroExtend,entropy_candidateVector]
          rw [(heavyRoot_spec hh (heavy_domain_of_index (index_le_candidateCutoff t h))).2]
        have hle := hmax q hq
        simp only [q,hrep,objective_zeroExtend,objective_candidateVector] at hle
        have hlt := branchObjective_lt_at_cutoff hh t ht
          (heavy_domain_of_index (index_le_candidateCutoff t h))
          (sample_entropy_le_candidateCutoff t h) (Nat.cast_lt.mpr (lt_of_not_ge hnot))
        rw [heavyRoot_eq_of_spec hh (heavy_domain_of_index hk) ⟨hv,hz.2⟩ hbranch] at hlt
        exact (not_lt_of_ge hle) hlt
      exact Or.inr ⟨m,z,hm,hzc,e.trans ⟨Fin.val,Fin.val_injective⟩,hk,hmM,⟨hv,hz.2⟩,hbranch,hext⟩

/-- On full support the exceptional-vector parametrization uses all available symbols;
uniform laws are its meeting point. -/
theorem candidate_form_fullSupport {m t : ℕ} (hm : 0 < m) (p : ProbabilityVector (Fin (m+1)))
    {h : ℝ} (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hpos : ∀ i, 0 < p.coord i) :
    ∃ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (e : Fin (m+1) ↪ Fin (m+1)),
      p = zeroExtend e (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩) := by
  classical
  by_cases hu : p.UniformOnSupport
  · let z := p.coord 0
    have hc (i : Fin (m+1)) : p.coord i = z := hu i 0 (hpos i) (hpos 0)
    have hsum : ((m : ℝ)+1)*z = 1 := by
      have he := p.tsum_coord
      rw [tsum_fintype] at he
      simp only [hc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at he
      exact he
    have hz0 : 0 < z := hpos 0
    have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have hz1 : z < 1 := by nlinarith
    have hq : (1-z)/(m : ℝ) = z := by
      apply (div_eq_iff hmreal.ne').mpr
      nlinarith
    refine ⟨z,⟨hz0,hz1⟩,Function.Embedding.refl _,?_⟩
    apply Subtype.ext
    apply lp.ext
    funext i
    change p.coord i = (zeroExtend (Function.Embedding.refl _) (candidateVector m z hm _)).coord i
    rw [show i = (Function.Embedding.refl (Fin (m+1))) i by rfl,coord_zeroExtend_apply]
    change p.coord i = candidateCoord m z i
    rw [hc]
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hq.symm
  · obtain ⟨n,z,hn,hz,e,_,hrep⟩ := p.exceptional_form_of_localMax ht hp hu
    have hsurj : Function.Surjective e := by
      intro i
      by_contra hnot
      have hzero : p.coord i = 0 := by
        rw [hrep]
        exact coord_zeroExtend_of_not_mem_range _ _ _ hnot
      exact (hpos i).ne' hzero
    have hcard := Fintype.card_congr (Equiv.ofBijective e ⟨e.injective,hsurj⟩)
    simp only [Fintype.card_fin] at hcard
    have hnm : n = m := by omega
    subst n
    exact ⟨z,hz,e,hrep⟩

/-- The unsaturated candidates use precisely the feasible interior roots of the
nonzero Appendix C polynomial, rather than an assumed stationarity condition. -/
theorem finite_candidate_complete_slack {m t : ℕ} (hm : 0 < m) (p : ProbabilityVector (Fin (m+1)))
    {h : ℝ} (ht : 1 ≤ t) (hp : LocalMaximizer t h p) (hslack : p.entropy < ENNReal.ofReal h) :
    ∃ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) (e : Fin (m+1) ↪ Fin (m+1)),
      z ∈ finiteStationaryRoots m t h ∧
      p = zeroExtend e (candidateVector m z hm ⟨hz.1.le,hz.2.le⟩) := by
  obtain ⟨z,hz,e,hrep⟩ := p.candidate_form_fullSupport hm ht hp
    (p.coord_pos_of_entropy_slack ht hp hslack)
  have hbranch : branchEntropy m z ≤ h := by
    have he : ENNReal.ofReal (branchEntropy m z) < ENNReal.ofReal h := by
      simpa only [hrep,entropy_zeroExtend,entropy_candidateVector] using hslack
    have hh : 0 < h := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hslack)
    exact ((ENNReal.ofReal_lt_ofReal_iff hh).mp he).le
  have hder := p.deriv_eq_of_entropy_slack ht hp hslack (e 0) (e (Fin.succ ⟨0,hm⟩))
  simp only [hrep,coord_zeroExtend_apply,coord_candidateVector,candidateCoord_zero,candidateCoord_succ] at hder
  exact ⟨z,hz,e,(mem_finiteStationaryRoots hm ht h z).mpr ⟨hz,hbranch,hder⟩,hrep⟩

end ProbabilityVector
end
end EntropyConstrainedMissingMass
