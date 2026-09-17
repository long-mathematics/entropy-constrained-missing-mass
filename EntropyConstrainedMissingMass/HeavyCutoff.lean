import EntropyConstrainedMissingMass.HeavyInterpolation
import EntropyConstrainedMissingMass.CertificateBounds

/-! The real-exponent heavy-tail cutoff. -/

open Set
namespace EntropyConstrainedMissingMass
noncomputable section

private def cutoffAux (s z u : ℝ) : ℝ := realMissingMassDeriv s u -
  s*u*(Real.log z-Real.log u)*(1-u)^(s-1)

private theorem hasDerivAt_cutoffAux (s z : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt (cutoffAux s z)
      (s*(1+Real.log z-Real.log u)*(1-u)^(s-2)*(s*u-1)) u := by
  have hp := ((hasDerivAt_id u).const_sub 1).rpow_const (p := s-1)
    (Or.inl (sub_pos.mpr hu1).ne')
  have hl := (Real.hasDerivAt_log hu.ne').const_sub (Real.log z)
  have hd := (hp.mul (((hasDerivAt_id u).const_mul (s+1)).const_sub 1)).sub
    ((((hasDerivAt_id u).const_mul s).mul hl).mul hp)
  convert hd using 1
  · rfl
  · simp only [id_eq, Pi.mul_apply]
    have he : (1-u)^(s-1) = (1-u)^(s-2)*(1-u) := by
      convert Real.rpow_add_one (sub_pos.mpr hu1).ne' (s-2) using 1
      congr 1
      ring
    rw [show s-1-1 = s-2 by ring, he]
    field_simp [hu.ne']
    ring

private theorem heavyPsi_neg_of_small {s z q : ℝ} (hs : 1 ≤ s)
    (hq : 0 < q) (hqz : q < z) (hz1 : z < 1) (hz : z ≤ 1/s) : heavyPsi s z q < 0 := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hz0 : 0 < z := hq.trans hqz
  have ha : StrictAntiOn (cutoffAux s z) (Icc q z) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) _
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hasDerivAt_cutoffAux s z (hq.trans hu.1) (hu.2.trans hz1)).deriv]
      have hlog : 0 < Real.log z - Real.log u := sub_pos.mpr
        (Real.strictMonoOn_log (hq.trans hu.1) hz0 hu.2)
      have hsu : s*u < 1 := by
        have hsz := (le_div_iff₀ hs0).mp hz
        nlinarith [mul_lt_mul_of_pos_left hu.2 hs0]
      exact mul_neg_of_pos_of_neg
        (mul_pos (mul_pos hs0 (by linarith)) (Real.rpow_pos_of_pos (sub_pos.mpr (hu.2.trans hz1)) _))
        (by linarith)
    · intro u hu
      exact (hasDerivAt_cutoffAux s z (hq.trans_le hu.1) (hu.2.trans_lt hz1)).continuousAt.continuousWithinAt
  have he := ha ⟨le_refl q,hqz.le⟩ ⟨hqz.le,le_refl z⟩ hqz
  unfold cutoffAux at he
  simp only [sub_self, mul_zero, zero_mul, sub_zero] at he
  unfold heavyPsi
  rw [Real.log_div hz0.ne' hq.ne']
  linarith

/-- The sign expression is strictly negative beyond the manuscript cutoff. -/
theorem heavyPsi_neg_of_cutoff {h m s : ℝ} (hh : 0 < h)
    (hm : Real.exp h - 1 < m) (hs : 1 ≤ s) (hcut : s*h+1 ≤ m) :
    heavyPsi s (heavyRoot h m) (heavyLight h m) < 0 := by
  obtain ⟨hm0,hq,hqz,hz1,hsig⟩ := heavy_parameters_pos hh hm
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hz0 : 0 < heavyRoot h m := hq.trans hqz
  by_cases hz : heavyRoot h m ≤ 1/s
  · exact heavyPsi_neg_of_small hs hq hqz hz1 hz
  · have hsz : 1 < s * heavyRoot h m := by
      have := (div_lt_iff₀ hs0).mp (lt_of_not_ge hz)
      nlinarith
    have hD : realMissingMassDeriv s (heavyRoot h m) < 0 := by
      unfold realMissingMassDeriv
      exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (sub_pos.mpr hz1) _)
        (by nlinarith)
    have hH : (1-heavyRoot h m)*(1+heavySigma h m) < h := by
      have he := heavy_entropy_sigma hh hm
      have hl := Real.log_lt_sub_one_of_pos hz0 hz1.ne
      nlinarith only [he,hl]
    have hmq : m * heavyLight h m = 1-heavyRoot h m := by
      unfold heavyLight
      field_simp
    have hb : 0 < 1-heavyLight h m-s*heavyLight h m*(1+heavySigma h m) := by
      have hlt := mul_lt_mul_of_pos_left hH hs0
      have he : m*(heavyLight h m+s*heavyLight h m*(1+heavySigma h m)) =
          (1-heavyRoot h m) + s*((1-heavyRoot h m)*(1+heavySigma h m)) := by
        rw [show m*(heavyLight h m+s*heavyLight h m*(1+heavySigma h m)) =
          m*heavyLight h m+s*(m*heavyLight h m)*(1+heavySigma h m) by ring, hmq]
        ring
      nlinarith only [hlt,he,hcut,hm0,hz0]
    have hpow : 0 < (1-heavyLight h m)^(s-1) :=
      Real.rpow_pos_of_pos (sub_pos.mpr (hqz.trans hz1)) _
    have he : heavyPsi s (heavyRoot h m) (heavyLight h m) =
        realMissingMassDeriv s (heavyRoot h m) - (1-heavyLight h m)^(s-1)*
          (1-heavyLight h m-s*heavyLight h m*(1+heavySigma h m)) := by
      unfold heavyPsi realMissingMassDeriv heavySigma
      ring
    rw [he]
    exact sub_neg.mpr (hD.trans (mul_pos hpow hb))

/-- Manuscript `lem:cutoff`: the genuine real-parameter derivative is negative
for every real sample exponent `s ≥ 1` once `m ≥ s*h+1`. -/
theorem heavy_cutoff {h m s : ℝ} (hh : 0 < h) (hm : Real.exp h - 1 < m)
    (hs : 1 ≤ s) (hcut : s*h+1 ≤ m) : deriv (heavyValue h s) m < 0 := by
  rw [(hasDerivAt_heavyValue hh hm s).deriv]
  obtain ⟨_,hq,_,_,hsig⟩ := heavy_parameters_pos hh hm
  exact mul_neg_of_pos_of_neg (div_pos hq hsig) (heavyPsi_neg_of_cutoff hh hm hs hcut)

/-- The heavy value is strictly decreasing on the entire cutoff tail. -/
theorem strictAntiOn_heavyValue {h s M : ℝ} (hh : 0 < h) (hs : 1 ≤ s)
    (hM : Real.exp h-1 < M) (hcut : s*h+1 ≤ M) :
    StrictAntiOn (heavyValue h s) (Ici M) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) _
  · intro m hm
    rw [interior_Ici] at hm
    exact heavy_cutoff hh (hM.trans hm) hs (hcut.trans hm.le)
  · intro m hm
    exact (hasDerivAt_heavyValue hh (hM.trans_le hm) s).continuousAt.continuousWithinAt

/-- Natural exponents recover exactly the branch objective used for candidates. -/
theorem heavyValue_nat_eq_branchObjective {h m : ℝ} (hh : 0 < h)
    (hm : Real.exp h-1 < m) (t : ℕ) :
    heavyValue h (t : ℝ) m = branchObjective m t (heavyRoot h m) := by
  obtain ⟨hm0,_,_,_,_⟩ := heavy_parameters_pos hh hm
  simp only [heavyValue, realMissingMassTerm, Real.rpow_natCast, heavyLight, branchObjective]
  field_simp

/-- Every multiplicity strictly above a valid cutoff is strictly worse than its
cutoff endpoint, including comparison of the integer candidate formulas. -/
theorem branchObjective_lt_at_cutoff {h M j : ℝ} (hh : 0 < h) (t : ℕ)
    (ht : 1 ≤ t) (hM : Real.exp h-1 < M) (hcut : (t : ℝ)*h+1 ≤ M) (hj : M < j) :
    branchObjective j t (heavyRoot h j) < branchObjective M t (heavyRoot h M) := by
  rw [← heavyValue_nat_eq_branchObjective hh (hM.trans hj) t,
    ← heavyValue_nat_eq_branchObjective hh hM t]
  exact strictAntiOn_heavyValue hh (by exact_mod_cast ht) hM hcut
    (show M ∈ Ici M from le_refl M) (show j ∈ Ici M from hj.le) hj

end
end EntropyConstrainedMissingMass
