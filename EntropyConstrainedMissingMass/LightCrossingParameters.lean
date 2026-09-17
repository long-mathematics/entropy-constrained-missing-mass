import EntropyConstrainedMissingMass.FiniteClassification
import EntropyConstrainedMissingMass.HeavyCrossing

/-! Ordering of the light and heavy candidate atom sizes. -/
namespace EntropyConstrainedMissingMass
noncomputable section
open Set

def lightRepeated (h : ℝ) : ℝ := (1 - lightRoot h) / (entropySupportIndex h : ℝ)

theorem light_parameters {h : ℝ} (hh : 0 < h) :
    0 ≤ lightRoot h ∧ lightRoot h < lightRepeated h ∧
      1 / ((entropySupportIndex h : ℝ) + 1) < lightRepeated h ∧ lightRepeated h < 1 := by
  have hk : 0 < entropySupportIndex h := entropySupportIndex_pos hh.le
  have hkr : 0 < (entropySupportIndex h : ℝ) := Nat.cast_pos.mpr hk
  have hs := lightRoot_spec hh
  have ha0 := hs.1.1
  have ha1 : lightRoot h < 1 := hs.1.2.trans_le ((div_le_one (by positivity)).mpr (by linarith))
  have ha := (lt_div_iff₀ (by positivity : (0 : ℝ) < (entropySupportIndex h : ℝ) + 1)).mp hs.1.2
  have hy : lightRoot h < lightRepeated h := by
    apply (lt_div_iff₀ hkr).mpr
    nlinarith
  have hyt : 1 / ((entropySupportIndex h : ℝ) + 1) < lightRepeated h := by
    apply (div_lt_div_iff₀ (by positivity) hkr).mpr
    nlinarith
  refine ⟨ha0, hy, hyt, ?_⟩
  by_cases hk1 : entropySupportIndex h = 1
  · have haz : lightRoot h ≠ 0 := by
      intro he
      have h := hs.2
      rw [he, branchEntropy_zero, hk1] at h
      norm_num at h
      linarith
    dsimp [lightRepeated]
    rw [hk1]
    norm_num
    exact lt_of_le_of_ne ha0 (Ne.symm haz)
  · have hk2 : 2 ≤ entropySupportIndex h := by omega
    have hk2r : (2 : ℝ) ≤ entropySupportIndex h := by exact_mod_cast hk2
    apply (div_lt_one hkr).mpr
    linarith

theorem branchEntropy_eq_negMulLog_pair {m : ℝ} (hm : m ≠ 0) (z : ℝ) :
    branchEntropy m z = Real.negMulLog z + m * Real.negMulLog ((1 - z) / m) := by
  unfold branchEntropy Real.negMulLog
  field_simp
  ring

theorem branchEntropy_mono_m {m n z : ℝ} (hm : 0 < m) (hmn : m ≤ n) (hz : z ≤ 1) :
    branchEntropy m z ≤ branchEntropy n z := by
  rw [branchEntropy_eq_negMulLog hm.ne', branchEntropy_eq_negMulLog (hm.trans_le hmn).ne']
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.log_le_log hm hmn) (sub_nonneg.mpr hz))

theorem branchEntropy_strictMono_m {m n z : ℝ} (hm : 0 < m) (hmn : m < n) (hz : z < 1) :
    branchEntropy m z < branchEntropy n z := by
  rw [branchEntropy_eq_negMulLog hm.ne', branchEntropy_eq_negMulLog (hm.trans hmn).ne']
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_left (Real.log_lt_log hm hmn) (sub_pos.mpr hz))

/-- Averaging the remaining light masses strictly increases entropy when `k≥2`.
The proof is the strict two-point concavity inequality with weights `1/k` and `(k-1)/k`. -/
theorem light_entropy_at_repeated_strict {h : ℝ} (hh : 0 < h)
    (hk2 : 2 ≤ entropySupportIndex h) :
    h < branchEntropy (entropySupportIndex h) (lightRepeated h) := by
  let k : ℝ := entropySupportIndex h
  let a := lightRoot h
  let y := lightRepeated h
  have hk : 0 < k := by dsimp [k]; exact Nat.cast_pos.mpr (entropySupportIndex_pos hh.le)
  have hk2r : 2 ≤ k := by dsimp [k]; exact_mod_cast hk2
  obtain ⟨ha, hay, _, hy1⟩ := light_parameters hh
  have hy : 0 ≤ y := le_trans ha hay.le
  have hsum : a + k * y = 1 := by
    dsimp [a, k, y, lightRepeated]
    field_simp
    ring
  have hmix := Real.strictConcaveOn_negMulLog.2 ha hy hay.ne
    (show 0 < 1 / k by positivity) (show 0 < (k - 1) / k from div_pos (by linarith) hk)
    (by field_simp; ring)
  simp only [smul_eq_mul] at hmix
  have he : 1 / k * a + (k - 1) / k * y = (1 - y) / k := by
    field_simp
    nlinarith [hsum]
  rw [he] at hmix
  have heh : Real.negMulLog a + k * Real.negMulLog y = h := by
    have he := (lightRoot_spec hh).2
    rw [branchEntropy_eq_negMulLog_pair hk.ne'] at he
    exact he
  rw [branchEntropy_eq_negMulLog_pair hk.ne']
  have hh' := (mul_lt_mul_of_pos_left hmix hk)
  have hw1 : k * (1 / k) = 1 := by field_simp
  have hw2 : k * ((k - 1) / k) = k - 1 := by field_simp
  rw [mul_add, ← mul_assoc, ← mul_assoc, hw1, hw2, one_mul] at hh'
  dsimp [y, k] at *
  nlinarith

theorem light_entropy_at_repeated_lt_heavy {h : ℝ} {m : ℕ} (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    h < branchEntropy m (lightRepeated h) := by
  have hk := entropySupportIndex_pos hh.le
  have hm' : (entropySupportIndex h : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hy1 := (light_parameters hh).2.2.2
  by_cases hk2 : 2 ≤ entropySupportIndex h
  · exact (light_entropy_at_repeated_strict hh hk2).trans_le
      (branchEntropy_mono_m (Nat.cast_pos.mpr hk) hm' hy1.le)
  · have hk1 : entropySupportIndex h = 1 := by omega
    have he : branchEntropy 1 (lightRepeated h) = h := by
      have hh' := (lightRoot_spec hh).2
      rw [hk1] at hh'
      simpa [lightRepeated, hk1, binary_branchEntropy_symmetry] using hh'
    exact he.symm.trans_lt (branchEntropy_strictMono_m (m := 1) (n := (m : ℝ))
      (by norm_num) (by exact_mod_cast (show 1 < m by omega)) hy1)

/-- The strict mass ordering needed by the light-heavy crossing theorem.
The only omitted heavy multiplicity is the binary duplicate `m=1`. -/
theorem light_heavy_mass_order {h : ℝ} {m : ℕ} (hh : 0 < h)
    (hm : entropySupportIndex h ≤ m) (hm2 : 2 ≤ m) :
    heavyLight h m < lightRepeated h ∧ lightRepeated h < heavyRoot h m := by
  have hdom := heavy_domain_of_index hm
  obtain ⟨hm0, hq, hqz, hz1, _⟩ := heavy_parameters_pos hh hdom
  obtain ⟨_, _, hyt, hy1⟩ := light_parameters hh
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hnorm : heavyRoot h m + (m : ℝ) * heavyLight h m = 1 := by
    dsimp [heavyLight]
    field_simp
    ring
  have hqt : heavyLight h m < 1 / ((m : ℝ) + 1) := by
    apply (lt_div_iff₀ hm1).mpr
    nlinarith
  have htm : 1 / ((m : ℝ) + 1) ≤ 1 / ((entropySupportIndex h : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hm 1
  refine ⟨hqt.trans_le htm |>.trans hyt, ?_⟩
  by_contra hzy
  have hzy' : heavyRoot h m ≤ lightRepeated h := le_of_not_gt hzy
  have hle := (strictAntiOn_branchEntropy hm0).antitoneOn
    ⟨(heavyRoot_spec hh hdom).1.1.le, hz1.le⟩ ⟨htm.trans hyt.le, hy1.le⟩ hzy'
  rw [(heavyRoot_spec hh hdom).2] at hle
  exact not_lt_of_ge hle (light_entropy_at_repeated_lt_heavy hh hm hm2)

end
end EntropyConstrainedMissingMass
