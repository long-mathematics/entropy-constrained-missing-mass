import EntropyConstrainedMissingMass.FiniteClassification
import EntropyConstrainedMissingMass.LogCertificates

/-! From certified entropy signs to the actual canonical roots and support index. -/
open Set
namespace EntropyConstrainedMissingMass
noncomputable section

theorem entropySupportIndex_eq_of_log_bounds {h : ℝ} {k : ℕ} (hk : 0 < k)
    (hl : Real.log k ≤ h) (hu : h < Real.log (k+1 : ℕ)) : entropySupportIndex h = k := by
  apply (Nat.floor_eq_iff (Real.exp_pos h).le).mpr
  constructor
  · exact (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hk)).mp hl
  · have hh := (Real.lt_log_iff_exp_lt (show (0 : ℝ) < (k+1 : ℕ) by positivity)).mp hu
    simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem heavyRoot_mem_of_entropy_signs {h a b : ℝ} {m : ℕ}
    (hh : 0 < h) (hm : entropySupportIndex h ≤ m)
    (ha : a ∈ Icc (1/((m : ℝ)+1)) 1) (hb : b ∈ Icc (1/((m : ℝ)+1)) 1)
    (hea : h < branchEntropy m a) (heb : branchEntropy m b < h) :
    heavyRoot h m ∈ Ioo a b := by
  have hmp : 0 < (m : ℝ) := Nat.cast_pos.mpr ((entropySupportIndex_pos hh.le).trans_le hm)
  have hs := heavyRoot_spec hh (heavy_domain_of_index hm)
  have hmono := (strictAntiOn_branchEntropy hmp).antitoneOn
  have hroot : heavyRoot h m ∈ Icc (1/((m : ℝ)+1)) 1 := ⟨hs.1.1.le,hs.1.2.le⟩
  constructor
  · by_contra hn
    have he := hmono hroot ha (le_of_not_gt hn)
    rw [hs.2] at he
    linarith
  · by_contra hn
    have he := hmono hb hroot (le_of_not_gt hn)
    rw [hs.2] at he
    linarith

theorem lightRoot_mem_of_entropy_signs {h a b : ℝ}
    (hh : 0 < h)
    (ha : a ∈ Icc 0 (1/((entropySupportIndex h : ℝ)+1)))
    (hb : b ∈ Icc 0 (1/((entropySupportIndex h : ℝ)+1)))
    (hea : branchEntropy (entropySupportIndex h) a < h)
    (heb : h < branchEntropy (entropySupportIndex h) b) : lightRoot h ∈ Ioo a b := by
  have hs := lightRoot_spec hh
  have hmono := (strictMonoOn_branchEntropy (Nat.cast_pos.mpr (entropySupportIndex_pos hh.le))).monotoneOn
  have hr : lightRoot h ∈ Icc 0 (1/((entropySupportIndex h : ℝ)+1)) := ⟨hs.1.1,hs.1.2.le⟩
  constructor
  · by_contra hn
    have he := hmono hr ha (le_of_not_gt hn)
    rw [hs.2] at he
    linarith
  · by_contra hn
    have he := hmono hb hr (le_of_not_gt hn)
    rw [hs.2] at he
    linarith

end
end EntropyConstrainedMissingMass
