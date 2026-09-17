import EntropyConstrainedMissingMass.CurvatureIntegrals

/-! The arithmetic-geometric-mean comparison supplying S I₁ ≥ 3/2. -/

open MeasureTheory Set
namespace EntropyConstrainedMissingMass.Curvature

private theorem triple_amgm_of_min {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hxz : x ≤ z) :
    27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
  have hu : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hv : 0 ≤ z - x := sub_nonneg.mpr hxz
  have hA : 0 ≤ 9 * x * ((y - z) ^ 2 + (y - x) * (z - x)) := by positivity
  have hB : 0 ≤ ((y - x) + (z - x)) ^ 3 := by positivity
  nlinarith only [hA, hB]

/-- Elementary cubic AM-GM without real powers or distinct-coordinate assumptions. -/
theorem triple_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ ((x + y + z) / 3) ^ 3 := by
  have h : 27 * (x * y * z) ≤ (x + y + z) ^ 3 := by
    by_cases hxy : x ≤ y
    · by_cases hxz : x ≤ z
      · exact triple_amgm_of_min hx hxy hxz
      · have h := triple_amgm_of_min hz (le_of_not_ge hxz) ((le_of_not_ge hxz).trans hxy)
        nlinarith only [h]
    · by_cases hyz : y ≤ z
      · have h := triple_amgm_of_min hy (le_of_not_ge hxy) hyz
        nlinarith only [h]
      · have h := triple_amgm_of_min hz ((le_of_not_ge hyz).trans (le_of_not_ge hxy))
          (le_of_not_ge hyz)
        nlinarith only [h]
  nlinarith only [h]

theorem D_le_mean_cube (x y z s : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : 0 ≤ s) : D x y z s ≤ (s + (x + y + z) / 3) ^ 3 := by
  have h := triple_amgm (s + x) (s + y) (s + z) (by linarith) (by linarith) (by linarith)
  have heq : (s + x + (s + y) + (s + z)) / 3 = s + (x + y + z) / 3 := by ring
  simpa only [heq, D] using h

/-- Integrating the denominator comparison gives the lower bound used in Appendix A. -/
theorem I1_ge_recip_mean (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / (2 * (x + y + z)) ≤ I1 x y z := by
  let c := (x + y + z) / 3
  have hc : 0 < c := by dsimp [c]; positivity
  have h := setIntegral_mono_on (integrableOn_I1 c c c hc hc hc)
    (integrableOn_I1 x y z hx hy hz) measurableSet_Ioi (fun s hs => ?_)
  · change I1 c c c ≤ I1 x y z at h
    rw [I1_uniform c hc] at h
    have heq : 1 / (2 * c) = 3 / (2 * (x + y + z)) := by dsimp [c]; field_simp
    simpa only [heq] using h
  · rw [D_uniform]
    exact div_le_div_of_nonneg_left (le_of_lt hs) (D_pos x y z hx hy hz s (le_of_lt hs))
      (D_le_mean_cube x y z s hx hy hz (le_of_lt hs))

theorem sum_mul_I1_ge (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 / 2 ≤ (x + y + z) * I1 x y z := by
  have h := I1_ge_recip_mean x y z hx hy hz
  have hS : 0 < x + y + z := by positivity
  have hm := mul_le_mul_of_nonneg_left h hS.le
  have heq : (x + y + z) * (3 / (2 * (x + y + z))) = 3 / 2 := by field_simp
  rw [heq] at hm
  exact hm

end EntropyConstrainedMissingMass.Curvature
