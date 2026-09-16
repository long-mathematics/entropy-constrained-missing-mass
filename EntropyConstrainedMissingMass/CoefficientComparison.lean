import EntropyConstrainedMissingMass.CoefficientExtremum
import EntropyConstrainedMissingMass.CoefficientPartialFractions

/-! The coefficient comparison of §3, with coefficients represented by finite convolutions. -/

namespace EntropyConstrainedMissingMass

def previousWeightedCoefficient (α x y z : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => weightedCoefficient α x y z n

/-- Coefficients of `(1-αw)(1-βw)G`. -/
def comparisonAuxCoefficient (α β x y z : ℝ) (n : ℕ) : ℝ :=
  weightedCoefficient α x y z n - β * previousWeightedCoefficient α x y z n

@[simp] theorem comparisonAuxCoefficient_zero (α β x y z : ℝ) :
    comparisonAuxCoefficient α β x y z 0 = 1 := by
  simp [comparisonAuxCoefficient, previousWeightedCoefficient]

theorem comparisonAuxCoefficient_swap (α β x y z : ℝ) (n : ℕ) :
    comparisonAuxCoefficient α β x y z n = comparisonAuxCoefficient β α x y z n := by
  cases n with
  | zero => simp
  | succ n =>
    cases n <;> simp [comparisonAuxCoefficient, previousWeightedCoefficient,
      weightedCoefficient, previousHomogeneous3, homogeneous3, homogeneous2] <;> ring

/-- The coefficient at index `n-1` in the product of the auxiliary series and `(1-βw)G`;
at `n=0` the negative-index coefficient is zero. -/
def comparisonCoefficient (α β x y z : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n,
    comparisonAuxCoefficient α β x y z j * weightedCoefficient β x y z (n - 1 - j)

theorem homogeneous2_scale (c x y : ℝ) (n : ℕ) :
    homogeneous2 (c * x) (c * y) n = c ^ n * homogeneous2 x y n := by
  induction n with
  | zero => simp [homogeneous2]
  | succ n ih =>
    rw [homogeneous2, homogeneous2, ih, mul_pow, pow_succ c n]
    ring

theorem homogeneous3_scale (c x y z : ℝ) (n : ℕ) :
    homogeneous3 (c * x) (c * y) (c * z) n = c ^ n * homogeneous3 x y z n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [homogeneous3, homogeneous3, homogeneous2_scale, ih, pow_succ c n]
    ring

theorem weightedCoefficient_scale (β x y z : ℝ) (n : ℕ) :
    weightedCoefficient β (β * x) (β * y) (β * z) n =
      β ^ n * coefficientDifference x y z n := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [weightedCoefficient, previousHomogeneous3, homogeneous3_scale,
      coefficientDifference, pow_succ]
    ring

theorem weightedCoefficient_bound {β x y z : ℝ} (hβ : 0 < β)
    (hx : 0 ≤ x) (hxβ : x < β) (hy : 0 ≤ y) (hyβ : y < β)
    (hz : 0 ≤ z) (hzβ : z < β) (n : ℕ) :
    weightedCoefficient β x y z n ≤
      max 1 (β / (3 * β - x - y - z)) * β ^ n := by
  have hden : 0 < 3 * β - x - y - z := by linarith
  have hsig : 0 < 3 - x / β - y / β - z / β := by
    have heq : 3 - x / β - y / β - z / β = (3 * β - x - y - z) / β := by
      field_simp
    rw [heq]
    exact div_pos hden hβ
  have heq : (3 - x / β - y / β - z / β)⁻¹ = β / (3 * β - x - y - z) := by
    field_simp
  have he := coefficient_extremum (div_nonneg hx hβ.le) ((div_le_one hβ).2 hxβ.le)
    (div_nonneg hy hβ.le) ((div_le_one hβ).2 hyβ.le)
    (div_nonneg hz hβ.le) ((div_le_one hβ).2 hzβ.le) hsig n
  rw [heq] at he
  have hs := weightedCoefficient_scale β (x / β) (y / β) (z / β) n
  simp only [mul_div_cancel₀ _ (ne_of_gt hβ)] at hs
  rw [hs]
  exact (mul_le_mul_of_nonneg_left he (pow_nonneg hβ.le n)).trans_eq (mul_comm _ _)

/-- The finite convolution against a geometric progression telescopes exactly. -/
theorem comparisonAuxCoefficient_telescoping (α β x y z : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), comparisonAuxCoefficient α β x y z j * β ^ (n - j)) =
      weightedCoefficient α x y z n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    have hsum : (∑ j ∈ Finset.range (n + 1),
        comparisonAuxCoefficient α β x y z j * β ^ (n + 1 - j)) =
        (∑ j ∈ Finset.range (n + 1),
          comparisonAuxCoefficient α β x y z j * β ^ (n - j)) * β := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have he : n + 1 - j = (n - j) + 1 := by have := Finset.mem_range.mp hj; omega
      rw [he, pow_succ]
      ring
    rw [hsum, ih]
    simp only [comparisonAuxCoefficient, previousWeightedCoefficient]
    ring

theorem weightedCoefficient_prev_pos {β x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) {n : ℕ}
    (hpos : 0 < weightedCoefficient β x y z (n + 1)) :
    0 < weightedCoefficient β x y z n := by
  cases n with
  | zero => simp
  | succ n =>
    have hp0 := homogeneous3_pos hx.le hy.le hz n
    have hp1 := homogeneous3_pos hx.le hy.le hz (n + 1)
    have hturan := homogeneous3_log_concave hx.le hy.le hz.le n
    simp only [weightedCoefficient, previousHomogeneous3] at hpos ⊢
    by_contra hn
    have hle := le_of_not_gt hn
    have hm1 := mul_pos hp0 hpos
    have hm2 := mul_nonpos_of_nonneg_of_nonpos hp1.le hle
    nlinarith

theorem weightedCoefficient_pos_of_le {β x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) {N : ℕ}
    (hpos : 0 < weightedCoefficient β x y z N) {j : ℕ} (hj : j ≤ N) :
    0 < weightedCoefficient β x y z j := by
  induction N with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    simp
  | succ N ih =>
    by_cases heq : j = N + 1
    · simpa [heq] using hpos
    · exact ih (weightedCoefficient_prev_pos hx hy hz hpos) (by omega)

theorem weightedCoefficient_pos_of_comparison {α β x y z : ℝ}
    (hα : 0 < α) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (n : ℕ)
    (hk : 0 < weightedCoefficient α x y z n)
    (hstep : β * weightedCoefficient α x y z n ≤ weightedCoefficient α x y z (n + 1)) :
    0 < weightedCoefficient β x y z (n + 1) := by
  cases n with
  | zero =>
    simp [weightedCoefficient, previousHomogeneous3, homogeneous3, homogeneous2] at hstep ⊢
    linarith
  | succ n =>
    have hp := homogeneous3_pos hx.le hy.le hz (n + 1)
    have ht := homogeneous3_strict_log_concave hx hy hz n
    have heq : weightedCoefficient α x y z (n + 1) * weightedCoefficient β x y z (n + 2) =
        homogeneous3 x y z (n + 1) *
          (weightedCoefficient α x y z (n + 2) - β * weightedCoefficient α x y z (n + 1)) +
        α * (homogeneous3 x y z (n + 1) ^ 2 -
          homogeneous3 x y z n * homogeneous3 x y z (n + 2)) := by
      simp only [weightedCoefficient, previousHomogeneous3]
      ring
    have hprod : 0 < weightedCoefficient α x y z (n + 1) *
        weightedCoefficient β x y z (n + 2) := by
      rw [heq]
      exact add_pos_of_nonneg_of_pos (mul_nonneg hp.le (sub_nonneg.mpr hstep))
        (mul_pos hα (sub_pos.mpr ht))
    exact pos_of_mul_pos_right hprod hk.le

/-- Positive coefficients of `(1-βw)G` satisfy a strict Turán inequality. -/
theorem weightedCoefficient_strict_log_concave {β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (n : ℕ)
    (hpos : 0 < weightedCoefficient β x y z n) :
    weightedCoefficient β x y z n * weightedCoefficient β x y z (n + 2) <
      weightedCoefficient β x y z (n + 1) ^ 2 := by
  have hc := weightedCoefficient_middle_strict_concavity hβx hxy hyz hz n
  have hm := mul_neg_of_pos_of_neg hpos hc
  have hs := sq_nonneg (weightedCoefficient β x y z (n + 1) - y * weightedCoefficient β x y z n)
  nlinarith

theorem comparisonAuxCoefficient_prev_pos {α β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) {n : ℕ}
    (hB0 : 0 < weightedCoefficient β x y z n)
    (hB1 : 0 < weightedCoefficient β x y z (n + 1))
    (ha : 0 ≤ comparisonAuxCoefficient α β x y z (n + 2)) :
    0 < comparisonAuxCoefficient α β x y z (n + 1) := by
  have ht := weightedCoefficient_strict_log_concave hβx hxy hyz hz n hB0
  rw [comparisonAuxCoefficient_swap] at ha ⊢
  simp only [comparisonAuxCoefficient, previousWeightedCoefficient] at ha ⊢
  by_contra hn
  have hm1 := mul_nonneg hB0.le ha
  have hm2 := mul_nonpos_of_nonneg_of_nonpos hB1.le (le_of_not_gt hn)
  nlinarith

theorem comparisonAuxCoefficient_pos_of_le {α β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (N : ℕ)
    (hB : ∀ j ≤ N + 1, 0 < weightedCoefficient β x y z j)
    (ha : 0 ≤ comparisonAuxCoefficient α β x y z (N + 1)) :
    ∀ j ≤ N, 0 < comparisonAuxCoefficient α β x y z j := by
  induction N with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp
  | succ N ih =>
    have hprev : 0 < comparisonAuxCoefficient α β x y z (N + 1) :=
      comparisonAuxCoefficient_prev_pos hβx hxy hyz hz (hB N (by omega))
        (hB (N + 1) (by omega)) ha
    intro j hj
    by_cases heq : j = N + 1
    · simpa [heq] using hprev
    · exact ih (fun k hk => hB k (by omega)) hprev.le j (by omega)

theorem comparisonCoefficient_le_of_aux_nonneg {α β x y z : ℝ} (hβ : 0 < β)
    (hx : 0 ≤ x) (hxβ : x < β) (hy : 0 ≤ y) (hyβ : y < β)
    (hz : 0 ≤ z) (hzβ : z < β) (n : ℕ)
    (ha : ∀ j ≤ n, 0 ≤ comparisonAuxCoefficient α β x y z j) :
    comparisonCoefficient α β x y z (n + 1) ≤
      max 1 (β / (3 * β - x - y - z)) * weightedCoefficient α x y z n := by
  let C := max 1 (β / (3 * β - x - y - z))
  calc
    comparisonCoefficient α β x y z (n + 1) =
        ∑ j ∈ Finset.range (n + 1),
          comparisonAuxCoefficient α β x y z j * weightedCoefficient β x y z (n - j) := by
      simp [comparisonCoefficient]
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        comparisonAuxCoefficient α β x y z j * (C * β ^ (n - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul_of_nonneg_left
        (weightedCoefficient_bound hβ hx hxβ hy hyβ hz hzβ (n - j)) (ha j hjn)
    _ = C * ∑ j ∈ Finset.range (n + 1),
        comparisonAuxCoefficient α β x y z j * β ^ (n - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = C * weightedCoefficient α x y z n := by
      rw [comparisonAuxCoefficient_telescoping]

theorem comparison_bound_constant_identity {β d : ℝ} (hβ : 0 < β) :
    max 1 (β / d) / β = max (1 / β) (1 / d) := by
  rw [← max_div_div_right hβ.le]
  congr 1
  field_simp

/-- The exact strict coefficient comparison, with `J` represented by its finite convolution.
There are no positivity, ratio, or transfer premises beyond the manuscript hypotheses. -/
theorem coefficient_comparison {α β x y z : ℝ}
    (hβx : x < β) (hxy : y < x) (hyz : z < y) (hz : 0 < z) (hα : 0 < α)
    (n : ℕ) (hk : 0 < weightedCoefficient α x y z n)
    (hstep : β * weightedCoefficient α x y z n ≤ weightedCoefficient α x y z (n + 1)) :
    comparisonCoefficient α β x y z n <
      max (1 / β) (1 / (3 * β - x - y - z)) * weightedCoefficient α x y z n := by
  have hy : 0 < y := hz.trans hyz
  have hx : 0 < x := hy.trans hxy
  have hβ : 0 < β := hx.trans hβx
  cases n with
  | zero =>
    simp only [comparisonCoefficient, Finset.range_zero, Finset.sum_empty,
      weightedCoefficient_zero, mul_one]
    exact lt_of_lt_of_le (one_div_pos.mpr hβ) (le_max_left _ _)
  | succ n =>
    have hBtop := weightedCoefficient_pos_of_comparison hα hx hy hz (n + 1) hk hstep
    have hB (j : ℕ) (hj : j ≤ n + 1 + 1) : 0 < weightedCoefficient β x y z j :=
      weightedCoefficient_pos_of_le hx hy hz hBtop hj
    have haTop : 0 ≤ comparisonAuxCoefficient α β x y z (n + 1 + 1) := by
      simpa only [comparisonAuxCoefficient, previousWeightedCoefficient] using sub_nonneg.mpr hstep
    have ha := comparisonAuxCoefficient_pos_of_le hβx hxy hyz hz (n + 1) hB haTop
    have hbound := comparisonCoefficient_le_of_aux_nonneg hβ hx.le hβx hy.le
      (hxy.trans hβx) hz.le (hyz.trans (hxy.trans hβx)) n
      (fun j hj => (ha j (by omega)).le)
    let C := max 1 (β / (3 * β - x - y - z))
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have han := ha (n + 1) le_rfl
    change 0 < weightedCoefficient α x y z (n + 1) - β * weightedCoefficient α x y z n at han
    have hstrict : C * weightedCoefficient α x y z n <
        (C / β) * weightedCoefficient α x y z (n + 1) := by
      calc
        C * weightedCoefficient α x y z n =
            (C / β) * (β * weightedCoefficient α x y z n) := by field_simp
        _ < (C / β) * weightedCoefficient α x y z (n + 1) :=
          mul_lt_mul_of_pos_left (sub_pos.mp han) (div_pos hC hβ)
    have heq : C / β = max (1 / β) (1 / (3 * β - x - y - z)) :=
      comparison_bound_constant_identity hβ
    rw [heq] at hstrict
    exact hbound.trans_lt hstrict

end EntropyConstrainedMissingMass
