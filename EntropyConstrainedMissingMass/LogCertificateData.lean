import EntropyConstrainedMissingMass.LogCertificates

namespace EntropyConstrainedMissingMass
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem log_two_certificate :
    (69314718055994530941723212145817656807 : ℝ)/10^38 ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718055994530941723212145817656808 : ℝ)/10^38 := by
  have h := log_certificate_normalized (y := 2) (by norm_num) 40
  constructor
  · apply le_trans ?_ h.1
    norm_num [logSeries, Finset.sum_range_succ]
  · apply le_trans h.2
    norm_num [logSeries, logRemainder, Finset.sum_range_succ]

end
end EntropyConstrainedMissingMass
