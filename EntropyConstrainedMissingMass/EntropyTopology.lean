import EntropyConstrainedMissingMass.Probability
import Mathlib.Topology.Semicontinuity.Basic

/-! Lower semicontinuity of extended entropy and closedness of entropy constraints. -/

namespace EntropyConstrainedMissingMass.ProbabilityVector
variable {ι : Type*}

theorem continuous_coord (i : ι) : Continuous (fun p : ProbabilityVector ι => p.coord i) :=
  ((lp.evalCLM ℝ (fun _ : ι => ℝ) 1 i).continuous).comp continuous_subtype_val

/-- Entropy is lower semicontinuous even in the coordinatewise topology on all real vectors. -/
theorem lowerSemicontinuous_entropy_function :
    LowerSemicontinuous (fun p : ι → ℝ => ∑' i, ENNReal.ofReal (Real.negMulLog (p i))) := by
  apply lowerSemicontinuous_tsum
  intro i
  exact (ENNReal.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp (continuous_apply i))).lowerSemicontinuous

/-- In particular extended entropy is lower semicontinuous in the manuscript's ℓ¹ topology. -/
theorem lowerSemicontinuous_entropy :
    LowerSemicontinuous (fun p : ProbabilityVector ι => p.entropy) := by
  apply lowerSemicontinuous_tsum
  intro i
  exact (ENNReal.continuous_ofReal.comp
    (Real.continuous_negMulLog.comp (continuous_coord i))).lowerSemicontinuous

theorem isClosed_feasible (h : ℝ) : IsClosed (Feasible h : Set (ProbabilityVector ι)) :=
  lowerSemicontinuous_entropy.isClosed_preimage (ENNReal.ofReal h)

end EntropyConstrainedMissingMass.ProbabilityVector
