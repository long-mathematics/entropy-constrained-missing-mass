# Final formalization audit

The complete 1,350-line manuscript, including all appendices, was independently
reread on 2026-09-16. The rebuilt inventory agrees with all **18 named results**
in [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md). Its **152 obligations**
comprise 18 named results, 49 labelled equation cross-checks, and 85 supporting
obligations. Alternate arguments below replace explicitly identified proof
calculations; those unused calculations are not claimed as separate Lean proofs.

## Statement and representation review

- Probability vectors are genuine ℓ¹ vectors with nonnegative coordinates summing
  to one. Countable sums and extended-valued entropy are retained. Finite support
  follows from local maximality and is not an initial assumption.
- The main theorem retains actual ℓ¹ local maximality, global attainment, and
  entropy saturation on infinite alphabets. Local structure is stronger than the
  manuscript in allowing arbitrary alphabets; attainment covers nonempty
  countable alphabets. Zero entropy and singleton alphabets have explicit wrappers.
- Curvature estimates include repeated coordinates and both equality iff clauses.
  Three-coordinate entropy curves and the displayed Hessian formula use the
  actual constructed curve and objective.
- Candidate roots are the unique entropy roots. Classification retains all ties,
  uniform endpoints, zero deletion, and binary duplication. `FiniteRealization`
  proves that fitting a fixed alphabet is equivalent to positive support size
  at most N, with exact preservation of entropy and objectives. At the zero
  endpoint the required support is m, rather than m+1.
- The repeated-size theorem treats general C² objectives and includes bridges
  from actual finite/countable local maxima. The heavy cutoff is proved through
  smooth real interpolation and then applied to integer multiplicities.
- The sharp value asymptotic uses genuine filter `IsBigO`. Optimizer scales and
  entropy/reciprocal error bounds have one eventual threshold for every optimizer.
  Sample complexity is the actual `Nat.find` least sample size; predecessor
  minimality, integer rounding, and the exact asymptotic prefactor are checked.
- Exponential zero counts include multiplicity. Crossing statements preserve
  directions, simple roots, endpoints, and the infinite endpoint. Winning heavy
  intervals are closed and light losing intervals are open, retaining ties.
- The finite-alphabet appendix includes slack-entropy full support, actual
  stationarity, the nonzero polynomial and degree/root bounds, and saturated
  support fitting. Feasible uniform laws and N=1/h=0 cases are retained.
- Occupancy quantities are random variables on actual IID samples, with ordinary
  integrals and complete optimizer equivalences. The singleton estimator K/n
  is also checked explicitly. All substantive Appendix D claims use exact
  rational Lean inequalities, including entropy-root brackets, objective
  enclosures, strict winners, and the heavy-branch counterexample.

## Alternate arguments and corrections to the ledger

1. Discrete coefficient recurrences and two explicit pair transfers replace
   the manuscript's differential mass-transfer argument. The required positivity
   and boundary comparisons are proved. The sigma<2 exclusion needs N≥1, as
   already stipulated in the manuscript; the ledger was corrected accordingly.
2. Strict discrete Turán/log-concavity inequalities prove the adjacent coefficient
   ratio conclusions directly. The unused continuous exponential interpolation
   derivative calculations are not separately formalized.
3. The kernel inequality uses an exactly evaluated positive remainder integral
   with a rational/logarithmic primitive. This replaces the sixth-derivative and
   five-jet Taylor calculation; positivity on both sides of 1 and equality only
   at 1 are proved for the same remainder.
4. Actual entropy-decreasing quadratic perturbations and a limit in their
   acceleration replace the repeated-size Lagrange-multiplier argument. They
   prove the same endpoint inequalities without assuming stationarity.
5. The rounded heavy candidate and its entropy-root expansion are checked.
   Bernoulli's inequality yields the reciprocal upper bound directly, replacing
   two auxiliary exponential expansions. An adjacent-threshold inverse-scale
   squeeze proves sample complexity with the exact prefactor.

No mathematical manuscript statement required clarification, weakening, or
repair. The only source edit was the requested editorial attribution correction
from “GPT 6 Sol” to “GPT-6 Astra.” The final tracked PDF was freshly rebuilt.

## Reproducible validation

- `lake clean entropy_constrained_missing_mass` then `lake build`: **passed,
  3,253 jobs**; every project module rebuilt against pinned dependencies.
- `lake env lean scripts/audit_lean.lean`: **2,133 declarations, 1,912 theorem
  constants**, all using only `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scripts/audit_source.py`: **113 owned Lean files**, **112 root-closure
  modules**, no proof escapes; all **152** ledger entries proved with acyclic
  dependencies; all **18** named results represented.
- `python3 scripts/missing_mass_extremizers_certificates.py`: all exact rational
  certificates passed, independently of the Lean proofs.
- `latexmk -g -pdf -interaction=nonstopmode -halt-on-error
  missing_mass_extremizers.tex`: passed, 19-page PDF, no undefined references or
  citations.
- Complete milestone diff and generated/source ownership reviewed; no temporary
  exploratory proof files are imported or committed.

The mathematical audit passed before production CI and main protection were
installed. CI reruns the build, axiom/source/ledger audits, and exact certificates.
