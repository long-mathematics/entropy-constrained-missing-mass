# Formalization status — IN PROGRESS

The entire manuscript (1,350 lines, including all appendices) was read on
2026-09-16. This is the initial exhaustive inventory, subject to the mandatory
independent final reread. **16 of 18 named manuscript results are proved in Lean.** The checked names are `thm:main`, `lem:entropy`, `lem:coefficient-extremum`, `lem:comparison`, `lem:repeated`, `thm:exceptional`, `lem:cutoff`, `thm:finite-classification`, `cor:small-samples`, `thm:asymptotics`, `lem:entropy-series`, `lem:zero-count`, `thm:heavy-crossing`, `thm:light-crossing`, `thm:finite-alphabet`, `cor:occupancy`.
The Python certificates are independent checks, not Lean proofs. Definitions,
equation cross-checks, and subsidiary obligations are counted separately below.

## Persistent state and next action

- Baseline: `7db0e78` (PR #4 squash-merged); work branch: `formalization/asymptotics-crossings-and-appendices`.
- Pinned Lean: v4.34.0; mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Current frontier: sample-complexity inversion and finite phase-interval reduction. Sixteen named results now kernel-check;
  eleven are merged in main. All numerical certificates are now actual Lean
  proofs, including the exact root brackets and optimizer uniqueness.
- Merged PR #2 validation: full `lake build` passed (2,898 jobs); namespace
  axiom audit checked 685 declarations (601 theorem constants including generated
  auxiliaries), all using only the three permitted standard axioms. Lexical audit
  of all 36 milestone Lean files found no holes/custom axioms. Exact Python
  certificates passed; ledger has 150 nodes, no missing dependency or cycle.
  No manuscript or PDF changes in this milestone.
- Current checked additions: full `ProbabilityVector.main_theorem`, actual entropy level curve and both derivative identities,
  exact objective second derivative, feasible finite perturbations/one-sided variation,
  actual simplex and reciprocal-square tilted probability laws, all moments and
  nondegeneracy, sharp curvature and equality characterizations. The main local
  structure and saturation results are stronger: they cover arbitrary/infinite
  alphabets respectively, while attainment covers all nonempty countable alphabets.
- Merged PR #3 validation: full `lake build` passed (2,928 jobs); root
  namespace audit checked 1,053 declarations (939 theorem constants including
  generated auxiliaries), all using only propext, Classical.choice and Quot.sound.
  Lexical audit of all 58 Lean files in the root import closure found no holes or
  custom axioms. Exact Python certificates passed. All 150 ledger nodes have
  valid acyclic dependencies; all 18 named source labels are represented.
  Complete milestone changes reviewed; no manuscript/PDF edits in this milestone.
- Next concrete proof units: SampleComplexity, PhaseIntervals, and the literal objective Hessian chain-rule display. The
  complete fixed-entropy asymptotic theorem, both crossing theorems, finite-
  alphabet classification, and certified examples are integrated for the next
  combined audit. An independent final manuscript reread is underway.
- Merged PR #4 validation: full `lake build` passed (2,946 jobs). The
  root namespace axiom audit checked 1,323 declarations (1,173 theorem constants,
  including generated auxiliaries), all using only the three permitted standard
  axioms. Lexical audit of all 72 Lean files in the root closure found no holes or
  custom axioms. All 150 ledger entries have valid acyclic dependencies. Exact
  Python certificates passed. The complete new proof units and correspondence
  were reviewed; no manuscript or PDF changes.
- Current milestone validation: full `lake build` passed (3,241 jobs); namespace
  audit checked 1,932 declarations (1,740 theorem constants), all using only
  propext, Classical.choice and Quot.sound. All 103 Lean files in the root
  import closure passed the hole/custom-axiom scan. All 150 ledger nodes have
  valid acyclic dependencies. Python certificates passed independently of the
  new Lean certificate proofs. Source hypotheses, uniform quantifiers,
  degeneracies, numerical enclosures and optimizer iffs were reviewed.
  No manuscript or PDF changes in this milestone.
- No production CI or protection should be installed before the complete final audit.
- Editorial change only: GPT 6 Sol → GPT-6 Astra; no mathematical TeX changes.
- Previous milestone validation: `lake build` passed (2,273 jobs); `lake env lean scripts/audit_lean.lean`
  audited 178 namespace declarations (154 theorem constants, including generated
  auxiliary declarations), permitting only propext, Classical.choice, Quot.sound.
  Source audit found no placeholders/custom axioms. All 18 named source labels
  appear in the ledger. Exact Python certificates passed. LaTeX compiled after
  the editorial change, with no undefined references or citations.
- Independent mathematical investigation checked all Appendix A identities and
  found no blocker. This is not a Lean proof of those analytic identities.
- Failed approaches: a blanket `import Mathlib` triggered unnecessary compilation;
  replaced with targeted imports. Lean v4.34 uses `Summable.of_nonneg_of_le`,
  `abs_add_le`, and `push Not`; use the installed API, not remembered older names.
  Blockers: none confirmed yet.

## Representation and equivalence policy

Use arbitrary finite/countable index types, nonnegative real coordinates with a
`HasSum` of one, and an ℓ¹ embedding/topology. Entropy is an `ENNReal` sum of
nonnegative `Real.negMulLog` terms; a finite-entropy bridge to a summable real
series is mandatory. The objective is a summable real series. Local maximality
must use the ℓ¹ neighborhood filter restricted to the entropy-feasible set.
No support finiteness is assumed. Finite support may only be exploited after
`finite_support`. Later finite vectors require a zero-extension equivalence.
Asymptotic errors must be uniform over optimizers, at fixed positive h.

For each TODO entry below, its intended declaration is a planning name, **not an
existing theorem**. Unless recorded otherwise: no reformulation has yet been
implemented, equivalence proof is pending with its representation, and no
alternate proof has yet been used. PROVED requires an actual kernel-checked
correspondence, not a numerical test or a theorem conditional on the result.

## Coverage and dependency graph

Tracked entries: **150** = 18 named results + 49 labelled equation cross-checks + 83 supporting obligations. Statuses: 134 PROVED, 3 IN PROGRESS, 13 TODO, 0 BLOCKED. Named results proved: 16/18.

The `Dependencies` fields are the adjacency-list dependency graph (arrows from
an obligation to prerequisites); it was checked for missing nodes and cycles.
Equation cross-checks preserve exact source displays, with their owning proof
unit as prerequisite. They do not count as independent named theorems.

### `probability`

- Source: Introduction; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.ofHasSum, hasSum_coord, coord_nonneg, coord_le_one, tsum_abs_coord`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: The ℓ¹ subtype accepts every nonnegative real HasSum-one vector; converse given by hasSum_coord. Valid for arbitrary index types.

For any nonempty finite or countable index type, nonnegative coordinates have sum one. Every coordinate is in [0,1]; their absolute sum is one. No finite-support assumption is permitted.

### `entropy`

- Source: Introduction; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.entropy_ne_top_iff, entropy_eq_ofReal_tsum, entropy_toReal`.
- Status: **PROVED**.
- Dependencies: `probability`.
- Reformulation/equivalence/alternate proof: Extended sum uses ofReal(Real.negMulLog); nonnegativity makes the ofReal bridge exact. Zero convention is inherited from negMulLog_zero.

Shannon entropy is the extended nonnegative sum of -p_i log p_i, with 0 log 0 = 0. Finite entropy is equivalent to summability of these real terms; its real value equals their real sum.

### `objective`

- Source: Introduction; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.objective_summable, objective_nonneg, objective_le_one, objective_reindex, objective_zeroExtend, objective_restrictSupport`.
- Status: **PROVED**.
- Dependencies: `probability`.
- Reformulation/equivalence/alternate proof: The defining real sum is absolutely summable. Generic embedding/restriction lemmas prove zero insertion/deletion and equivalence invariance; arbitrary index types and t=0 are also covered.

For every natural t (in particular t ≥ 1), ∑ p_i(1-p_i)^t converges absolutely and lies in [0,1]; its value is invariant under reindexing and adding or deleting zeros.

### `local_topology`

- Source: Introduction; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.dist_eq_tsum, LocalMaximizer, replaceFinite, dist_replaceFinite, tendsto_of_finite_coordinate_tendsto`.
- Status: **PROVED**.
- Dependencies: `probability`, `entropy`, `objective`.
- Reformulation/equivalence/alternate proof: The exact l1 metric and genuine finite normalized replacements are constructed. Coordinate convergence on a fixed finite perturbation implies l1 convergence for arbitrary filters.

The probability vectors carry the ℓ¹ topology. A feasible local maximizer means a neighborhood in this topology on which every feasible objective is at most its value. Finite-coordinate perturbations tending coordinatewise to the original vector tend in ℓ¹.

### `zero_entropy`

- Source: §5.2 and Appendix C; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.entropy_eq_zero_iff, objective_eq_zero_of_entropy_eq_zero, feasible_zero_iff, entropy_eq_zero_of_subsingleton`.
- Status: **PROVED**.
- Dependencies: `entropy`, `objective`.
- Reformulation/equivalence/alternate proof: An explicit coordinate equals one and every other coordinate equals zero iff extended entropy is zero. This includes one-symbol alphabets.

Entropy zero holds exactly for point masses; at t ≥ 1 their objective is zero. If the alphabet has one symbol this is the only probability vector.

### `root_coordinates`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.localRoots, contDiffAt_localRoots, eventually_localRoots_positive_ordered, hasDerivAt_localRoots_E, hasDerivAt_localRoots_P`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Actual inverse-function-theorem inverse for (S,E,P), then fixed-S directional derivatives; no surrogate stationarity premise.

For 0<x<y<z and fixed S=x+y+z, (E,P) are smooth local coordinates; sufficiently small changes retain positive distinct roots. Their derivatives are u_E=-u/W′(u) and u_P=1/W′(u), W(u)=u³-Su²+Eu-P.

### `integral_convergence`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `Curvature.integrableOn_I0, integrableOn_I1, integrableOn_curvature_numerator, I0_pos, I1_pos; TripleGeometry.integrableOn_div_D_sq`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: All I0/I1/curvature and three Hessian integrands converge for every positive triple. Squared-degree Hessian is the curvature numerator centered at zero.

For every positive triple, I₀,I₁ and all integrals defining entropy Hessians and K converge; I₀>0 and I₁>0.

### `log_integral`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `Curvature.integral_reciprocal_difference`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Convergent reciprocal difference on Ioi 0; omission of endpoint zero does not change Lebesgue integrals.

For u>0, log u=∫₀∞(1/(s+1)-1/(s+u)) ds.

### `root_partial_fractions`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.partial_fractions_one, partial_fractions_root`.
- Status: **PROVED**.
- Dependencies: `root_coordinates`.
- Reformulation/equivalence/alternate proof: Finite sums over Fin 3 equal the two exact rational functions; denominator nonvanishing is explicit.

For distinct positive roots, ∑1/((s+u)W′(u))=1/D(s) and ∑u/((s+u)W′(u))=-s/D(s), for s≥0.

### `entropy_hessian`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.hasDerivAt_localEntropy_E, hasDerivAt_localEntropy_P, hasDerivAt_partialEntropy_EE, hasDerivAt_partialEntropy_EP, hasDerivAt_partialEntropy_PE, hasDerivAt_partialEntropy_PP`.
- Status: **PROVED**.
- Dependencies: `root_coordinates`, `integral_convergence`, `log_integral`, `root_partial_fractions`.
- Reformulation/equivalence/alternate proof: Actual derivatives of localEntropy built from the smooth local roots. Reciprocal-integral differentiation has a uniform integrable majorant; neighboring inverse charts are proved compatible.

At distinct positive roots, H_E=I₁, H_P=I₀, H_EE=-∫s²/D², H_EP=-∫s/D², H_PP=-∫1/D²; justify differentiation under each integral.

### `entropy_curve`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.entropyCurve, eventually_entropyCurve_entropy, eventually_entropyCurve_derivatives, hasDerivAt_entropyCurve_m, hasDerivAt_deriv_entropyCurve_product`.
- Status: **PROVED**.
- Dependencies: `entropy_hessian`.
- Reformulation/equivalence/alternate proof: A genuine analytic implicit function with E=E₀+r and fixed S gives the local root path. Entropy is constant nearby, P′=−m holds throughout a neighborhood, and the Hessian/quotient calculation yields m′=−K and P″=K with the original normalization.

The local entropy level is a smooth curve P(E), with P′=-m and P″=K.

### `triple_necessary`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.objective_stationary_of_localMax, objective_curvature_nonpos_of_localMax, objective_P_nonneg_of_localMax`.
- Status: **PROVED**.
- Dependencies: `local_topology`, `entropy_curve`.
- Reformulation/equivalence/alternate proof: All three necessary conditions are derived from genuine ℓ¹ local maximality through embedded actual paths. Finite support and entropy saturation are not assumed; slack entropy is included.

A local maximizer containing three distinct positive coordinates has D_t=0, C_t≤0 and (F_t)_P≥0, including when the entropy constraint is slack.

### `objective_calculus`

- Source: §2 and §5.1; unnamed supporting assertion.
- Lean correspondence: `deriv_missingMassTerm, deriv2_missingMassTerm, existsUnique_second_derivative_zero, not_three_equal_objective_derivatives`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Exact polynomial derivatives, the unique interior zero of f″ for t≥2, and the two-Rolle contradiction are checked, including t=1 endpoint formulas.

For integer t≥1, f_t is polynomial and f′_t(u)=(t+1)(1-u)^t-t(1-u)^(t-1). For t>1 and 0<u<1, f″_t(u)=t(1-u)^(t-2)((t+1)u-2), with just one zero in (0,1).

### `positive_R`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `TripleGeometry.objective_P_pos_of_stationary`.
- Status: **PROVED**.
- Dependencies: `triple_necessary`, `objective_calculus`, `root_coordinates`.
- Reformulation/equivalence/alternate proof: Actual divided differences express root-coordinate derivatives; nonnegative product derivative and stationarity imply positivity by equality of the three f′ values and Rolle. This entry is the stated conditional algebraic step; the separate triple_necessary entry supplies stationarity from local maximality.

For t>1 at a stationary triple with (F_t)_P≥0, R_t=(F_t)_P>0: otherwise equality of three first derivatives contradicts Rolle and the one-zero property.

### `t_one_triple`

- Source: §2; unnamed supporting assertion.
- Lean correspondence: `triple_objective_one, hasDerivAt_objective_one_path, not_localMax_three_sizes_one`.
- Status: **PROVED**.
- Dependencies: `triple_necessary`.
- Reformulation/equivalence/alternate proof: The affine-in-E identity and actual entropy-path derivative 2 contradict Fermat stationarity. The generic two-size extraction also gives finite support and saturation at t=1.

F₁=S-S²+2E and its entropy-curve first derivative is 2, excluding three sizes at t=1.

### `homogeneous`

- Source: §3; unnamed supporting assertion.
- Lean correspondence: `homogeneous3_eq_monomial_sum, homogeneous3_pos_of_ne_zero, homogeneous3_partial_fraction, homogeneousSeries_eq_product_inverse`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Explicit monomial sum equals the recursively defined coefficients. Formal power-series equality with the product of three inverses verifies the generating function, including repeated/zero variables.

For three nonnegative variables, G=∏(1-r_i w)^(-1)=∑h_j w^j, where h_j is the complete homogeneous polynomial and negative indices are zero. Nonzero r implies h_j>0 for all j≥0.

### `turan`

- Source: §3, eq:turan; unnamed supporting assertion.
- Lean correspondence: `homogeneous3_turan_all, homogeneous3_turan_nonneg, homogeneous3_ratio_antitone, homogeneous3_ratio_strictAnti`.
- Status: **PROVED**.
- Dependencies: `homogeneous`.
- Reformulation/equivalence/alternate proof: The j=0 negative-index convention is explicit. Algebraic recurrence proves the identity directly at all real triples; positivity supplies the ratio conclusions.

For all nonnegative triples and integers j≥0, h_j²-h_(j-1)h_(j+1)=h_j(r₁r₂,r₁r₃,r₂r₃)≥0. For nonzero r the successive ratios decrease; for all-positive r they decrease strictly.

### `coefficient_transfer`

- Source: §3; unnamed supporting assertion.
- Lean correspondence: `coefficientDifference_pos_of_le, coefficientDifference_le_of_pair_product, coefficient_extremum`.
- Status: **IN PROGRESS**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: Discrete recurrence comparison proves nondecrease under pair concentration and two explicit transfers prove the full bound. The original derivative identity and sigma exclusion are not yet individually checked.

If b_N=h_N-h_(N-1)>0, all earlier b_j are positive, σ<2, and transferring mass from a smaller interior coordinate to a larger one preserves positivity and does not decrease b_N; at most two transfers reach a vertex of the fixed-sum cube slice. Include N=0,1, r=0 and σ=1,2 boundaries.

### `coefficient_boundary`

- Source: §3; unnamed supporting assertion.
- Lean correspondence: `coefficientDifference_two_ones, homogeneous2_one_geometric_identity, coefficientDifference_two_ones_le, coefficientDifference_zero_last_le_one`.
- Status: **IN PROGRESS**.
- Dependencies: `homogeneous`.
- Reformulation/equivalence/alternate proof: Boundary bounds used by the full theorem are checked including sigma=1. Explicit one-one-zero power identity and all stated boundary classification assertions still need wrappers.

At fixed σ∈(0,2), boundary representatives are (1,1,1-σ) for σ≤1 and (1,2-σ,0) for σ≥1. Coefficients b_N are respectively ∑_{k=0}^N(1-σ)^k≤1/σ and (2-σ)^N≤1.

### `comparison_ratios`

- Source: §3; unnamed supporting assertion.
- Lean correspondence: `weightedCoefficient_pos_of_comparison, weightedCoefficient_pos_of_le, weightedCoefficient_middle_strict_concavity, weightedCoefficient_strict_log_concave, comparisonAuxCoefficient_pos_of_le`.
- Status: **IN PROGRESS**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: Positivity through n+1, strict Turan cross-product inequality and all a_j positivity are checked. Discrete middle concavity replaces exponential interpolation. Explicit ratio and interpolation assertion wrappers remain to be recorded.

Under lem:comparison hypotheses with n≥1, all B_j=h_j-βh_(j-1) are positive through n+1 and B_j/B_(j-1) strictly decrease there, by the strictly concave exponential interpolation g. Hence a_j=B_j-αB_(j-1)>0 for 0≤j≤n.

### `comparison_telescoping`

- Source: §3; unnamed supporting assertion.
- Lean correspondence: `comparisonAuxCoefficient_telescoping, comparisonCoefficient_le_of_aux_nonneg, coefficient_comparison, comparisonCoefficient_eq_coeff`.
- Status: **PROVED**.
- Dependencies: `comparison_ratios`, `lem:coefficient-extremum`.
- Reformulation/equivalence/alternate proof: Exact finite convolution equals the power-series coefficient; scaled extremum bound and strict telescoping bound include index zero.

Under the comparison hypotheses, J=∑_{j=0}^{n-1}a_jB_(n-1-j)≤C k_(n-1)<C k_n/β with C=max(1,β/(3β-∑q_i)); n=0 has J=0,k₀=1.

### `divided_differences`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `secondDifference_constant, secondDifference_shifted_linear, secondDifference_shifted_pow, hasDerivAt_localObjective_P, hasDerivAt_objective_path`.
- Status: **PROVED**.
- Dependencies: `homogeneous`, `root_coordinates`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: Exact polynomial divided differences include degrees zero and one; actual first derivatives of the inverse-root map and of any fixed-S path with E′=1,P′=−m yield R and D.

The second divided difference of (1-u)^j at x,y,z is h_(j-2)(1-x,1-y,1-z), including j=0,1. Therefore R_t=(t+1)k_n and D_t=(t+1)(k_(n+1)-βk_n).

### `objective_curvature`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `hasCoeffDerivAt_complementarySeries, hasDerivAt_stationarityCoefficient, hasDerivAt_deriv_objective_entropyCurve`.
- Status: **PROVED**.
- Dependencies: `divided_differences`, `entropy_curve`.
- Reformulation/equivalence/alternate proof: The exact actual second derivative of the constructed entropy curve is (n+3)(K k_n−J). Power-series coefficient differentiation is proved coefficientwise, including n=0 and β′=−K. This proves the needed curvature directly; the separate labelled general partial-Hessian chain-rule display remains to be cross-checked.

For t≥2,n=t-2,α=t/(t+1),β=1+m,q=(1-x,1-y,1-z), the entropy-curve second derivative is C_t=(t+1)(K k_n-J). The variation β′=-K must be included.

### `curvature_contradiction`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `coefficient_curvature_ratio_gap, coefficient_curvature_twentieth_gap, not_localMax_three_sizes_of_curvature_bound`.
- Status: **PROVED**.
- Dependencies: `lem:comparison`, `lem:entropy`, `objective_curvature`.
- Reformulation/equivalence/alternate proof: Both strict quantitative bounds are checked with actual source coefficients. The full local contradiction composes them with exact objective variations and the proved sharp analytic bound in MainTheorem.

For S≤1, D_t=0 and R_t>0 imply C_t/R_t>1/(15(S+m)) and C_t>R_t/(20S)>0.

### `two_sizes`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.two_sizes_of_localMax, TripleGeometry.not_localMax_three_sizes`.
- Status: **PROVED**.
- Dependencies: `curvature_contradiction`, `positive_R`, `t_one_triple`, `local_topology`.
- Reformulation/equivalence/alternate proof: Ordered embedded triples are excluded by the actual entropy path. Exhaustive total-order cases extract two positive sizes (allowed to coincide). Holds for arbitrary index types, hence finite/countable alphabets.

Every ℓ¹-local maximum on every finite or countable alphabet has at most two positive coordinate values, by feasible three-coordinate perturbations.

### `finite_support`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.finite_support_of_localMax`.
- Status: **PROVED**.
- Dependencies: `probability`, `two_sizes`.
- Reformulation/equivalence/alternate proof: Derived from the now-proved two-size conclusion and finiteness of each positive-mass fiber; no finite-support premise.

A probability vector with at most two distinct positive coordinate values has finite support, since each positive value can occur only finitely many times.

### `sorted_reduction`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.antitone_sortedNat, entropy_sortedNat, objective_sortedNat, coord_le_recip_of_antitone, isMaxOn_feasible_of_sorted`.
- Status: **PROVED**.
- Dependencies: `objective`, `entropy`.
- Reformulation/equivalence/alternate proof: Alternate reduction: finite entropy-nonincreasing coarsenings converge in objective and can be sorted exactly. Compact sorted class therefore attains the unrestricted supremum without asserting a global infinite permutation.

For the countably infinite optimization, symmetry and zero invariance allow a maximizing sequence of nonincreasing vectors. A sorted vector has p_i≤1/i for i≥1.

### `entropy_tail`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.sorted_tail_le, uniform_sorted_tail, cauchySeq_of_sorted_coordinate_tendsto, isCompact_sortedFeasible`.
- Status: **PROVED**.
- Dependencies: `sorted_reduction`.
- Reformulation/equivalence/alternate proof: Zero-based natural coordinates translate source i>N to n>=N. Coordinate convergence and uniform tails imply l1 Cauchy; completeness of the mass-one subtype preserves normalization.

For a sorted feasible vector and N≥1, ∑_{i>N}p_i≤h/log(N+1). A coordinatewise limit of a uniformly entropy-bounded sorted sequence has mass one and the convergence is in ℓ¹.

### `entropy_lsc`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.lowerSemicontinuous_entropy_function, lowerSemicontinuous_entropy, isClosed_feasible`.
- Status: **PROVED**.
- Dependencies: `entropy`.
- Reformulation/equivalence/alternate proof: Product-topology lower semicontinuity for extended entropy is proved first and composed with the continuous coordinate map.

Entropy is lower semicontinuous under coordinatewise convergence of probability vectors by the nonnegative Fatou lemma.

### `objective_lipschitz`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `exists_attained_objective_lipschitz_constant, ProbabilityVector.objective_dist_le_derivativeMax`.
- Status: **PROVED**.
- Dependencies: `objective`, `objective_calculus`, `local_topology`.
- Reformulation/equivalence/alternate proof: The absolute derivative attains its finite maximum on [0,1]; the scalar mean-value bound and actual countable ℓ¹ objective estimate use exactly this constant. The prior explicit t+1 bound is also retained.

For t≥1, L_t=max_{0≤u≤1}|f_t′(u)| is finite, and |Φ_t(p)−Φ_t(q)|≤L_t‖p−q‖₁ on every finite/countable alphabet.

### `attainment`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.exists_global_maximizer_finite, exists_global_maximizer_countable, exists_global_maximizer`.
- Status: **PROVED**.
- Dependencies: `entropy_tail`, `entropy_lsc`, `objective_lipschitz`, `zero_entropy`.
- Reformulation/equivalence/alternate proof: All nonempty countable index types, including finite ones, and all t>=0. Infinite case uses compact sorted set and entropy-nonincreasing finite coarsenings, an alternate proof of the same unrestricted maximum.

For every t≥1 and finite h≥0, a feasible maximum exists, on finite alphabets by compactness and on countably infinite alphabets by the sorted diagonal sequence and tail bound.

### `atom_splitting`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.splitAtom, dist_splitAtom, entropy_splitAtom, objective_splitAtom, objective_lt_splitAtom`.
- Status: **PROVED**.
- Dependencies: `entropy`, `objective`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: Actual double coordinate update in the l1 probability subtype; exact distance/entropy/objective change and positive entropy increment tending to zero.

For 0<ε<a≤1, splitting a into a-ε,ε changes ℓ¹ distance by 2ε, raises entropy by a positive increment tending to zero, and strictly increases Φ_t for every integer t≥1.

### `entropy_saturation`

- Source: §4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.entropy_saturation_of_localMax, entropy_toReal_saturation_of_localMax`.
- Status: **PROVED**.
- Dependencies: `finite_support`, `atom_splitting`.
- Reformulation/equivalence/alternate proof: The structural finite-support theorem supplies an unused atom on every infinite alphabet; the checked atom-splitting improvement forces equality. Extended and real entropy forms are both supplied.

Every countably infinite alphabet local maximizer has H=h: use finite support and split into an unused coordinate if H<h.

### `repeated_variation`

- Source: §5.1; unnamed supporting assertion.
- Lean correspondence: `repeatedFour_nonpos_curvature, repeatedFour_weighted_endpoint_bound, ProbabilityVector.repeated_pair_weighted_bound`.
- Status: **PROVED**.
- Dependencies: `local_topology`.
- Reformulation/equivalence/alternate proof: Alternate second-variation proof constructs actual entropy-decreasing quadratic paths and passes their acceleration to the critical value. This directly proves the source endpoint inequalities with the logarithmic secant in place of a multiplier; no multiplier existence theorem or stationarity assumption is used.

A repeated size u at a local maximizer has f″(u)≤0. If x<y are both repeated, the four-coordinate mass/entropy gradients are independent, multipliers satisfy f′=λ+μ(-log u-1), and pair-difference second variations give uf″(u)+μ≤0.

### `weighted_log_average`

- Source: §5.1; unnamed supporting assertion.
- Lean correspondence: `weighted_second_derivative_integral, weighted_log_average, exists_weighted_second_derivative_eq_log_secant`.
- Status: **PROVED**.
- Dependencies: `repeated_variation`.
- Reformulation/equivalence/alternate proof: The literal integral/secant equality follows by FTC; Cauchy mean value realizes it as an interior weighted curvature and gives the strict-quasiconvexity contradiction.

For repeated x<y, -μ=(f′(y)-f′(x))/log(y/x)=∫_x^y uf″(u)du/u / log(y/x). Strict quasiconvexity makes this average strictly below max(xf″(x),yf″(y)).

### `quasiconvex`

- Source: §5.1; unnamed supporting assertion.
- Lean correspondence: `weightedCurvature_strict_quasiconvex_on_interval, deriv_weightedCurvature_mul_one_sub, curvatureDerivativeQuadratic_strictAnti, curvature_quadratic_factor, curvature_roots_order`.
- Status: **PROVED**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: The full strict quasiconvexity conclusion is checked by a root-free quadratic sign argument, including t=1,2. Explicit radical roots and their ordering now also kernel-check in QuasiconvexRoots.

For f_t and integer t≥1, uf″_t is strictly quasiconvex on the interval containing f″_t≤0. For t=1 it is -2u; for t>1 its derivative has the displayed quadratic with roots 0<r_-<2/(t+1)<r_+.

### `shape_boundaries`

- Source: §5.1; unnamed supporting assertion.
- Lean correspondence: `candidateCoord_uniform, binary_candidate_swap, ProbabilityVector.not_lightCandidateForm_heavy`.
- Status: **PROVED**.
- Dependencies: `probability`.

Uniform laws are z=q=1/(m+1). Binary nonuniform laws have duplicate light/heavy descriptions; for support≥3 these nonuniform shapes differ up to permutation.

### `branch_entropy`

- Source: §5.2; unnamed supporting assertion.
- Lean correspondence: `branchEntropy_zero, branchEntropy_one, branchEntropy_uniform, continuous_branchEntropy, hasDerivAt_branchEntropy`.
- Status: **PROVED**.
- Dependencies: `entropy`.
- Reformulation/equivalence/alternate proof: Exact source formula is branchEntropy; proved for positive real m, hence for all positive natural multiplicities. CandidateVectors proves equality to actual distribution entropy.

For integer m≥1, E_m is continuous on [0,1], E_m(0)=log m, E_m(1/(m+1))=log(m+1), E_m(1)=0, and E′_m(z)=log((1-z)/(mz)) for 0<z<1.

### `entropy_roots`

- Source: §5.2; unnamed supporting assertion.
- Lean correspondence: `existsUnique_light_candidate_parameter, existsUnique_heavy_candidate_parameter, light_entropy_eq_log_iff, light_entropy_index, heavy_entropy_index, binary_entropy_root_duplicate`.
- Status: **PROVED**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: All unique-root and zero endpoint assertions are checked. The entropy index is forced for every light/uniform representation; heavy indices are bounded below. Binary descriptions are identified by exact coordinate reindexing.

For h>0,k=floor(exp h), exactly one a∈[0,1/(k+1)) solves E_k(a)=h. It is zero iff h=log k. For every integer m≥k, exactly one z_m∈(1/(m+1),1) solves E_m(z_m)=h. No other light/uniform shapes saturate h.

### `candidate_completeness`

- Source: §5.2; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.candidate_complete_of_localMax, candidate_complete_of_globalMax`.
- Status: **PROVED**.
- Dependencies: `thm:exceptional`, `entropy_saturation`, `entropy_roots`, `shape_boundaries`.
- Reformulation/equivalence/alternate proof: Actual coordinate equality to a zero-extended entropy-matched light or heavy vector. Uniform endpoints and binary duplication are proved explicitly. Applies to all infinite alphabets for the local assertion.

Every global optimizer on a countably infinite alphabet is p_L or p_m^H for m≥k, with the binary duplicate exactly when 0<h<log 2 and m=1.

### `real_heavy_roots`

- Source: §5.3; unnamed supporting assertion.
- Lean correspondence: `heavyRoot_spec, heavyRoot_eq_of_spec, contDiffAt_heavyRoot, hasDerivAt_heavyRoot, hasDerivAt_heavyLight, heavy_entropy_sigma`.
- Status: **PROVED**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: Canonical unique real-multiplicity root; smoothness follows from the implicit-function theorem and root uniqueness. All derivative identities are derived for this function.

For h>0 and real m>exp h-1, a unique heavy root exists and depends smoothly on m. With σ=log(z/q)>0, h=-log z+(1-z)σ, dz/dm=q/σ>0 and dq/dm=-q(1+σ)/(mσ)<0.

### `heavy_derivative`

- Source: §5.3; unnamed supporting assertion.
- Lean correspondence: `hasDerivAt_heavyValue, hasDerivAt_cutoffAux`.
- Status: **PROVED**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: Real powers give the actual continuation for all real exponents. The scalar derivative and auxiliary derivative are checked exactly.

For real s≥1, db_m(s)/dm=q Ψ_s(z,q)/σ, Ψ_s=f′_s(z)-f′_s(q)+sqσ(1-q)^(s-1). For z≤1/s, use A′_z(u)=s(1+log(z/u))(1-u)^(s-2)(su-1)<0 on q<u<z.

### `heavy_cutoff_sign`

- Source: §5.3; unnamed supporting assertion.
- Lean correspondence: `heavyPsi_neg_of_cutoff, heavy_cutoff`.
- Status: **PROVED**.
- Dependencies: `heavy_derivative`.
- Reformulation/equivalence/alternate proof: The two source sign cases and s=1 are covered by the checked real-exponent cutoff proof.

If z>1/s and m≥sh+1, f′_s(z)<0 and 1-q-sq(1+σ)>1-(sh+1)/m≥0, because (1-z)(1+σ)<h. Hence Ψ_s<0; include s=1.

### `cutoff_discrete`

- Source: §5.3; unnamed supporting assertion.
- Lean correspondence: `branchObjective_lt_at_cutoff, ProbabilityVector.candidate_complete_at_cutoff`.
- Status: **PROVED**.
- Dependencies: `lem:cutoff`.
- Reformulation/equivalence/alternate proof: Strict antitonicity on the real tail excludes every integer beyond the canonical cutoff; no tied optimizer is discarded.

For M=max(k,ceil(th+1)), every integer j>M has b_j(t)<b_M(t). All removed candidates have strictly larger support.

### `small_samples_hessian`

- Source: §5.4; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.repeated_pair_weighted_bound, repeatedPairHessian_one, repeatedPairHessian_two, ProbabilityVector.not_localMax_heavy_candidate_smallSamples`.
- Status: **PROVED**.
- Dependencies: `repeated_variation`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: Entropy-feasible quadratic paths prove the necessary Hessian bound. Exact positive scalar formulas contradict it for t=1,2 and all natural m>=2.

For heavy m≥2, write z=rq,q=1/(m+r),r>1. The necessary qf″_t(q)+μ≤0 instead equals 2q((r-1)/log r-1)>0 for t=1 and N_m(r)/((m+r)²log r)>0 for t=2.

### `small_samples_scalar`

- Source: §5.4; unnamed supporting assertion.
- Lean correspondence: `smallSampleNumerator_decompose, hasDerivAt_smallSampleNumerator_two, smallSampleNumerator_two_pos, hasDerivAt_logRatioGap, logRatioGap_pos`.
- Status: **PROVED**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: Exact scalar expressions, derivative and positivity for every real m>=2 and r>1, stronger than natural multiplicities.

N_m=N₂+4(m-2)(r-1-log r); N₂(1)=0 and N₂′(r)=2(r-1/r-2log r)>0 for r>1, since the inner derivative is (r-1)²/r².

### `heavy_L_identities`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `heavy_tail_entropy, heavy_tail_objective, heavy_tail_entropy_correction, entropyTailCorrection_remainder_bound, entropyTailCorrection_expansion`.
- Status: **PROVED**.
- Dependencies: `branch_entropy`, `objective`.
- Reformulation/equivalence/alternate proof: Exact identities and a quantitative quadratic remainder; the stated expansion is an actual one-sided IsBigO at zero.

For a heavy law L=mq,z=1-L, h=-(1-L)log(1-L)-L log q, Φ_t=(1-L)L^t+L(1-q)^t, and A(L)=-(1-L)log(1-L)/L=1-L/2+O(L²) as L↓0.

### `asymptotic_lower`

- Source: §6, lower bound; unnamed supporting assertion.
- Lean correspondence: `roundedTailMass_eventually_spec, rounded_entropy_scale_nat_expansion, reciprocal_upper_of_heavy_candidate`.
- Status: **PROVED**.
- Dependencies: `entropy_roots`, `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: Actual multiplicity ceil(ht) and its unique entropy root are used. The source reciprocal asymptotic follows via Bernoulli and d^2/(d-1), an alternate proof avoiding an unnecessary exponential remainder.

For m=ceil(ht) at fixed h>0, eventually a heavy entropy root exists, L=O_h(1/log t), and d=h/L=T+log T+1+O_h(log T/T); tq=1/d+O_h(1/(tT)) and -t log(1-q)=1/d+O_h(1/(tT)).

### `reciprocal_upper`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `asymptotic_reciprocal_upper`.
- Status: **PROVED**.
- Dependencies: `asymptotic_lower`, `attainment`.
- Reformulation/equivalence/alternate proof: Actual optimum satisfies the eventual stated upper bound, with constants depending only on fixed h.

For fixed h>0, h/B_t(h)≤T+log T+2+O_h(log T/T), hence B_t(h)≥c_h/T eventually for c_h>0.

### `eventually_heavy`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `asymptotic_value_lower, tendsto_nat_mul_lightValue, ProbabilityVector.globalMax_eventually_heavy`.
- Status: **PROVED**.
- Dependencies: `reciprocal_upper`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: The fixed light candidate decays faster than the explicit heavy lower bound. At one common threshold every global maximum is heavy.

The fixed light/uniform candidate decays exponentially, so every optimizer is eventually heavy, uniformly in its choice.

### `optimizer_bounds`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `heavy_entropy_largest_atom_bound, light_block_le_exp, heavy_competitive_scaled_atom_lt_one, heavy_scale_ge_log_sample, optimalHeavy_eventually_estimates`.
- Status: **PROVED**.
- Dependencies: `eventually_heavy`, `heavy_L_identities`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: Explicit scalar estimates are applied simultaneously to every maximizing heavy root after all threshold conditions have been discharged.

Uniformly over heavy optimizers, z≥exp(-h), L≤ρ_h=1-exp(-h)<1, the heavy contribution is ≤ρ_h^t, u=tq=O_h(log T), L=O_h(1/T), d=T-log u+1+O_h(1/T).

### `reciprocal_lower`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `heavy_competitive_reciprocal_lower_strong, asymptotic_reciprocal_lower, optimalValue_sharp_asymptotic`.
- Status: **PROVED**.
- Dependencies: `optimizer_bounds`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: The lower bound retains the nonnegative scalar gap and has explicit error (2h+1)/log t. Together with the checked upper bound it yields the exact sharp value expansion.

Uniformly over optimizers, h/B_t≥d exp u-O_h(T²ρ_h^t)=d exp u-o_h(1/T). Eventually u<1 and d≥T; putting v=Tu gives d exp u≥T+log T+1+v-log v-O_h(1/T)≥T+log T+2-O_h(1/T).

### `optimizer_scales`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `scalarGap_coercive, optimizer_scales_uniform, ProbabilityVector.globalMax_optimizer_scales_uniform`.
- Status: **PROVED**.
- Dependencies: `reciprocal_lower`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: A positive scalar gap away from one yields uniform control. All three normalized errors are bounded for every optimizer at the same threshold, with actual candidate representations.

Uniformly over optimizers, 0≤v-log v-1=O_h(log T/T); coercivity and the unique zero at v=1 give v→1. Thus q∼1/(t log t), L∼h/log t and m∼ht.

### `strict_B_monotone`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `strictAnti_optimalValue`.
- Status: **PROVED**.
- Dependencies: `attainment`, `entropy_saturation`, `thm:asymptotics`.
- Reformulation/equivalence/alternate proof: Strict antitonicity of the actual optimal value at every natural sample index, using attainment and strict objective decrease.

At fixed h>0, B_t strictly decreases for positive integer t and tends to zero. This gives existence of the integer hitting time N_h(ε) for ε>0.

### `asymptotic_inversion`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.asymptotic_inversion`.
- Status: **TODO**.
- Dependencies: `strict_B_monotone`, `thm:asymptotics`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For A=h/ε and S=A-log A-2, the integers nearest exp(S±η) bracket N_h(ε) eventually for every fixed η>0; hence log N_h=S+o(1).

### `occupancy_identities`

- Source: §6; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.integral_singletonCount, integral_distinctCount_increment, integral_coverage`.
- Status: **PROVED**.
- Dependencies: `objective`.
- Reformulation/equivalence/alternate proof: A PMF is built from the original probability coordinates, then a finite IID product measure. Singleton cardinality, observed-mass sum and distinct-count increment are genuine random variables; their expected values are proved by countable nonnegative integration and conversion to Bochner integrals.

For independent samples of any finite/countable probability law, E K_(n,1)=n Φ_(n-1) for n≥2, E(K_(t+1)-K_t)=Φ_t for t≥1, and E C_t=1-Φ_t. Countable interchanges are justified; optimizers coincide exactly, including all ties.

### `uniform_curvature`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.I0_uniform, I1_uniform, m_uniform, K_uniform`.
- Status: **PROVED**.
- Dependencies: `integral_convergence`.
- Reformulation/equivalence/alternate proof: Exact integrals with convergence and positive a, using inverse-power primitives.

For x=y=z=a>0, I₀=1/(2a²), I₁=1/(2a), m=a and K=4/(15a).

### `kernel_density`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.integral_kernel, integral_mul_kernel`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Exact nonnegative rational density, mass one and first moment a on positive half-line.

κ_a(s)=2a²/(s+a)³ is a probability density on [0,∞) with mean a for every a>0.

### `kernel_remainder`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.J_closed_form, J_one, kernel_remainder_identity, kernel_bound, kernel_bound_eq_iff`.
- Status: **PROVED**.
- Dependencies: `kernel_density`.
- Reformulation/equivalence/alternate proof: Exact positive remainder evaluated by a rational/logarithmic primitive instead of six Taylor derivatives. Strictness and equality iff a=1 are checked.

J_*(a)=∫(s-1)²κ₁(s)κ_a(s)ds has the displayed logarithmic closed form for a≠1 and J_*(1)=8/15. Its difference from 2(9-a)/(15(a+1)) equals the displayed nonnegative integral remainder for every a>0. Include both sides of a=1.

### `kernel_taylor`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.kernel_taylor`.
- Status: **TODO**.
- Dependencies: `kernel_density`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

The smooth M(a) defined from J_* has M^(j)(1)=0 for 0≤j≤5 and M^(6)(a)=360(a-1)(2a³+12a²-10a+13)/a⁴. The cubic equals 2a³+12(a-5/12)²+131/12>0 for a>0.

### `mixture_bound`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.mixture_curvature_bound, mixed_kernel_scaling, integrable_mixed_kernel_prod, integral_mixed_mixture_eq`.
- Status: **PROVED**.
- Dependencies: `kernel_remainder`.
- Reformulation/equivalence/alternate proof: Law represented on subtype Icc a b with positive a: every compact positive support lies in such an interval. Scaling, product integrability, Fubini and quadratic expansion are proved.

For any probability law λ with compact positive support, mλ=EλV and G=Eλκ_V obey ∫(s-mλ)²G²≥8mλ/15+(2/3)Eλ[(V-mλ)²/(V+mλ)]. Justify Fubini, scaling, and the square expansion.

### `simplex_mixture`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.simplexLaw_mean, simplexLaw_inverse_cube, simplexLaw_inverse_square, simplexLaw_inverse, simplexLaw_not_ae_constant`.
- Status: **PROVED**.
- Dependencies: `integral_convergence`.
- Reformulation/equivalence/alternate proof: Concrete barycentric uniform-simplex measure has the exact first/second moments and reciprocal-cube identity. Dominated Fubini yields inverse moments. Explicit variance rules out almost-sure constancy for nonuniform triples.

For uniform simplex U and V=xU₁+yU₂+zU₃, EV=S/3 and E(s+V)^(-3)=1/D(s). Thus I₀=EV^(-2)/2 and I₁=EV^(-1)/2. Nonuniform x,y,z imply V is not almost surely constant.

### `tilted_moments`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.tiltedSimplexLaw_probability, tiltedSimplexLaw_mean, tiltedSimplexLaw_second_moment, tiltedSimplexLaw_third_moment, tiltedSimplexLaw_density, tiltedSimplexLaw_weighted_variance_pos, m_lt_mean_of_nonuniform`.
- Status: **PROVED**.
- Dependencies: `simplex_mixture`.
- Reformulation/equivalence/alternate proof: The reciprocal-square withDensity law is genuinely a probability measure. Exact density and three moments are checked; equivalence of null sets and raw variance establish strictness for every nonuniform triple.

Under dλ=v^(-2)dP_V/(2I₀), G=1/(I₀D), EλV=m, b₂=EλV²=1/(2I₀), EλV³=(S/3)b₂. Hence Eλ[(V-m)²(V+m)]=(S/3-m)b₂>0 for nonuniform triples, proving 0<m<S/3.

### `mixture_cauchy`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.mixture_dispersion_lower_of_third_moment, tiltedSimplexLaw_curvature, curvature_lower_of_nonuniform`.
- Status: **PROVED**.
- Dependencies: `mixture_bound`, `tilted_moments`.
- Reformulation/equivalence/alternate proof: Integrated nonnegative-square proof supplies the Cauchy bound without square-root machinery. Applying it to the actual tilt yields precisely the manuscript K lower bound, including all integrability requirements.

Cauchy–Schwarz gives Eλ[(V-m)²/(V+m)]≥(b₂-m²)²/((S/3-m)b₂), hence K≥(8/15)I₁+(1-2mI₁)²/(S-3m).

### `curvature_algebra`

- Source: Appendix A; unnamed supporting assertion.
- Lean correspondence: `Curvature.sum_mul_I1_ge, entropy_curvature_strict, m_eq_mean_iff, entropy_curvature_eq_iff`.
- Status: **PROVED**.
- Dependencies: `mixture_cauchy`, `uniform_curvature`.
- Reformulation/equivalence/alternate proof: AM–GM gives S I1≥3/2; the exact two algebraic square identities imply strict curvature for nonuniform triples. Uniform evaluation gives both equality characterizations.

AM–GM gives j=SI₁≥3/2. For r=m/S∈(0,1/3), d=1-3r,v=j-3/2≥0, the two displayed square identities imply K>16/(15(S+m)); strictness and uniform_curvature give both iff equality clauses.

### `entropy_log_series`

- Source: Appendix B.1; unnamed supporting assertion.
- Lean correspondence: `hasSum_missingMassTerm_div, ProbabilityVector.entropy_series`.
- Status: **PROVED**.
- Dependencies: `entropy`, `objective`.
- Reformulation/equivalence/alternate proof: Uses the mathlib logarithm power series, includes zero coordinates separately, then ENNReal.tsum_comm. Natural n corresponds exactly to manuscript j=n+1.

For 0<u≤1, -log u=∑_{j≥1}(1-u)^j/j. Multiplication by p_i and nonnegative Tonelli give the entropy series, including infinite entropy and zero atoms.

### `entropy_difference`

- Source: Appendix B.1; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.hasSum_objective_sub_div_zero, summable_abs_objective_sub_div, exists_objective_lt_of_equal_entropy, objective_eq_of_equal_entropy_of_le`.
- Status: **PROVED**.
- Dependencies: `lem:entropy-series`.
- Reformulation/equivalence/alternate proof: Equal finite extended entropy gives absolutely summable zero weighted difference and the required sign contradiction.

For two finite equal-entropy laws, ∑_{j≥1}(Φ_j(p)-Φ_j(q))/j converges absolutely to zero. If a difference is nonnegative at all positive integers and strictly positive at some integer, equal entropy is impossible.

### `rolle_multiplicity`

- Source: Appendix B.1; unnamed supporting assertion.
- Lean correspondence: `rolle_multiplicity, exponential_sum_zeros_of_nonzero`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: Induction uses actual analytic orders, derivative order at each repeated zero, and Rolle zeros between consecutive roots.

A nonzero exponential polynomial with r distinct positive bases has at most r-1 real zeros counted with analytic multiplicity: induction after division and differentiation, including repeated roots.

### `four_term_zeros`

- Source: Appendix B.1; unnamed supporting assertion.
- Lean correspondence: `four_term_zeros_exp, four_term_zeros`.
- Status: **PROVED**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: The derivative after two positive exponential normalizations has strictly positive derivative; multiplicity-aware Rolle bounds recover the exact bound of two.

For signs +,-,-,+ and strictly increasing positive bases, F/b^s has derivative whose quotient by (d/b)^s is strictly increasing and has at most one simple zero. Thus F has at most two real zeros counted with multiplicity.

### `heavy_crossing_inputs`

- Source: Appendix B.2; unnamed supporting assertion.
- Lean correspondence: `strictMonoOn_heavyRoot, strictAntiOn_heavyLight, heavy_difference_four_term, heavy_difference_eventually_pos, heavy_difference_entropy_series`.
- Status: **PROVED**.
- Dependencies: `real_heavy_roots`, `entropy_difference`.
- Reformulation/equivalence/alternate proof: Actual implicit derivatives give the atom order; exponential normalization gives the eventual sign. The convergent entropy difference series forces a negative positive-integer value.

For k≤i<j, z_i<z_j and q_j<q_i. The heavy difference has four increasing bases with signs +,-,-,+, is zero at 0, positive eventually and negative at some positive integer by equal entropy.

### `light_heavy_order`

- Source: Appendix B.2; unnamed supporting assertion.
- Lean correspondence: `light_heavy_mass_order`.
- Status: **PROVED**.
- Dependencies: `entropy_roots`, `entropy`.
- Reformulation/equivalence/alternate proof: Strict q_m<y<z_m proved for every nonduplicate branch. A finite scalar strict-concavity argument replaces averaging a countable sequence.

For every nonduplicate heavy candidate, q_m<y<z_m. Strict entropy increase by averaging the remaining light-law atoms proves z_m>y; include a=0 and binary exclusion.

### `light_crossing_inputs`

- Source: Appendix B.2; unnamed supporting assertion.
- Lean correspondence: `heavy_strict_below_light_smallSamples, light_heavy_difference_entropy_series, light_heavy_single_zero_bound, light_heavy_double_zero_bound`.
- Status: **PROVED**.
- Dependencies: `cor:small-samples`, `entropy_difference`, `light_heavy_order`.
- Reformulation/equivalence/alternate proof: The full small-sample optimizer iff plus shape distinction proves both strict small-sample signs. Exact exponentials, including uniform and coincident-base cases, provide the appropriate multiplicity bound and eventual sign.

For nonduplicates b_m(1)<ℓ(1), b_m(2)<ℓ(2). When a=0 or q_m<a, increasing-base signs are +,-,+ or +,-,-,+. When q_m=a, combine the coefficient to (m-1)a>0. When 0<a<q_m, signs are +,-,+,-, eventual negativity and entropy equality force a positive integer value at j≥3.

### `finite_phase_reduction`

- Source: Appendix B.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.finite_phase_reduction`.
- Status: **TODO**.
- Dependencies: `thm:heavy-crossing`, `thm:light-crossing`, `lem:cutoff`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For T_m=τ_(m,m+1),R_m=max(m+1,ceil(hT_m+1)), m loses to m+1 when t>T_m. For 1≤t≤T_m, all j>R_m lose to R_m by the cutoff. Thus finitely many comparisons suffice; all endpoint ties are retained.

### `winning_multiplicity`

- Source: Appendix B.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.winning_multiplicity`.
- Status: **TODO**.
- Dependencies: `thm:heavy-crossing`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At fixed h, if i<j and b_j(t₁)≥b_i(t₁), then b_j(t₂)>b_i(t₂) for t₂>t₁. Therefore heavy winning multiplicities cannot decrease as integer sample size increases.

### `finite_slack`

- Source: Appendix C; unnamed supporting assertion.
- Lean correspondence: `ProbabilityVector.coord_pos_of_entropy_slack, deriv_eq_of_entropy_slack, finite_candidate_complete_saturated`.
- Status: **PROVED**.
- Dependencies: `atom_splitting`, `thm:exceptional`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: Unused-coordinate splitting forces full support under slack. Continuity makes the entropy bound inactive, and actual mass-preserving pair paths force equality of derivatives. Saturated cutoff competitors fit in the original finite alphabet.

On N≥2 symbols with h>0, every slack-entropy maximizer has full support; ordinary normalization stationarity yields equality of f′ at all positive sizes.

### `finite_polynomial`

- Source: Appendix C; unnamed supporting assertion.
- Lean correspondence: `finiteStationarity_iff_polynomial_zero, finiteStationarityPolynomial_ne_zero, natDegree_finiteStationarityPolynomial_le, card_finiteStationaryRoots_le`.
- Status: **PROVED**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: Exact denominator clearing, nonzero endpoint evaluation, degree at most t, and finite feasible root list of cardinal at most t. The uniform root is explicitly included.

The stationarity equation f′_t(z)=f′_t((1-z)/(N-1)) is equivalent on (0,1) to eq:finite-polynomial. That polynomial has degree≤t and is nonzero, since the derivative difference at z=1 is -2 for t=1 and -1 for t>1. Thus it has at most t roots; z=1/N is a root.

### `finite_list`

- Source: Appendix C; unnamed supporting assertion.
- Lean correspondence: `finite_alphabet_candidate_complete, exists_feasible_of_mem_finiteAlphabetValueList, finiteAlphabet_globalMax_iff`.
- Status: **PROVED**.
- Dependencies: `finite_slack`, `finite_polynomial`, `cutoff_discrete`, `zero_entropy`.
- Reformulation/equivalence/alternate proof: Every actual maximizer belongs to the source candidate list; every listed entry is feasible. Saturated support fitting is expressed by zero insertion and actual finite realization, preserving all zero-coordinate endpoints.

Keep saturated candidates with support≤N and all feasible stationary full-support candidates. Every maximizer belongs to this finite list; excluded heavy multiplicities are beaten by a smaller-support candidate. All listed candidates are feasible. Include N=1,h=0 and feasible full-support uniform laws.

### `log_certificate`

- Source: Appendix D; unnamed supporting assertion.
- Lean correspondence: `log_certificate, log_certificate_normalized, log_range_reduction`.
- Status: **PROVED**.
- Dependencies: `log_integral`.
- Reformulation/equivalence/alternate proof: Exact source remainder including the factor 2R+1, proved by integrating the remainder derivative and bounding its denominator. Integer power-of-two range reduction includes negative exponents.

For R≥1 and v=(y-1)/(y+1)∈[0,1/3], 0≤log y-2∑_{r<R}v^(2r+1)/(2r+1)≤2v^(2R+1)/((2R+1)(1-v²)); include y=2 for log 2. Scaling x=2^j y gives bounds with reversed endpoints if j<0.

### `objective_certificate`

- Source: Appendix D; unnamed supporting assertion.
- Lean correspondence: `objective_certificate, objective_certificate_nat`.
- Status: **PROVED**.
- Dependencies: `objective`.
- Reformulation/equivalence/alternate proof: Exact closed-bracket bounds, strengthened to real m≥1 and t≥0. branchObjective is exactly the manuscript formula; CandidateVectors gives the probability-vector bridge.

For integer m,t≥1 and 0≤a≤z≤b≤1, the lower and upper rational expressions in Appendix D bound V_(m,t)(z), respectively.

### `certificate_roots`

- Source: Appendix D; unnamed supporting assertion.
- Lean correspondence: `Certificates.index_0 through index_3, cutoff_0 through cutoff_3, all root_* theorems in CertificateRootData`.
- Status: **PROVED**.
- Dependencies: `log_certificate`, `entropy_roots`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: All 24 stored open brackets, the four entropy indices, and all cutoffs are verified from 101 kernel-checked rational logarithm enclosures. Generator Python only emits terms and proofs; norm_num and the Lean kernel validate the arithmetic, with no external oracle or native_decide.

All 24 stored brackets of width 10^(-30) contain their unique entropy roots; entropy indices and cutoffs for the four stored cases are correct and candidate lists are complete. Python is independent evidence; Lean must justify the logarithm bounds and rational computations.

### `nonunimodal`

- Source: Appendix D, eq:nonunimodal-example; unnamed supporting assertion.
- Lean correspondence: `Certificates.value_3_heavy_10, value_3_heavy_11, value_3_heavy_12, nonunimodal_example`.
- Status: **PROVED**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: All three strict decimal bounds and the strict valley hold for actual canonical heavy roots.

At h=19/8,t=8, b₁₀ is strictly between .456467562315 and .456467562316; b₁₁ between .455820123956 and .455820123957; b₁₂ between .457052010607 and .457052010608. Hence b₁₀>b₁₁<b₁₂.

### `certificate_winner14`

- Source: Appendix D; unnamed supporting assertion.
- Lean correspondence: `Certificates.unique_optimizer_3, optimal_value_3, global_value_19_8, root_3_heavy_14`.
- Status: **PROVED**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: All finite competitors are strictly worse than m=14; the exact global value and optimizer iff follow from the full classification. The heavy root has the displayed width-10^-30 bracket.

At h=19/8,t=8,M=20, the unique global winner is heavy m=14, .458686581808<B₈(19/8)<.458686581809, and its heavy atom lies between 343937132264853115880129584166/10³⁰ and the next numerator /10³⁰.

### `certificate_reentrance`

- Source: Appendix D; unnamed supporting assertion.
- Lean correspondence: `Certificates.unique_optimizer_0, unique_optimizer_1, unique_optimizer_2, heavy_maximum_0, heavy_maximum_1, heavy_maximum_2`.
- Status: **PROVED**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: Exact optimizer iffs certify light/heavy(m=3)/light. All six displayed decimal enclosures and three cutoffs are checked; the maximum over all heavy multiplicities is identified using the real cutoff theorem.

At t=3 and h=11/10,6/5,7/5 the unique winning types are respectively light,heavy(m=3),light; the six strict decimal intervals and cutoffs M=5,5,6 in the table hold.

### `thm:main`

- Source: Introduction; TeX label: `thm:main`.
- Lean correspondence: `ProbabilityVector.main_theorem`.
- Status: **PROVED**.
- Dependencies: `two_sizes`, `finite_support`, `attainment`, `entropy_saturation`.
- Reformulation/equivalence/alternate proof: One theorem combines all local structural, global attainment and infinite-alphabet saturation clauses for nonempty Countable alphabets, t≥1 and h≥0. The local structural and saturation components are stronger in alphabet generality. The true ℓ¹ feasible topology and ENNReal/real entropy bridge are retained.

Exact manuscript statement/display:

```tex
For every integer $t\ge1$ and $0\le h<\infty$, every local maximizer of
$\Phi_t$ on $\mathcal P_h(I)$, in the $\ell^1$ topology, has at most two
atom sizes and has finite support. The maximum is attained. If $I$ is
countably infinite, every local maximizer satisfies $H(p)=h$.
```

### `lem:entropy`

- Source: The three-coordinate reduction; TeX label: `lem:entropy`.
- Lean correspondence: `Curvature.entropy_curvature`.
- Status: **PROVED**.
- Dependencies: `curvature_algebra`, `uniform_curvature`.
- Reformulation/equivalence/alternate proof: Actual convergent source integrals for every positive triple, including repeated coordinates. Both iff equality clauses are proved. The simplex law is constructed as a barycentric pushforward of the weighted unit square; all tilt/Fubini/moment identities are checked.

Exact manuscript statement/display:

```tex
For every positive triple,
\begin{equation}\label{eq:entropy-bound}
 0<m\le S/3,\qquad \K\ge\frac{16}{15(S+m)}.
\end{equation}
Equality in $m\le S/3$, or in the lower bound for $\K$, holds if and only
if $x=y=z$.
```

### `lem:coefficient-extremum`

- Source: The finite coefficient comparison; TeX label: `lem:coefficient-extremum`.
- Lean correspondence: `coefficient_extremum, coefficientDifference_eq`.
- Status: **PROVED**.
- Dependencies: `coefficient_transfer`, `coefficient_boundary`.
- Reformulation/equivalence/alternate proof: Exact all-degree bound for all cube points with positive sigma, including zero/repeated/boundary coordinates. Discrete pair-transfer recurrence replaces derivative/first-zero proof; stronger zero-last endpoint bound avoids separate sigma>=2 exclusion.

Exact manuscript statement/display:

```tex
If $r\in[0,1]^3$ and $\sigma=3-\sum_i r_i>0$, then
\begin{equation}\label{eq:b-bound}
 b_j:=h_j(r)-h_{j-1}(r)\le C_\sigma:=\max\{1,\sigma^{-1}\}
 \qquad(j\ge0).
\end{equation}
```

### `lem:comparison`

- Source: The finite coefficient comparison; TeX label: `lem:comparison`.
- Lean correspondence: `coefficient_comparison_series, comparisonSeriesCoefficient_eq, homogeneousSeries_eq_product_inverse`.
- Status: **PROVED**.
- Dependencies: `comparison_telescoping`.
- Reformulation/equivalence/alternate proof: Exact manuscript assumptions and strict bound at all n including negative-index coefficient zero. Formal-series identity bridges the finite convolution. Discrete middle concavity and Turan replace real exponential interpolation.

Exact manuscript statement/display:

```tex
Let $\beta>q_1>q_2>q_3>0$, $\alpha>0$, and $n\ge0$ be an integer.
Write $G=G_q$, $k_j=h_j(q)-\alpha h_{j-1}(q)$, and suppose
$k_n>0$, $k_{n+1}\ge\beta k_n$. Then
\begin{equation}\label{eq:coefficient}
\begin{aligned}
 J&:=[w^{n-1}](1-\alpha w)(1-\beta w)^2G(w)^2\\
  &<\max\left\{\frac1\beta,\frac1{3\beta-\sum_iq_i}\right\}k_n,
\end{aligned}
\end{equation}
where negative-index coefficients are zero.
```

### `lem:repeated`

- Source: One exceptional atom and a finite classification; TeX label: `lem:repeated`.
- Lean correspondence: `ProbabilityVector.repeated_size_criterion, repeated_size_criterion_finite, repeated_size_criterion_of_localMax`.
- Status: **PROVED**.
- Dependencies: `repeated_variation`, `weighted_log_average`.
- Reformulation/equivalence/alternate proof: Actual finite-coordinate local maximality for general scalar objectives, with the finite and countable bridges. Alternate proof uses entropy-decreasing quadratic paths and a limit to the critical acceleration; no stationarity or multiplier conclusion is assumed.

Exact manuscript statement/display:

```tex
Let $f\in C[0,1]\cap C^2(0,1)$, and let $J\subset(0,1)$ be an interval
containing every $u$ for which $f''(u)\le0$. Suppose that $g(u)=uf''(u)$
satisfies
\begin{equation}\label{eq:strict-quasiconvex}
 g(v)<\max\{g(x),g(y)\}\qquad(x<v<y,\quad x,y\in J).
\end{equation}
At a finite-dimensional local maximum of $\sum_i f(p_i)$ under normalization
and an upper Shannon-entropy constraint, at most one distinct positive
coordinate value can occur more than once. The same conclusion holds on a
countable alphabet whenever the objective is well-defined and the point is
locally maximal under finite-coordinate perturbations.
```

### `thm:exceptional`

- Source: One exceptional atom and a finite classification; TeX label: `thm:exceptional`.
- Lean correspondence: `ProbabilityVector.exceptional_form_of_localMax`.
- Status: **PROVED**.
- Dependencies: `thm:main`, `lem:repeated`, `quasiconvex`, `shape_boundaries`.
- Reformulation/equivalence/alternate proof: Every actual nonuniform local maximum on an arbitrary alphabet equals a zero extension of the displayed candidate vector, with positive natural multiplicity and z in (0,1) unequal to the repeated size. Ordering gives the light/heavy dichotomy.

Exact manuscript statement/display:

```tex
Under the hypotheses of Theorem~\ref{thm:main}, every nonuniform local
maximizer has, up to permutation and zero coordinates, the form
\begin{equation}\label{eq:exceptional-form}
 p_m(z)=\left(z,\underbrace{q,\ldots,q}_{m\text{ copies}}\right),
 \qquad q=\frac{1-z}{m},\quad m\in\mathbb N,\quad 0<z<1.
\end{equation}
Thus either $z<q$ (one light atom) or $z>q$ (one heavy atom).
```

### `lem:cutoff`

- Source: One exceptional atom and a finite classification; TeX label: `lem:cutoff`.
- Lean correspondence: `heavy_cutoff`.
- Status: **PROVED**.
- Dependencies: `heavy_derivative`, `heavy_cutoff_sign`.
- Reformulation/equivalence/alternate proof: Actual derivative of the uniquely defined real-multiplicity heavy root and real-exponent objective is strictly negative throughout the stated domain, including s=1.

Exact manuscript statement/display:

```tex
Fix $h>0$ and a real exponent $s\ge1$. Interpolate the heavy formulas by
allowing $m>e^h-1$ to be real and taking the unique root
$E_m(z_m)=h$ with $z_m>1/(m+1)$. Then
\begin{equation}\label{eq:cutoff-decrease}
 \frac{\dd}{\dd m}b_m(s)<0\qquad\text{whenever }m\ge sh+1.
\end{equation}
```

### `thm:finite-classification`

- Source: One exceptional atom and a finite classification; TeX label: `thm:finite-classification`.
- Lean correspondence: `optimalValue_eq_finiteCandidateMaximum, ProbabilityVector.globalMax_iff_finite_candidate, ProbabilityVector.support_card_le_candidateCutoff`.
- Status: **PROVED**.
- Dependencies: `candidate_completeness`, `cutoff_discrete`, `attainment`.
- Reformulation/equivalence/alternate proof: optimalValue is the genuine supremum over all feasible countable distributions. The finite max includes k through max(k,ceil(th+1)); the iff retains all ties and zero-coordinate embeddings, and the support bound is proved.

Exact manuscript statement/display:

```tex
For integer $t\ge1$ and $h>0$, put
\begin{equation}\label{eq:M-cutoff}
 M=M(t,h)=\max\{k,\lceil th+1\rceil\},\qquad k=\lfloor e^h\rfloor.
\end{equation}
Then
\begin{equation}\label{eq:finite-maximum}
 B_t(h)=\max\{\ell(t),b_k(t),b_{k+1}(t),\ldots,b_M(t)\}.
\end{equation}
Up to permutation and zero coordinates, the global maximizers are exactly
the candidates in this list attaining the displayed maximum. In particular,
every global maximizer has at most $M+1$ positive coordinates.
```

### `cor:small-samples`

- Source: One exceptional atom and a finite classification; TeX label: `cor:small-samples`.
- Lean correspondence: `ProbabilityVector.globalMax_iff_lightCandidateForm_smallSamples, ProbabilityVector.optimalValue_eq_lightValue_smallSamples`.
- Status: **PROVED**.
- Dependencies: `small_samples_hessian`, `small_samples_scalar`, `candidate_completeness`, `attainment`.
- Reformulation/equivalence/alternate proof: Exact optimizer iff on every countably infinite alphabet and equality of the genuine supremum to the canonical light value. Heavy multiplicity at least two is excluded by an actual feasible three-coordinate variation; the binary duplicate is explicitly reindexed.

Exact manuscript statement/display:

```tex
For $t=1$ and $t=2$, the unique global maximizer on a countably infinite
alphabet, up to permutation and zero coordinates, is $p_{\rm L}$.
Equivalently, $B_t(h)=\ell(t)$ for $h>0$.
```

### `thm:asymptotics`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `thm:asymptotics`.
- Lean correspondence: `thm_asymptotics, ProbabilityVector.globalMax_optimizer_scales_uniform`.
- Status: **PROVED**.
- Dependencies: `reciprocal_upper`, `reciprocal_lower`, `eventually_heavy`, `optimizer_scales`.
- Reformulation/equivalence/alternate proof: Actual optimalValue IsBigO expansion along natural sample sizes, eventual heaviness, and explicit epsilon bounds with one common threshold for every maximizing m,z and actual probability law. This is the uniform meaning of all three source asymptotic equivalences.

Exact manuscript statement/display:

```tex
As integer $t\to\infty$,
\begin{equation}\label{eq:sharp-asymptotic}
 \frac{h}{B_t(h)}
 =\log t+\log\log t+2
  +O_h\!\left(\frac{\log\log t}{\log t}\right).
\end{equation}
Every global maximizer is eventually one-heavy. Writing any such maximizer
as
\[
 p_t=\left(1-L_t,
       \underbrace{q_t,\ldots,q_t}_{m_t\text{ copies}}\right),
 \qquad m_tq_t=L_t,
\]
we have, uniformly over the choice of a maximizer,
\begin{equation}\label{eq:optimizer-scales}
 L_t\sim\frac h{\log t},\qquad
 q_t\sim\frac1{t\log t},\qquad
 m_t\sim ht.
\end{equation}
```

### `cor:sample-complexity`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `cor:sample-complexity`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.cor_sample_complexity`.
- Status: **TODO**.
- Dependencies: `asymptotic_inversion`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
For fixed $h>0$, define
\[
 N_h(\varepsilon)=\min\{t\in\mathbb N:B_t(h)\le\varepsilon\}.
\]
Then
\begin{equation}\label{eq:sample-complexity}
 N_h(\varepsilon)\sim
 \frac{\varepsilon}{e^2h}\exp\!\left(\frac h\varepsilon\right)
 \qquad(\varepsilon\downarrow0).
\end{equation}
```

### `cor:occupancy`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `cor:occupancy`.
- Lean correspondence: `singleton_expectation_max, discovery_expectation_max, coverage_expectation_min, singleton_optimizer_iff_finite_candidate, discovery_optimizer_iff_finite_candidate, coverage_optimizer_iff_finite_candidate`.
- Status: **PROVED**.
- Dependencies: `occupancy_identities`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: Actual IID probability product laws and ordinary Bochner expectations. The attained extrema are IsGreatest/IsLeast of actual expectation images, with complete optimizer iffs. The new observation is coordinate zero and prior observations are successor coordinates, a relabeling of the IID samples.

Exact manuscript statement/display:

```tex
Let $K_n$ be the number of distinct symbols in $n$ independent samples,
let $K_{n,1}$ be the number occurring exactly once, and let $C_n$ be the
probability mass of the observed symbols. Then
\begin{equation}\label{eq:occupancy-extrema}
 \begin{aligned}
 \max_{H(p)\le h}\EE_p K_{n,1}&=nB_{n-1}(h) &&(n\ge2),\\
 \max_{H(p)\le h}\EE_p(K_{t+1}-K_t)&=B_t(h) &&(t\ge1),\\
 \min_{H(p)\le h}\EE_p C_t&=1-B_t(h) &&(t\ge1).
 \end{aligned}
\end{equation}
The optimizers are exactly those in Theorem~\ref{thm:finite-classification},
with the corresponding sample-size index.
```

### `lem:entropy-series`

- Source: Crossing structure of the candidate family; TeX label: `lem:entropy-series`.
- Lean correspondence: `ProbabilityVector.entropy_series, hasSum_objective_sub_div_zero, summable_abs_objective_sub_div`.
- Status: **PROVED**.
- Dependencies: `entropy_log_series`.
- Reformulation/equivalence/alternate proof: Explicit manuscript theorem and both finite-equal-entropy consequences. n:ℕ indexes j=n+1, so the denominator and objective index match exactly. Arbitrary index types strengthen finite/countable scope.

Exact manuscript statement/display:

```tex
For every discrete probability distribution,
\begin{equation}\label{eq:entropy-series}
 H(p)=\sum_{j=1}^\infty\frac{\Phi_j(p)}j,
\end{equation}
with equality in $[0,\infty]$. In particular, if two distributions have
the same finite entropy, the weighted series of the differences of their
$\Phi_j$ values converges absolutely and sums to zero.
```

### `lem:zero-count`

- Source: Crossing structure of the candidate family; TeX label: `lem:zero-count`.
- Lean correspondence: `exponential_sum_zeros_rpow, four_term_zeros`.
- Status: **PROVED**.
- Dependencies: `rolle_multiplicity`, `four_term_zeros`.
- Reformulation/equivalence/alternate proof: ZeroMultiplicityBound asserts finiteness of the entire real zero set and bounds the sum of actual analyticOrderAt multiplicities in ENat, including repeated roots. The nonzero-function assumption permits zero coefficients and is stronger than the source version.

Exact manuscript statement/display:

```tex
A nonzero sum of $r$ exponentials with distinct positive bases has at most
$r-1$ real zeros, counted with multiplicity. If
\[
 F(s)=Aa^s-Bb^s-Cc^s+Dd^s,
 \qquad 0<a<b<c<d,\quad A,B,C,D>0,
\]
then $F$ has at most two real zeros, counted with multiplicity.
```

### `thm:heavy-crossing`

- Source: Crossing structure of the candidate family; TeX label: `thm:heavy-crossing`.
- Lean correspondence: `heavy_heavy_single_crossing`.
- Status: **PROVED**.
- Dependencies: `heavy_crossing_inputs`, `lem:zero-count`.
- Reformulation/equivalence/alternate proof: Exact entire real zero set {0,τ}, τ>1, both analytic multiplicities one, and strict signs on both positive intervals. Actual real-exponent canonical heavy families; no sign or crossing premise is assumed.

Exact manuscript statement/display:

```tex
For each pair of integers $k\le i<j$, there is a unique positive crossing
$\tau_{ij}>1$. It is simple, and
\begin{equation}\label{eq:heavy-crossing-sign}
 \begin{cases}
 b_j(s)<b_i(s),&0<s<\tau_{ij},\\
 b_j(s)>b_i(s),&s>\tau_{ij}.
 \end{cases}
\end{equation}
```

### `thm:light-crossing`

- Source: Crossing structure of the candidate family; TeX label: `thm:light-crossing`.
- Lean correspondence: `light_heavy_single_crossing, light_heavy_double_crossing, binary_heavy_lightRealValue_eq`.
- Status: **PROVED**.
- Dependencies: `light_crossing_inputs`, `lem:zero-count`.
- Reformulation/equivalence/alternate proof: Single and double crossing cases partition the source domain. Exact zero sets, analytic simplicity, endpoints above two, all strict signs and binary exclusion are explicit.

Exact manuscript statement/display:

```tex
Fix $m\ge k$ such that $p_m^{\rm H}$ is not the binary duplicate of
$p_{\rm L}$. There are endpoints
$2<\alpha_m<\beta_m\le\infty$ such that
\begin{equation}\label{eq:light-crossing-sign}
 b_m(s)>\ell(s)\quad\Longleftrightarrow\quad
 \alpha_m<s<\beta_m\qquad(s>0).
\end{equation}
More precisely, if $p_{\rm L}$ is uniform or $q_m\le a$, then
$\beta_m=\infty$ and $\alpha_m$ is the unique positive zero of
$b_m-\ell$. If $0<a<q_m$, then $\alpha_m$ and $\beta_m$ are its
exactly two positive zeros. Every finite positive crossing is simple;
outside the closed interval the inequality in~\eqref{eq:light-crossing-sign}
is strictly reversed.
```

### `cor:phase-intervals`

- Source: Crossing structure of the candidate family; TeX label: `cor:phase-intervals`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.cor_phase_intervals`.
- Status: **TODO**.
- Dependencies: `finite_phase_reduction`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
For integer $t\ge1$, the heavy distribution $p_m^{\rm H}$ is globally
optimal if and only if
\begin{equation}\label{eq:heavy-phase}
 \underline{s}_m\le t\le\overline{s}_m.
\end{equation}
If the lower endpoint exceeds the upper endpoint, this multiplicity never
wins. The light or uniform candidate is globally optimal if and only if
\begin{equation}\label{eq:light-phase}
 t\notin
 \bigcup_{\substack{k\le m\le M(t,h)\\p_m^{\rm H}\ne p_{\rm L}}}
       (\alpha_m,\beta_m),
\end{equation}
where equality or inequality of distributions is understood up to
permutation and zero coordinates. All endpoint ties are included.
```

### `thm:finite-alphabet`

- Source: A fixed finite alphabet; TeX label: `thm:finite-alphabet`.
- Lean correspondence: `finiteAlphabetOptimalValue_eq_max, finiteAlphabet_globalMax_iff, finiteAlphabetOptimalValue_zero, finiteAlphabetOptimalValue_one, finiteAlphabet_globalMax_zero_iff`.
- Status: **PROVED**.
- Dependencies: `finite_list`, `attainment`.
- Reformulation/equivalence/alternate proof: The actual finite-alphabet supremum equals a finite maximum, and tied optimizers satisfy an exact iff. Saturated entries are filtered by actual realization on N symbols (no optimality condition); this preserves the full-support uniform endpoint despite the extra zero in its light parametrization. Stationary roots form the exact feasible polynomial-root list. All N=1 and h=0 clauses are included.

Exact manuscript statement/display:

```tex
The maximum $B_{t,N}(h)$ is the largest objective value in the finite list
just described. Up to permutation, its maximizing vectors are exactly the
candidates attaining that value.
```

### `eq:entropy-derivatives`

- Source: The three-coordinate reduction; TeX label: `eq:entropy-derivatives`.
- Lean correspondence: `TripleGeometry.hasDerivAt_localEntropy_E, hasDerivAt_localEntropy_P`.
- Status: **PROVED**.
- Dependencies: `entropy_hessian`.
- Reformulation/equivalence/alternate proof: Exact directional partial derivatives at fixed S in the actual inverse-root chart.

Exact manuscript statement/display:

```tex
\HH_E=I_1,\qquad \HH_P=I_0.
```

### `eq:curve`

- Source: The three-coordinate reduction; TeX label: `eq:curve`.
- Lean correspondence: `hasDerivAt_P_of_entropy_path, hasDerivAt_deriv_entropyCurve_product`.
- Status: **PROVED**.
- Dependencies: `entropy_curve`.
- Reformulation/equivalence/alternate proof: Exact displayed quantities are linked to the source definitions and actual curve derivatives in the owning proof units; strict inequalities and degree-zero boundary are preserved.

Exact manuscript statement/display:

```tex
P'=-m,\qquad P''=\K.
```

### `eq:entropy-bound`

- Source: The three-coordinate reduction; TeX label: `eq:entropy-bound`.
- Lean correspondence: `Curvature.entropy_curvature`.
- Status: **PROVED**.
- Dependencies: `lem:entropy`.
- Reformulation/equivalence/alternate proof: Exact displayed quantities are linked to the source definitions and actual curve derivatives in the owning proof units; strict inequalities and degree-zero boundary are preserved.

Exact manuscript statement/display:

```tex
0<m\le S/3,\qquad \K\ge\frac{16}{15(S+m)}.
```

### `eq:variations`

- Source: The three-coordinate reduction; TeX label: `eq:variations`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_variations`.
- Status: **TODO**.
- Dependencies: `entropy_curve`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{aligned}
 \phi'&=\mathcal D_t:=(F_t)_E-m(F_t)_P,\\
 \phi''&=\mathcal C_t:=(F_t)_{EE}-2m(F_t)_{EP}
                  +m^2(F_t)_{PP}+\K(F_t)_P.
\end{aligned}
```

### `eq:target`

- Source: The three-coordinate reduction; TeX label: `eq:target`.
- Lean correspondence: `not_localMax_three_sizes_of_curvature_bound, coefficient_curvature_gap`.
- Status: **PROVED**.
- Dependencies: `curvature_contradiction`.
- Reformulation/equivalence/alternate proof: Exact displayed quantities are linked to the source definitions and actual curve derivatives in the owning proof units; strict inequalities and degree-zero boundary are preserved.

Exact manuscript statement/display:

```tex
\mathcal D_t=0,\quad R_t>0,\quad S\le1
 \quad\Longrightarrow\quad \mathcal C_t>0,
```

### `eq:turan`

- Source: The finite coefficient comparison; TeX label: `eq:turan`.
- Lean correspondence: `homogeneous3_turan_all, homogeneous3_turan_nonneg`.
- Status: **PROVED**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: Exact identity at every natural index, with previousHomogeneous3 zero at index zero.

Exact manuscript statement/display:

```tex
h_j(r)^2-h_{j-1}(r)h_{j+1}(r)
 =h_j(r_1r_2,r_1r_3,r_2r_3)\ge0\qquad(j\ge0).
```

### `eq:b-bound`

- Source: The finite coefficient comparison; TeX label: `eq:b-bound`.
- Lean correspondence: `coefficient_extremum, coefficientDifference_eq`.
- Status: **PROVED**.
- Dependencies: `lem:coefficient-extremum`.
- Reformulation/equivalence/alternate proof: Natural index with previous coefficient zero at index zero is exact; sigma=3-x-y-z is definitionally expanded.

Exact manuscript statement/display:

```tex
b_j:=h_j(r)-h_{j-1}(r)\le C_\sigma:=\max\{1,\sigma^{-1}\}
 \qquad(j\ge0).
```

### `eq:coefficient`

- Source: The finite coefficient comparison; TeX label: `eq:coefficient`.
- Lean correspondence: `coefficient_comparison_series, comparisonCoefficient_eq_coeff`.
- Status: **PROVED**.
- Dependencies: `lem:comparison`.
- Reformulation/equivalence/alternate proof: Exact formal coefficient of (1-alpha*w)(1-beta*w)^2 G^2 with source negative-index convention.

Exact manuscript statement/display:

```tex
\begin{aligned}
 J&:=[w^{n-1}](1-\alpha w)(1-\beta w)^2G(w)^2\\
  &<\max\left\{\frac1\beta,\frac1{3\beta-\sum_iq_i}\right\}k_n,
\end{aligned}
```

### `eq:derivatives`

- Source: Completion of the two-size proof; TeX label: `eq:derivatives`.
- Lean correspondence: `hasDerivAt_localObjective_P, hasDerivAt_objective_path, hasDerivAt_deriv_objective_entropyCurve`.
- Status: **PROVED**.
- Dependencies: `objective_curvature`.
- Reformulation/equivalence/alternate proof: Exact displayed quantities are linked to the source definitions and actual curve derivatives in the owning proof units; strict inequalities and degree-zero boundary are preserved.

Exact manuscript statement/display:

```tex
\begin{aligned}
 R_t&=(t+1)k_n,\\
 \mathcal D_t&=(t+1)(k_{n+1}-\beta k_n),\\
 \mathcal C_t&=(t+1)(\K k_n-J).
\end{aligned}
```

### `eq:positive-curvature`

- Source: Completion of the two-size proof; TeX label: `eq:positive-curvature`.
- Lean correspondence: `coefficient_curvature_ratio_gap, coefficient_curvature_twentieth_gap`.
- Status: **PROVED**.
- Dependencies: `curvature_contradiction`.
- Reformulation/equivalence/alternate proof: Exact displayed quantities are linked to the source definitions and actual curve derivatives in the owning proof units; strict inequalities and degree-zero boundary are preserved.

Exact manuscript statement/display:

```tex
\frac{\mathcal C_t}{R_t}=\K-\frac J{k_n}
 >\frac1{15(S+m)}>0.
```

### `eq:strict-quasiconvex`

- Source: One exceptional atom and a finite classification; TeX label: `eq:strict-quasiconvex`.
- Lean correspondence: `weightedCurvature_strict_quasiconvex_on_interval`.
- Status: **PROVED**.
- Dependencies: `lem:repeated`.
- Reformulation/equivalence/alternate proof: Exact three-point strict inequality on the actual nonpositive-curvature interval; alternate proof uses the decreasing derivative quadratic without solving its roots.

Exact manuscript statement/display:

```tex
g(v)<\max\{g(x),g(y)\}\qquad(x<v<y,\quad x,y\in J).
```

### `eq:log-average`

- Source: One exceptional atom and a finite classification; TeX label: `eq:log-average`.
- Lean correspondence: `weighted_log_average`.
- Status: **PROVED**.
- Dependencies: `weighted_log_average`.
- Reformulation/equivalence/alternate proof: The exact integral/secant display is checked; the eliminated multiplier is its defining negative logarithmic secant.

Exact manuscript statement/display:

```tex
-\mu=\frac{f'(y)-f'(x)}{\log(y/x)}
 =\frac{\displaystyle\int_x^y g(u)\,\frac{\dd u}{u}}
        {\log(y/x)}.
```

### `eq:exceptional-form`

- Source: One exceptional atom and a finite classification; TeX label: `eq:exceptional-form`.
- Lean correspondence: `ProbabilityVector.exceptional_form_of_localMax`.
- Status: **PROVED**.
- Dependencies: `thm:exceptional`.
- Reformulation/equivalence/alternate proof: Exact coordinate representation via candidateVector and zeroExtend; no numerical or conditional representation.

Exact manuscript statement/display:

```tex
p_m(z)=\left(z,\underbrace{q,\ldots,q}_{m\text{ copies}}\right),
 \qquad q=\frac{1-z}{m},\quad m\in\mathbb N,\quad 0<z<1.
```

### `eq:branch-functions`

- Source: One exceptional atom and a finite classification; TeX label: `eq:branch-functions`.
- Lean correspondence: `branchEntropy, branchObjective, entropy_candidateVector, objective_candidateVector, lightRealValue, lightRealValue_nat, heavyValue_eq, heavyValue_integer_eq`.
- Status: **PROVED**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: Exact entropy and integer objective formulas are realized by actual finite/countable probability laws. The real-power candidate continuations agree at every natural exponent.

Exact manuscript statement/display:

```tex
\begin{aligned}
 E_m(z)&=-z\log z-(1-z)\log\frac{1-z}{m},\\
 V_{m,s}(z)&=z(1-z)^s+(1-z)\left(1-\frac{1-z}{m}\right)^s.
 \end{aligned}
```

### `eq:entropy-branch-derivative`

- Source: One exceptional atom and a finite classification; TeX label: `eq:entropy-branch-derivative`.
- Lean correspondence: `hasDerivAt_branchEntropy, deriv_branchEntropy`.
- Status: **PROVED**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: Exact derivative, on m>0 and 0<z<1; endpoint continuity handled separately.

Exact manuscript statement/display:

```tex
E_m'(z)=\log\frac{1-z}{mz},
```

### `eq:light-candidate`

- Source: One exceptional atom and a finite classification; TeX label: `eq:light-candidate`.
- Lean correspondence: `canonicalLight, lightRoot_spec, lightRepeated, lightRealValue, objective_canonicalLight`.
- Status: **PROVED**.
- Dependencies: `entropy_roots`.
- Reformulation/equivalence/alternate proof: Canonical vector, repeated mass, unique light entropy root and real-exponent objective reproduce the display, including a=0.

Exact manuscript statement/display:

```tex
p_{\rm L}=p_k(a),\qquad y=\frac{1-a}{k},\qquad
 \ell(s)=V_{k,s}(a).
```

### `eq:heavy-candidates`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-candidates`.
- Lean correspondence: `canonicalHeavy, heavyRoot_spec, heavyLight, heavyValue_eq, objective_canonicalHeavy`.
- Status: **PROVED**.
- Dependencies: `entropy_roots`.
- Reformulation/equivalence/alternate proof: Canonical vector, repeated mass, unique heavy entropy root and real-exponent objective reproduce the display.

Exact manuscript statement/display:

```tex
q_m=\frac{1-z_m}{m},\qquad
 p_m^{\rm H}=p_m(z_m),\qquad b_m(s)=V_{m,s}(z_m).
```

### `eq:cutoff-decrease`

- Source: One exceptional atom and a finite classification; TeX label: `eq:cutoff-decrease`.
- Lean correspondence: `heavy_cutoff`.
- Status: **PROVED**.
- Dependencies: `lem:cutoff`.
- Reformulation/equivalence/alternate proof: Exact derivative inequality for the canonical smooth real heavy family.

Exact manuscript statement/display:

```tex
\frac{\dd}{\dd m}b_m(s)<0\qquad\text{whenever }m\ge sh+1.
```

### `eq:heavy-entropy-sigma`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-entropy-sigma`.
- Lean correspondence: `heavy_entropy_sigma`.
- Status: **PROVED**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: Exact identity, derived from the unique root equation.

Exact manuscript statement/display:

```tex
h=-\log z+(1-z)\sigma.
```

### `eq:heavy-m-derivatives`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-m-derivatives`.
- Lean correspondence: `hasDerivAt_heavyRoot, hasDerivAt_heavyLight`.
- Status: **PROVED**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: Both actual derivative identities, including their signs from heavy_parameters_pos.

Exact manuscript statement/display:

```tex
\frac{\dd z}{\dd m}=\frac q\sigma,
 \qquad
 \frac{\dd q}{\dd m}=-\frac{q(1+\sigma)}{m\sigma}.
```

### `eq:heavy-objective-derivative`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-objective-derivative`.
- Lean correspondence: `hasDerivAt_heavyValue`.
- Status: **PROVED**.
- Dependencies: `heavy_derivative`.
- Reformulation/equivalence/alternate proof: Exact real-exponent derivative and heavyPsi definition.

Exact manuscript statement/display:

```tex
\frac{\dd b_m(s)}{\dd m}=\frac q\sigma\Psi_s(z,q),\qquad
 \Psi_s(z,q)=f_s'(z)-f_s'(q)+sq\sigma(1-q)^{s-1}.
```

### `eq:M-cutoff`

- Source: One exceptional atom and a finite classification; TeX label: `eq:M-cutoff`.
- Lean correspondence: `candidateCutoff, index_le_candidateCutoff, sample_entropy_le_candidateCutoff`.
- Status: **PROVED**.
- Dependencies: `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: Natural ceiling equals the mathematical ceiling on this positive domain; cutoff is the exact displayed maximum.

Exact manuscript statement/display:

```tex
M=M(t,h)=\max\{k,\lceil th+1\rceil\},\qquad k=\lfloor e^h\rfloor.
```

### `eq:finite-maximum`

- Source: One exceptional atom and a finite classification; TeX label: `eq:finite-maximum`.
- Lean correspondence: `optimalValue_eq_finiteCandidateMaximum`.
- Status: **PROVED**.
- Dependencies: `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: Genuine global supremum equals max of the canonical finite candidate values.

Exact manuscript statement/display:

```tex
B_t(h)=\max\{\ell(t),b_k(t),b_{k+1}(t),\ldots,b_M(t)\}.
```

### `eq:small-sample-hessian`

- Source: One exceptional atom and a finite classification; TeX label: `eq:small-sample-hessian`.
- Lean correspondence: `ProbabilityVector.repeated_pair_weighted_bound, ProbabilityVector.repeatedPairHessian_nonpos_of_localMax`.
- Status: **PROVED**.
- Dependencies: `small_samples_hessian`.
- Reformulation/equivalence/alternate proof: The source multiplier is represented by its explicit logarithmic secant; the necessary inequality follows from feasible quadratic paths without introducing a Lagrange multiplier.

Exact manuscript statement/display:

```tex
qf_t''(q)+\mu\le0,\qquad
 \mu=\frac{f_t'(q)-f_t'(z)}{\log r},
```

### `eq:sharp-asymptotic`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:sharp-asymptotic`.
- Lean correspondence: `optimalValue_sharp_asymptotic`.
- Status: **PROVED**.
- Dependencies: `thm:asymptotics`.
- Reformulation/equivalence/alternate proof: Exact reciprocal expansion with IsBigO error at the natural-number atTop filter.

Exact manuscript statement/display:

```tex
\frac{h}{B_t(h)}
 =\log t+\log\log t+2
  +O_h\!\left(\frac{\log\log t}{\log t}\right).
```

### `eq:optimizer-scales`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:optimizer-scales`.
- Lean correspondence: `optimizer_scales_uniform, ProbabilityVector.globalMax_optimizer_scales_uniform`.
- Status: **PROVED**.
- Dependencies: `optimizer_scales`.
- Reformulation/equivalence/alternate proof: All three source equivalences have their exact uniform epsilon meaning.

Exact manuscript statement/display:

```tex
L_t\sim\frac h{\log t},\qquad
 q_t\sim\frac1{t\log t},\qquad
 m_t\sim ht.
```

### `eq:L-entropy-objective`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:L-entropy-objective`.
- Lean correspondence: `heavy_tail_entropy, heavy_tail_objective`.
- Status: **PROVED**.
- Dependencies: `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: Exact substitution z=1-L in the entropy and objective formulas.

Exact manuscript statement/display:

```tex
\begin{aligned}
 h&=-(1-L)\log(1-L)-L\log q,\\
 \Phi_t(p)&=(1-L)L^t+L(1-q)^t.
 \end{aligned}
```

### `eq:A-L`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:A-L`.
- Lean correspondence: `entropyTailCorrection_expansion, entropyTailCorrection_remainder_bound`.
- Status: **PROVED**.
- Dependencies: `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: Quantified remainder bound implies precisely A(L)=1-L/2+O(L²) as L decreases to zero.

Exact manuscript statement/display:

```tex
A(L)=-\frac{1-L}{L}\log(1-L)
     =1-\frac L2+O(L^2)\qquad(L\downarrow0).
```

### `eq:d-lower-candidate`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:d-lower-candidate`.
- Lean correspondence: `rounded_entropy_scale_nat_expansion`.
- Status: **PROVED**.
- Dependencies: `asymptotic_lower`.
- Reformulation/equivalence/alternate proof: Exact canonical rounded multiplicity and entropy root satisfy the displayed d expansion.

Exact manuscript statement/display:

```tex
d=T+\log T+1+O_h\!\left(\frac{\log T}{T}\right).
```

### `eq:reciprocal-upper`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:reciprocal-upper`.
- Lean correspondence: `asymptotic_reciprocal_upper`.
- Status: **PROVED**.
- Dependencies: `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: Actual optimalValue, with a quantified eventual error at the source scale.

Exact manuscript statement/display:

```tex
\begin{aligned}
 \frac h{B_t(h)}
 &\le d\exp\!\left(\frac1d+O_h\!\left(\frac1{tT}\right)\right)\\
 &=T+\log T+2+O_h\!\left(\frac{\log T}{T}\right).
 \end{aligned}
```

### `eq:optimizer-d`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:optimizer-d`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_optimizer_d`.
- Status: **TODO**.
- Dependencies: `optimizer_bounds`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
d=T-\log u+1+O_h(T^{-1}).
```

### `eq:reciprocal-uniform`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:reciprocal-uniform`.
- Lean correspondence: `heavy_competitive_reciprocal_lower_strong, optimalHeavy_eventually_estimates`.
- Status: **PROVED**.
- Dependencies: `reciprocal_lower`.
- Reformulation/equivalence/alternate proof: Stronger explicit lower bound retains the scalar gap uniformly over every maximizing heavy root.

Exact manuscript statement/display:

```tex
\frac h{B_t(h)}
 \ge de^u-O_h(T^2\rho_h^t)
 =de^u-o_h(T^{-1}).
```

### `eq:scalar-gap`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:scalar-gap`.
- Lean correspondence: `heavy_scalar_gap_strong, scalarGap_coercive`.
- Status: **PROVED**.
- Dependencies: `reciprocal_lower`.
- Reformulation/equivalence/alternate proof: Exact nonnegative scalar gap v-log(v)-1 and uniform coercivity at v=1 are checked.

Exact manuscript statement/display:

```tex
\begin{aligned}
 de^u&\ge d+Tu\\
 &\ge T+\log T+1+v-\log v-O_h(T^{-1})\\
 &\ge T+\log T+2-O_h(T^{-1}),
 \end{aligned}
```

### `eq:sample-complexity`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:sample-complexity`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_sample_complexity`.
- Status: **TODO**.
- Dependencies: `cor:sample-complexity`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
N_h(\varepsilon)\sim
 \frac{\varepsilon}{e^2h}\exp\!\left(\frac h\varepsilon\right)
 \qquad(\varepsilon\downarrow0).
```

### `eq:occupancy-extrema`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:occupancy-extrema`.
- Lean correspondence: `singleton_expectation_max, discovery_expectation_max, coverage_expectation_min`.
- Status: **PROVED**.
- Dependencies: `cor:occupancy`.
- Reformulation/equivalence/alternate proof: Exact source formulas for actual expectations, with attained extrema and all optimizing laws.

Exact manuscript statement/display:

```tex
\begin{aligned}
 \max_{H(p)\le h}\EE_p K_{n,1}&=nB_{n-1}(h) &&(n\ge2),\\
 \max_{H(p)\le h}\EE_p(K_{t+1}-K_t)&=B_t(h) &&(t\ge1),\\
 \min_{H(p)\le h}\EE_p C_t&=1-B_t(h) &&(t\ge1).
 \end{aligned}
```

### `eq:kernel`

- Source: The entropy-curvature estimate; TeX label: `eq:kernel`.
- Lean correspondence: `Curvature.kernel_bound, kernel_bound_eq_iff`.
- Status: **PROVED**.
- Dependencies: `kernel_remainder`.
- Reformulation/equivalence/alternate proof: Exact sharp bound with equality characterization, valid on both sides of one.

Exact manuscript statement/display:

```tex
J_*(a)\ge\frac{2(9-a)}{15(a+1)}
 =\frac{13}{15}-\frac a3+\frac{(a-1)^2}{3(a+1)}.
```

### `eq:mixture`

- Source: The entropy-curvature estimate; TeX label: `eq:mixture`.
- Lean correspondence: `Curvature.mixture_curvature_bound`.
- Status: **PROVED**.
- Dependencies: `mixture_bound`.
- Reformulation/equivalence/alternate proof: Same probability law, mean, mixture density and dispersion expression on the compact positive interval representation.

Exact manuscript statement/display:

```tex
\int_0^\infty(s-m_\lambda)^2G(s)^2\dd s
 \ge\frac{8m_\lambda}{15}
      +\frac23\int\frac{(v-m_\lambda)^2}{v+m_\lambda}\dd\lambda(v).
```

### `eq:entropy-series`

- Source: Crossing structure of the candidate family; TeX label: `eq:entropy-series`.
- Lean correspondence: `ProbabilityVector.entropy_series`.
- Status: **PROVED**.
- Dependencies: `lem:entropy-series`.
- Reformulation/equivalence/alternate proof: The positive-integer sum is indexed by n+1; all terms are nonnegative, with exact ENNReal.ofReal bridges.

Exact manuscript statement/display:

```tex
H(p)=\sum_{j=1}^\infty\frac{\Phi_j(p)}j,
```

### `eq:heavy-crossing-sign`

- Source: Crossing structure of the candidate family; TeX label: `eq:heavy-crossing-sign`.
- Lean correspondence: `heavy_heavy_single_crossing`.
- Status: **PROVED**.
- Dependencies: `thm:heavy-crossing`.
- Reformulation/equivalence/alternate proof: Exact signs on either side of the unique simple positive crossing.

Exact manuscript statement/display:

```tex
\begin{cases}
 b_j(s)<b_i(s),&0<s<\tau_{ij},\\
 b_j(s)>b_i(s),&s>\tau_{ij}.
 \end{cases}
```

### `eq:light-crossing-sign`

- Source: Crossing structure of the candidate family; TeX label: `eq:light-crossing-sign`.
- Lean correspondence: `light_heavy_single_crossing, light_heavy_double_crossing`.
- Status: **PROVED**.
- Dependencies: `thm:light-crossing`.
- Reformulation/equivalence/alternate proof: The source interval is represented by separate finite/infinite endpoint cases, with exact root sets and strict exterior signs.

Exact manuscript statement/display:

```tex
b_m(s)>\ell(s)\quad\Longleftrightarrow\quad
 \alpha_m<s<\beta_m\qquad(s>0).
```

### `eq:light-strict-small`

- Source: Crossing structure of the candidate family; TeX label: `eq:light-strict-small`.
- Lean correspondence: `heavy_strict_below_light_smallSamples`.
- Status: **PROVED**.
- Dependencies: `light_crossing_inputs`.
- Reformulation/equivalence/alternate proof: Strict inequalities at both t=1 and t=2 exclude exactly the binary duplicate.

Exact manuscript statement/display:

```tex
b_m(1)<\ell(1),\qquad b_m(2)<\ell(2).
```

### `eq:phase-cutoff`

- Source: Crossing structure of the candidate family; TeX label: `eq:phase-cutoff`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_phase_cutoff`.
- Status: **TODO**.
- Dependencies: `finite_phase_reduction`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
T_m=\tau_{m,m+1},\qquad
 R_m=\max\{m+1,\lceil hT_m+1\rceil\},
```

### `eq:phase-endpoints`

- Source: Crossing structure of the candidate family; TeX label: `eq:phase-endpoints`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_phase_endpoints`.
- Status: **TODO**.
- Dependencies: `finite_phase_reduction`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{aligned}
 \underline{s}_m
 &=\max\bigl(\{\alpha_m\}\cup
                \{\tau_{j,m}:k\le j<m\}\bigr),\\
 \overline{s}_m
 &=\min\bigl(\{\beta_m\}\cup
                \{\tau_{m,j}:m<j\le R_m\}\bigr).
 \end{aligned}
```

### `eq:heavy-phase`

- Source: Crossing structure of the candidate family; TeX label: `eq:heavy-phase`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_phase`.
- Status: **TODO**.
- Dependencies: `cor:phase-intervals`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\underline{s}_m\le t\le\overline{s}_m.
```

### `eq:light-phase`

- Source: Crossing structure of the candidate family; TeX label: `eq:light-phase`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_light_phase`.
- Status: **TODO**.
- Dependencies: `cor:phase-intervals`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
t\notin
 \bigcup_{\substack{k\le m\le M(t,h)\\p_m^{\rm H}\ne p_{\rm L}}}
       (\alpha_m,\beta_m),
```

### `eq:finite-stationarity`

- Source: A fixed finite alphabet; TeX label: `eq:finite-stationarity`.
- Lean correspondence: `ProbabilityVector.deriv_eq_of_entropy_slack, finiteStationarity_iff_polynomial_zero`.
- Status: **PROVED**.
- Dependencies: `finite_slack`.
- Reformulation/equivalence/alternate proof: Actual slack local maximality implies derivative equality; the exact scalar equation is equivalent to the displayed polynomial.

Exact manuscript statement/display:

```tex
f_t'(z)=f_t'\!\left(\frac{1-z}{N-1}\right)
```

### `eq:finite-polynomial`

- Source: A fixed finite alphabet; TeX label: `eq:finite-polynomial`.
- Lean correspondence: `eval_finiteStationarityPolynomial, finiteStationarity_iff_polynomial_zero`.
- Status: **PROVED**.
- Dependencies: `finite_polynomial`.
- Reformulation/equivalence/alternate proof: Exact source polynomial with m=N-1; nonzero and degree/cardinality bounds are proved.

Exact manuscript statement/display:

```tex
\begin{aligned}
 &(N-1)^t(1-z)^{t-1}\bigl(1-(t+1)z\bigr)\\
 &\qquad-(N-2+z)^{t-1}\bigl((t+1)z+N-t-2\bigr)=0.
 \end{aligned}
```

### `eq:nonunimodal-example`

- Source: Certified nonmonotonicity examples; TeX label: `eq:nonunimodal-example`.
- Lean correspondence: `Certificates.value_3_heavy_10, value_3_heavy_11, value_3_heavy_12`.
- Status: **PROVED**.
- Dependencies: `nonunimodal`.
- Reformulation/equivalence/alternate proof: The three displayed strict bounds are kernel-checked for actual entropy roots.

Exact manuscript statement/display:

```tex
\begin{aligned}
 0.456467562315&<b_{10}(8)<0.456467562316,\\
 0.455820123956&<b_{11}(8)<0.455820123957,\\
 0.457052010607&<b_{12}(8)<0.457052010608.
 \end{aligned}
```

### `eq:log-certificate`

- Source: Certified nonmonotonicity examples; TeX label: `eq:log-certificate`.
- Lean correspondence: `log_certificate`.
- Status: **PROVED**.
- Dependencies: `log_certificate`.
- Reformulation/equivalence/alternate proof: Exact positive-series inequality, including its denominator factor 2R+1.

Exact manuscript statement/display:

```tex
0\le\log y-2\sum_{r=0}^{R-1}\frac{v^{2r+1}}{2r+1}
 \le\frac{2v^{2R+1}}{(2R+1)(1-v^2)}.
```
