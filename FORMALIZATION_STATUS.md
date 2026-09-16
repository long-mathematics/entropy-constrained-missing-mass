# Formalization status — IN PROGRESS

The entire manuscript (1,350 lines, including all appendices) was read on
2026-09-16. This is the initial exhaustive inventory, subject to the mandatory
independent final reread. **One of 18 named manuscript results is proved in Lean: `lem:entropy-series`.**
The Python certificates are independent checks, not Lean proofs. Definitions,
equation cross-checks, and subsidiary obligations are counted separately below.

## Persistent state and next action

- Baseline: `c50920a`; work branch: `formalization/foundations-and-ledger`.
- Pinned Lean: v4.34.0; mathlib: `5ed2965256430c3649e86755f9576b54eca72435`.
- Current frontier: entropy lower semicontinuity, compactness/attainment, the
  three-coordinate differential geometry, and integral curvature identities.
  Next theorem: lower semicontinuity of extended entropy in the ℓ¹ topology.
- No production CI or protection should be installed before the complete final audit.
- Editorial change only: GPT 6 Sol → GPT-6 Astra; no mathematical TeX changes.
- Validation: `lake build` passed (2,273 jobs); `lake env lean scripts/audit_lean.lean`
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

Tracked entries: **150** = 18 named results + 49 labelled equation cross-checks + 83 supporting obligations. Statuses: 10 PROVED, 10 IN PROGRESS, 130 TODO, 0 BLOCKED. Named results proved: 1/18.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.local_topology`.
- Status: **IN PROGRESS**.
- Dependencies: `probability`, `entropy`, `objective`.
- Checked progress and remaining work: ProbabilityVector.dist_eq_tsum proves exact metric identity and LocalMaximizer uses IsLocalMaxOn in that metric; finite-coordinate perturbation convergence remains TODO.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.root_coordinates`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For 0<x<y<z and fixed S=x+y+z, (E,P) are smooth local coordinates; sufficiently small changes retain positive distinct roots. Their derivatives are u_E=-u/W′(u) and u_P=1/W′(u), W(u)=u³-Su²+Eu-P.

### `integral_convergence`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.integral_convergence`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For every positive triple, I₀,I₁ and all integrals defining entropy Hessians and K converge; I₀>0 and I₁>0.

### `log_integral`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.log_integral`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For u>0, log u=∫₀∞(1/(s+1)-1/(s+u)) ds.

### `root_partial_fractions`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.root_partial_fractions`.
- Status: **TODO**.
- Dependencies: `root_coordinates`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For distinct positive roots, ∑1/((s+u)W′(u))=1/D(s) and ∑u/((s+u)W′(u))=-s/D(s), for s≥0.

### `entropy_hessian`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_hessian`.
- Status: **TODO**.
- Dependencies: `root_coordinates`, `integral_convergence`, `log_integral`, `root_partial_fractions`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At distinct positive roots, H_E=I₁, H_P=I₀, H_EE=-∫s²/D², H_EP=-∫s/D², H_PP=-∫1/D²; justify differentiation under each integral.

### `entropy_curve`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_curve`.
- Status: **TODO**.
- Dependencies: `entropy_hessian`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

The local entropy level is a smooth curve P(E), with P′=-m and P″=K.

### `triple_necessary`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.triple_necessary`.
- Status: **TODO**.
- Dependencies: `local_topology`, `entropy_curve`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

A local maximizer containing three distinct positive coordinates has D_t=0, C_t≤0 and (F_t)_P≥0, including when the entropy constraint is slack.

### `objective_calculus`

- Source: §2 and §5.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.objective_calculus`.
- Status: **IN PROGRESS**.
- Dependencies: mathlib foundations.
- Checked progress and remaining work: ObjectiveCalculus proves continuity and the exact first/second derivatives, including global endpoint formulas. The one-root/Rolle argument remains TODO.

For integer t≥1, f_t is polynomial and f′_t(u)=(t+1)(1-u)^t-t(1-u)^(t-1). For t>1 and 0<u<1, f″_t(u)=t(1-u)^(t-2)((t+1)u-2), with just one zero in (0,1).

### `positive_R`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.positive_R`.
- Status: **TODO**.
- Dependencies: `triple_necessary`, `objective_calculus`, `root_coordinates`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For t>1 at a stationary triple with (F_t)_P≥0, R_t=(F_t)_P>0: otherwise equality of three first derivatives contradicts Rolle and the one-zero property.

### `t_one_triple`

- Source: §2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.t_one_triple`.
- Status: **TODO**.
- Dependencies: `triple_necessary`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

F₁=S-S²+2E and its entropy-curve first derivative is 2, excluding three sizes at t=1.

### `homogeneous`

- Source: §3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.homogeneous`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For three nonnegative variables, G=∏(1-r_i w)^(-1)=∑h_j w^j, where h_j is the complete homogeneous polynomial and negative indices are zero. Nonzero r implies h_j>0 for all j≥0.

### `turan`

- Source: §3, eq:turan; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.turan`.
- Status: **TODO**.
- Dependencies: `homogeneous`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For all nonnegative triples and integers j≥0, h_j²-h_(j-1)h_(j+1)=h_j(r₁r₂,r₁r₃,r₂r₃)≥0. For nonzero r the successive ratios decrease; for all-positive r they decrease strictly.

### `coefficient_transfer`

- Source: §3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.coefficient_transfer`.
- Status: **TODO**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

If b_N=h_N-h_(N-1)>0, all earlier b_j are positive, σ<2, and transferring mass from a smaller interior coordinate to a larger one preserves positivity and does not decrease b_N; at most two transfers reach a vertex of the fixed-sum cube slice. Include N=0,1, r=0 and σ=1,2 boundaries.

### `coefficient_boundary`

- Source: §3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.coefficient_boundary`.
- Status: **TODO**.
- Dependencies: `homogeneous`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At fixed σ∈(0,2), boundary representatives are (1,1,1-σ) for σ≤1 and (1,2-σ,0) for σ≥1. Coefficients b_N are respectively ∑_{k=0}^N(1-σ)^k≤1/σ and (2-σ)^N≤1.

### `comparison_ratios`

- Source: §3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.comparison_ratios`.
- Status: **TODO**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Under lem:comparison hypotheses with n≥1, all B_j=h_j-βh_(j-1) are positive through n+1 and B_j/B_(j-1) strictly decrease there, by the strictly concave exponential interpolation g. Hence a_j=B_j-αB_(j-1)>0 for 0≤j≤n.

### `comparison_telescoping`

- Source: §3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.comparison_telescoping`.
- Status: **TODO**.
- Dependencies: `comparison_ratios`, `lem:coefficient-extremum`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Under the comparison hypotheses, J=∑_{j=0}^{n-1}a_jB_(n-1-j)≤C k_(n-1)<C k_n/β with C=max(1,β/(3β-∑q_i)); n=0 has J=0,k₀=1.

### `divided_differences`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.divided_differences`.
- Status: **TODO**.
- Dependencies: `homogeneous`, `root_coordinates`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

The second divided difference of (1-u)^j at x,y,z is h_(j-2)(1-x,1-y,1-z), including j=0,1. Therefore R_t=(t+1)k_n and D_t=(t+1)(k_(n+1)-βk_n).

### `objective_curvature`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.objective_curvature`.
- Status: **TODO**.
- Dependencies: `divided_differences`, `entropy_curve`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For t≥2,n=t-2,α=t/(t+1),β=1+m,q=(1-x,1-y,1-z), the entropy-curve second derivative is C_t=(t+1)(K k_n-J). The variation β′=-K must be included.

### `curvature_contradiction`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.curvature_contradiction`.
- Status: **TODO**.
- Dependencies: `lem:comparison`, `lem:entropy`, `objective_curvature`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For S≤1, D_t=0 and R_t>0 imply C_t/R_t>1/(15(S+m)) and C_t>R_t/(20S)>0.

### `two_sizes`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.two_sizes`.
- Status: **TODO**.
- Dependencies: `curvature_contradiction`, `positive_R`, `t_one_triple`, `local_topology`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Every ℓ¹-local maximum on every finite or countable alphabet has at most two positive coordinate values, by feasible three-coordinate perturbations.

### `finite_support`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.finite_support`.
- Status: **IN PROGRESS**.
- Dependencies: `probability`, `two_sizes`.
- Checked progress and remaining work: Support.finite_support_of_finite_sizes and finite_support_of_two_sizes prove the support implication, but the premise for local maximizers is not yet proved.

A probability vector with at most two distinct positive coordinate values has finite support, since each positive value can occur only finitely many times.

### `sorted_reduction`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.sorted_reduction`.
- Status: **TODO**.
- Dependencies: `objective`, `entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For the countably infinite optimization, symmetry and zero invariance allow a maximizing sequence of nonincreasing vectors. A sorted vector has p_i≤1/i for i≥1.

### `entropy_tail`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_tail`.
- Status: **TODO**.
- Dependencies: `sorted_reduction`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For a sorted feasible vector and N≥1, ∑_{i>N}p_i≤h/log(N+1). A coordinatewise limit of a uniformly entropy-bounded sorted sequence has mass one and the convergence is in ℓ¹.

### `entropy_lsc`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_lsc`.
- Status: **TODO**.
- Dependencies: `entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Entropy is lower semicontinuous under coordinatewise convergence of probability vectors by the nonnegative Fatou lemma.

### `objective_lipschitz`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.objective_lipschitz`.
- Status: **IN PROGRESS**.
- Dependencies: `objective`, `objective_calculus`, `local_topology`.
- Checked progress and remaining work: ObjectiveContinuity proves objective_dist_le and continuous_objective with explicit constant t+1 by an algebraic power estimate. This replaces derivative-maximization for continuity; the displayed optimal derivative-bound form itself is not yet checked.

For integer t≥1, |Φ_t(p)-Φ_t(q)|≤L_t‖p-q‖₁, where L_t=max_[0,1]|f′_t|<∞.

### `attainment`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.attainment`.
- Status: **TODO**.
- Dependencies: `entropy_tail`, `entropy_lsc`, `objective_lipschitz`, `zero_entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For every t≥1 and finite h≥0, a feasible maximum exists, on finite alphabets by compactness and on countably infinite alphabets by the sorted diagonal sequence and tail bound.

### `atom_splitting`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.atom_splitting`.
- Status: **IN PROGRESS**.
- Dependencies: `entropy`, `objective`, `objective_calculus`.
- Checked progress and remaining work: ObjectiveCalculus.missingMassTerm_split_strict proves strict scalar improvement. Constructing the perturbation, its ℓ¹ distance and entropy increment remains TODO.

For 0<ε<a≤1, splitting a into a-ε,ε changes ℓ¹ distance by 2ε, raises entropy by a positive increment tending to zero, and strictly increases Φ_t for every integer t≥1.

### `entropy_saturation`

- Source: §4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_saturation`.
- Status: **TODO**.
- Dependencies: `finite_support`, `atom_splitting`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Every countably infinite alphabet local maximizer has H=h: use finite support and split into an unused coordinate if H<h.

### `repeated_variation`

- Source: §5.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.repeated_variation`.
- Status: **TODO**.
- Dependencies: `local_topology`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

A repeated size u at a local maximizer has f″(u)≤0. If x<y are both repeated, the four-coordinate mass/entropy gradients are independent, multipliers satisfy f′=λ+μ(-log u-1), and pair-difference second variations give uf″(u)+μ≤0.

### `weighted_log_average`

- Source: §5.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.weighted_log_average`.
- Status: **TODO**.
- Dependencies: `repeated_variation`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For repeated x<y, -μ=(f′(y)-f′(x))/log(y/x)=∫_x^y uf″(u)du/u / log(y/x). Strict quasiconvexity makes this average strictly below max(xf″(x),yf″(y)).

### `quasiconvex`

- Source: §5.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.quasiconvex`.
- Status: **TODO**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For f_t and integer t≥1, uf″_t is strictly quasiconvex on the interval containing f″_t≤0. For t=1 it is -2u; for t>1 its derivative has the displayed quadratic with roots 0<r_-<2/(t+1)<r_+.

### `shape_boundaries`

- Source: §5.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.shape_boundaries`.
- Status: **IN PROGRESS**.
- Dependencies: `probability`.
- Checked progress and remaining work: CandidateVectors proves the uniform coordinate formula. Binary permutation equivalence and support≥3 distinction remain TODO.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_roots`.
- Status: **IN PROGRESS**.
- Dependencies: `branch_entropy`.
- Checked progress and remaining work: BranchEntropy proves exact candidate-root existence/uniqueness, including h=log k endpoint, and support-index log bounds. Exclusion of all other saturated shapes and binary equivalence remains TODO.

For h>0,k=floor(exp h), exactly one a∈[0,1/(k+1)) solves E_k(a)=h. It is zero iff h=log k. For every integer m≥k, exactly one z_m∈(1/(m+1),1) solves E_m(z_m)=h. No other light/uniform shapes saturate h.

### `candidate_completeness`

- Source: §5.2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.candidate_completeness`.
- Status: **TODO**.
- Dependencies: `thm:exceptional`, `entropy_saturation`, `entropy_roots`, `shape_boundaries`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Every global optimizer on a countably infinite alphabet is p_L or p_m^H for m≥k, with the binary duplicate exactly when 0<h<log 2 and m=1.

### `real_heavy_roots`

- Source: §5.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.real_heavy_roots`.
- Status: **TODO**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For h>0 and real m>exp h-1, a unique heavy root exists and depends smoothly on m. With σ=log(z/q)>0, h=-log z+(1-z)σ, dz/dm=q/σ>0 and dq/dm=-q(1+σ)/(mσ)<0.

### `heavy_derivative`

- Source: §5.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.heavy_derivative`.
- Status: **TODO**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For real s≥1, db_m(s)/dm=q Ψ_s(z,q)/σ, Ψ_s=f′_s(z)-f′_s(q)+sqσ(1-q)^(s-1). For z≤1/s, use A′_z(u)=s(1+log(z/u))(1-u)^(s-2)(su-1)<0 on q<u<z.

### `heavy_cutoff_sign`

- Source: §5.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.heavy_cutoff_sign`.
- Status: **TODO**.
- Dependencies: `heavy_derivative`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

If z>1/s and m≥sh+1, f′_s(z)<0 and 1-q-sq(1+σ)>1-(sh+1)/m≥0, because (1-z)(1+σ)<h. Hence Ψ_s<0; include s=1.

### `cutoff_discrete`

- Source: §5.3; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.cutoff_discrete`.
- Status: **TODO**.
- Dependencies: `lem:cutoff`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For M=max(k,ceil(th+1)), every integer j>M has b_j(t)<b_M(t). All removed candidates have strictly larger support.

### `small_samples_hessian`

- Source: §5.4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.small_samples_hessian`.
- Status: **TODO**.
- Dependencies: `repeated_variation`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For heavy m≥2, write z=rq,q=1/(m+r),r>1. The necessary qf″_t(q)+μ≤0 instead equals 2q((r-1)/log r-1)>0 for t=1 and N_m(r)/((m+r)²log r)>0 for t=2.

### `small_samples_scalar`

- Source: §5.4; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.small_samples_scalar`.
- Status: **TODO**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

N_m=N₂+4(m-2)(r-1-log r); N₂(1)=0 and N₂′(r)=2(r-1/r-2log r)>0 for r>1, since the inner derivative is (r-1)²/r².

### `heavy_L_identities`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.heavy_L_identities`.
- Status: **TODO**.
- Dependencies: `branch_entropy`, `objective`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For a heavy law L=mq,z=1-L, h=-(1-L)log(1-L)-L log q, Φ_t=(1-L)L^t+L(1-q)^t, and A(L)=-(1-L)log(1-L)/L=1-L/2+O(L²) as L↓0.

### `asymptotic_lower`

- Source: §6, lower bound; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.asymptotic_lower`.
- Status: **TODO**.
- Dependencies: `entropy_roots`, `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For m=ceil(ht) at fixed h>0, eventually a heavy entropy root exists, L=O_h(1/log t), and d=h/L=T+log T+1+O_h(log T/T); tq=1/d+O_h(1/(tT)) and -t log(1-q)=1/d+O_h(1/(tT)).

### `reciprocal_upper`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.reciprocal_upper`.
- Status: **TODO**.
- Dependencies: `asymptotic_lower`, `attainment`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For fixed h>0, h/B_t(h)≤T+log T+2+O_h(log T/T), hence B_t(h)≥c_h/T eventually for c_h>0.

### `eventually_heavy`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eventually_heavy`.
- Status: **TODO**.
- Dependencies: `reciprocal_upper`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

The fixed light/uniform candidate decays exponentially, so every optimizer is eventually heavy, uniformly in its choice.

### `optimizer_bounds`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.optimizer_bounds`.
- Status: **TODO**.
- Dependencies: `eventually_heavy`, `heavy_L_identities`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Uniformly over heavy optimizers, z≥exp(-h), L≤ρ_h=1-exp(-h)<1, the heavy contribution is ≤ρ_h^t, u=tq=O_h(log T), L=O_h(1/T), d=T-log u+1+O_h(1/T).

### `reciprocal_lower`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.reciprocal_lower`.
- Status: **TODO**.
- Dependencies: `optimizer_bounds`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Uniformly over optimizers, h/B_t≥d exp u-O_h(T²ρ_h^t)=d exp u-o_h(1/T). Eventually u<1 and d≥T; putting v=Tu gives d exp u≥T+log T+1+v-log v-O_h(1/T)≥T+log T+2-O_h(1/T).

### `optimizer_scales`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.optimizer_scales`.
- Status: **TODO**.
- Dependencies: `reciprocal_lower`, `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Uniformly over optimizers, 0≤v-log v-1=O_h(log T/T); coercivity and the unique zero at v=1 give v→1. Thus q∼1/(t log t), L∼h/log t and m∼ht.

### `strict_B_monotone`

- Source: §6; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.strict_B_monotone`.
- Status: **TODO**.
- Dependencies: `attainment`, `entropy_saturation`, `thm:asymptotics`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.occupancy_identities`.
- Status: **TODO**.
- Dependencies: `objective`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For independent samples of any finite/countable probability law, E K_(n,1)=n Φ_(n-1) for n≥2, E(K_(t+1)-K_t)=Φ_t for t≥1, and E C_t=1-Φ_t. Countable interchanges are justified; optimizers coincide exactly, including all ties.

### `uniform_curvature`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.uniform_curvature`.
- Status: **TODO**.
- Dependencies: `integral_convergence`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For x=y=z=a>0, I₀=1/(2a²), I₁=1/(2a), m=a and K=4/(15a).

### `kernel_density`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.kernel_density`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

κ_a(s)=2a²/(s+a)³ is a probability density on [0,∞) with mean a for every a>0.

### `kernel_remainder`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.kernel_remainder`.
- Status: **TODO**.
- Dependencies: `kernel_density`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.mixture_bound`.
- Status: **TODO**.
- Dependencies: `kernel_remainder`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For any probability law λ with compact positive support, mλ=EλV and G=Eλκ_V obey ∫(s-mλ)²G²≥8mλ/15+(2/3)Eλ[(V-mλ)²/(V+mλ)]. Justify Fubini, scaling, and the square expansion.

### `simplex_mixture`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.simplex_mixture`.
- Status: **TODO**.
- Dependencies: `integral_convergence`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For uniform simplex U and V=xU₁+yU₂+zU₃, EV=S/3 and E(s+V)^(-3)=1/D(s). Thus I₀=EV^(-2)/2 and I₁=EV^(-1)/2. Nonuniform x,y,z imply V is not almost surely constant.

### `tilted_moments`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.tilted_moments`.
- Status: **TODO**.
- Dependencies: `simplex_mixture`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Under dλ=v^(-2)dP_V/(2I₀), G=1/(I₀D), EλV=m, b₂=EλV²=1/(2I₀), EλV³=(S/3)b₂. Hence Eλ[(V-m)²(V+m)]=(S/3-m)b₂>0 for nonuniform triples, proving 0<m<S/3.

### `mixture_cauchy`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.mixture_cauchy`.
- Status: **TODO**.
- Dependencies: `mixture_bound`, `tilted_moments`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Cauchy–Schwarz gives Eλ[(V-m)²/(V+m)]≥(b₂-m²)²/((S/3-m)b₂), hence K≥(8/15)I₁+(1-2mI₁)²/(S-3m).

### `curvature_algebra`

- Source: Appendix A; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.curvature_algebra`.
- Status: **IN PROGRESS**.
- Dependencies: `mixture_cauchy`, `uniform_curvature`.
- Checked progress and remaining work: CurvatureAlgebra proves both final square identities and entropy_curvature_strict_of_lower_bound; AM–GM/integral lower bound remains TODO. This does not establish lem:entropy.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.entropy_difference`.
- Status: **IN PROGRESS**.
- Dependencies: `lem:entropy-series`.
- Checked progress and remaining work: EntropySeries proves absolute summability and zero sum. The sign-change consequence is still TODO.

For two finite equal-entropy laws, ∑_{j≥1}(Φ_j(p)-Φ_j(q))/j converges absolutely to zero. If a difference is nonnegative at all positive integers and strictly positive at some integer, equal entropy is impossible.

### `rolle_multiplicity`

- Source: Appendix B.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.rolle_multiplicity`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

A nonzero exponential polynomial with r distinct positive bases has at most r-1 real zeros counted with analytic multiplicity: induction after division and differentiation, including repeated roots.

### `four_term_zeros`

- Source: Appendix B.1; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.four_term_zeros`.
- Status: **TODO**.
- Dependencies: mathlib foundations.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For signs +,-,-,+ and strictly increasing positive bases, F/b^s has derivative whose quotient by (d/b)^s is strictly increasing and has at most one simple zero. Thus F has at most two real zeros counted with multiplicity.

### `heavy_crossing_inputs`

- Source: Appendix B.2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.heavy_crossing_inputs`.
- Status: **TODO**.
- Dependencies: `real_heavy_roots`, `entropy_difference`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For k≤i<j, z_i<z_j and q_j<q_i. The heavy difference has four increasing bases with signs +,-,-,+, is zero at 0, positive eventually and negative at some positive integer by equal entropy.

### `light_heavy_order`

- Source: Appendix B.2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.light_heavy_order`.
- Status: **TODO**.
- Dependencies: `entropy_roots`, `entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

For every nonduplicate heavy candidate, q_m<y<z_m. Strict entropy increase by averaging the remaining light-law atoms proves z_m>y; include a=0 and binary exclusion.

### `light_crossing_inputs`

- Source: Appendix B.2; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.light_crossing_inputs`.
- Status: **TODO**.
- Dependencies: `cor:small-samples`, `entropy_difference`, `light_heavy_order`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.finite_slack`.
- Status: **TODO**.
- Dependencies: `atom_splitting`, `thm:exceptional`, `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

On N≥2 symbols with h>0, every slack-entropy maximizer has full support; ordinary normalization stationarity yields equality of f′ at all positive sizes.

### `finite_polynomial`

- Source: Appendix C; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.finite_polynomial`.
- Status: **TODO**.
- Dependencies: `objective_calculus`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

The stationarity equation f′_t(z)=f′_t((1-z)/(N-1)) is equivalent on (0,1) to eq:finite-polynomial. That polynomial has degree≤t and is nonzero, since the derivative difference at z=1 is -2 for t=1 and -1 for t>1. Thus it has at most t roots; z=1/N is a root.

### `finite_list`

- Source: Appendix C; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.finite_list`.
- Status: **TODO**.
- Dependencies: `finite_slack`, `finite_polynomial`, `cutoff_discrete`, `zero_entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Keep saturated candidates with support≤N and all feasible stationary full-support candidates. Every maximizer belongs to this finite list; excluded heavy multiplicities are beaten by a smaller-support candidate. All listed candidates are feasible. Include N=1,h=0 and feasible full-support uniform laws.

### `log_certificate`

- Source: Appendix D; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.log_certificate`.
- Status: **TODO**.
- Dependencies: `log_integral`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.certificate_roots`.
- Status: **TODO**.
- Dependencies: `log_certificate`, `entropy_roots`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

All 24 stored brackets of width 10^(-30) contain their unique entropy roots; entropy indices and cutoffs for the four stored cases are correct and candidate lists are complete. Python is independent evidence; Lean must justify the logarithm bounds and rational computations.

### `nonunimodal`

- Source: Appendix D, eq:nonunimodal-example; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.nonunimodal`.
- Status: **TODO**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At h=19/8,t=8, b₁₀ is strictly between .456467562315 and .456467562316; b₁₁ between .455820123956 and .455820123957; b₁₂ between .457052010607 and .457052010608. Hence b₁₀>b₁₁<b₁₂.

### `certificate_winner14`

- Source: Appendix D; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.certificate_winner14`.
- Status: **TODO**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At h=19/8,t=8,M=20, the unique global winner is heavy m=14, .458686581808<B₈(19/8)<.458686581809, and its heavy atom lies between 343937132264853115880129584166/10³⁰ and the next numerator /10³⁰.

### `certificate_reentrance`

- Source: Appendix D; unnamed supporting assertion.
- Intended Lean declaration: `EntropyConstrainedMissingMass.certificate_reentrance`.
- Status: **TODO**.
- Dependencies: `certificate_roots`, `objective_certificate`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

At t=3 and h=11/10,6/5,7/5 the unique winning types are respectively light,heavy(m=3),light; the six strict decimal intervals and cutoffs M=5,5,6 in the table hold.

### `thm:main`

- Source: Introduction; TeX label: `thm:main`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_main`.
- Status: **TODO**.
- Dependencies: `two_sizes`, `finite_support`, `attainment`, `entropy_saturation`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
For every integer $t\ge1$ and $0\le h<\infty$, every local maximizer of
$\Phi_t$ on $\mathcal P_h(I)$, in the $\ell^1$ topology, has at most two
atom sizes and has finite support. The maximum is attained. If $I$ is
countably infinite, every local maximizer satisfies $H(p)=h$.
```

### `lem:entropy`

- Source: The three-coordinate reduction; TeX label: `lem:entropy`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_entropy`.
- Status: **TODO**.
- Dependencies: `curvature_algebra`, `uniform_curvature`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_coefficient_extremum`.
- Status: **TODO**.
- Dependencies: `coefficient_transfer`, `coefficient_boundary`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_comparison`.
- Status: **TODO**.
- Dependencies: `comparison_telescoping`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_repeated`.
- Status: **TODO**.
- Dependencies: `repeated_variation`, `weighted_log_average`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_exceptional`.
- Status: **TODO**.
- Dependencies: `thm:main`, `lem:repeated`, `quasiconvex`, `shape_boundaries`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_cutoff`.
- Status: **TODO**.
- Dependencies: `heavy_derivative`, `heavy_cutoff_sign`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_finite_classification`.
- Status: **TODO**.
- Dependencies: `candidate_completeness`, `cutoff_discrete`, `attainment`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.cor_small_samples`.
- Status: **TODO**.
- Dependencies: `small_samples_hessian`, `small_samples_scalar`, `candidate_completeness`, `attainment`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
For $t=1$ and $t=2$, the unique global maximizer on a countably infinite
alphabet, up to permutation and zero coordinates, is $p_{\rm L}$.
Equivalently, $B_t(h)=\ell(t)$ for $h>0$.
```

### `thm:asymptotics`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `thm:asymptotics`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_asymptotics`.
- Status: **TODO**.
- Dependencies: `reciprocal_upper`, `reciprocal_lower`, `eventually_heavy`, `optimizer_scales`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.cor_occupancy`.
- Status: **TODO**.
- Dependencies: `occupancy_identities`, `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.lem_zero_count`.
- Status: **TODO**.
- Dependencies: `rolle_multiplicity`, `four_term_zeros`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_heavy_crossing`.
- Status: **TODO**.
- Dependencies: `heavy_crossing_inputs`, `lem:zero-count`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_light_crossing`.
- Status: **TODO**.
- Dependencies: `light_crossing_inputs`, `lem:zero-count`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.thm_finite_alphabet`.
- Status: **TODO**.
- Dependencies: `finite_list`, `attainment`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
The maximum $B_{t,N}(h)$ is the largest objective value in the finite list
just described. Up to permutation, its maximizing vectors are exactly the
candidates attaining that value.
```

### `eq:entropy-derivatives`

- Source: The three-coordinate reduction; TeX label: `eq:entropy-derivatives`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_entropy_derivatives`.
- Status: **TODO**.
- Dependencies: `entropy_hessian`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\HH_E=I_1,\qquad \HH_P=I_0.
```

### `eq:curve`

- Source: The three-coordinate reduction; TeX label: `eq:curve`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_curve`.
- Status: **TODO**.
- Dependencies: `entropy_curve`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
P'=-m,\qquad P''=\K.
```

### `eq:entropy-bound`

- Source: The three-coordinate reduction; TeX label: `eq:entropy-bound`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_entropy_bound`.
- Status: **TODO**.
- Dependencies: `lem:entropy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_target`.
- Status: **TODO**.
- Dependencies: `curvature_contradiction`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\mathcal D_t=0,\quad R_t>0,\quad S\le1
 \quad\Longrightarrow\quad \mathcal C_t>0,
```

### `eq:turan`

- Source: The finite coefficient comparison; TeX label: `eq:turan`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_turan`.
- Status: **TODO**.
- Dependencies: `turan`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
h_j(r)^2-h_{j-1}(r)h_{j+1}(r)
 =h_j(r_1r_2,r_1r_3,r_2r_3)\ge0\qquad(j\ge0).
```

### `eq:b-bound`

- Source: The finite coefficient comparison; TeX label: `eq:b-bound`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_b_bound`.
- Status: **TODO**.
- Dependencies: `lem:coefficient-extremum`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
b_j:=h_j(r)-h_{j-1}(r)\le C_\sigma:=\max\{1,\sigma^{-1}\}
 \qquad(j\ge0).
```

### `eq:coefficient`

- Source: The finite coefficient comparison; TeX label: `eq:coefficient`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_coefficient`.
- Status: **TODO**.
- Dependencies: `lem:comparison`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{aligned}
 J&:=[w^{n-1}](1-\alpha w)(1-\beta w)^2G(w)^2\\
  &<\max\left\{\frac1\beta,\frac1{3\beta-\sum_iq_i}\right\}k_n,
\end{aligned}
```

### `eq:derivatives`

- Source: Completion of the two-size proof; TeX label: `eq:derivatives`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_derivatives`.
- Status: **TODO**.
- Dependencies: `objective_curvature`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_positive_curvature`.
- Status: **TODO**.
- Dependencies: `curvature_contradiction`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac{\mathcal C_t}{R_t}=\K-\frac J{k_n}
 >\frac1{15(S+m)}>0.
```

### `eq:strict-quasiconvex`

- Source: One exceptional atom and a finite classification; TeX label: `eq:strict-quasiconvex`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_strict_quasiconvex`.
- Status: **TODO**.
- Dependencies: `lem:repeated`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
g(v)<\max\{g(x),g(y)\}\qquad(x<v<y,\quad x,y\in J).
```

### `eq:log-average`

- Source: One exceptional atom and a finite classification; TeX label: `eq:log-average`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_log_average`.
- Status: **TODO**.
- Dependencies: `weighted_log_average`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
-\mu=\frac{f'(y)-f'(x)}{\log(y/x)}
 =\frac{\displaystyle\int_x^y g(u)\,\frac{\dd u}{u}}
        {\log(y/x)}.
```

### `eq:exceptional-form`

- Source: One exceptional atom and a finite classification; TeX label: `eq:exceptional-form`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_exceptional_form`.
- Status: **TODO**.
- Dependencies: `thm:exceptional`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
p_m(z)=\left(z,\underbrace{q,\ldots,q}_{m\text{ copies}}\right),
 \qquad q=\frac{1-z}{m},\quad m\in\mathbb N,\quad 0<z<1.
```

### `eq:branch-functions`

- Source: One exceptional atom and a finite classification; TeX label: `eq:branch-functions`.
- Lean correspondence: `branchEntropy, branchObjective, entropy_candidateVector, objective_candidateVector, entropy_natCandidateVector, objective_natCandidateVector`.
- Status: **IN PROGRESS**.
- Dependencies: `branch_entropy`.
- Reformulation/equivalence/alternate proof: Definitions reproduce the formulas exactly; actual finite and countable vectors formally realize them for integer sample sizes. Real-exponent objective continuation remains in the crossing/cutoff obligations.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_light_candidate`.
- Status: **TODO**.
- Dependencies: `entropy_roots`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
p_{\rm L}=p_k(a),\qquad y=\frac{1-a}{k},\qquad
 \ell(s)=V_{k,s}(a).
```

### `eq:heavy-candidates`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-candidates`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_candidates`.
- Status: **TODO**.
- Dependencies: `entropy_roots`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
q_m=\frac{1-z_m}{m},\qquad
 p_m^{\rm H}=p_m(z_m),\qquad b_m(s)=V_{m,s}(z_m).
```

### `eq:cutoff-decrease`

- Source: One exceptional atom and a finite classification; TeX label: `eq:cutoff-decrease`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_cutoff_decrease`.
- Status: **TODO**.
- Dependencies: `lem:cutoff`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac{\dd}{\dd m}b_m(s)<0\qquad\text{whenever }m\ge sh+1.
```

### `eq:heavy-entropy-sigma`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-entropy-sigma`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_entropy_sigma`.
- Status: **TODO**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
h=-\log z+(1-z)\sigma.
```

### `eq:heavy-m-derivatives`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-m-derivatives`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_m_derivatives`.
- Status: **TODO**.
- Dependencies: `real_heavy_roots`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac{\dd z}{\dd m}=\frac q\sigma,
 \qquad
 \frac{\dd q}{\dd m}=-\frac{q(1+\sigma)}{m\sigma}.
```

### `eq:heavy-objective-derivative`

- Source: One exceptional atom and a finite classification; TeX label: `eq:heavy-objective-derivative`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_objective_derivative`.
- Status: **TODO**.
- Dependencies: `heavy_derivative`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac{\dd b_m(s)}{\dd m}=\frac q\sigma\Psi_s(z,q),\qquad
 \Psi_s(z,q)=f_s'(z)-f_s'(q)+sq\sigma(1-q)^{s-1}.
```

### `eq:M-cutoff`

- Source: One exceptional atom and a finite classification; TeX label: `eq:M-cutoff`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_M_cutoff`.
- Status: **TODO**.
- Dependencies: `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
M=M(t,h)=\max\{k,\lceil th+1\rceil\},\qquad k=\lfloor e^h\rfloor.
```

### `eq:finite-maximum`

- Source: One exceptional atom and a finite classification; TeX label: `eq:finite-maximum`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_finite_maximum`.
- Status: **TODO**.
- Dependencies: `thm:finite-classification`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
B_t(h)=\max\{\ell(t),b_k(t),b_{k+1}(t),\ldots,b_M(t)\}.
```

### `eq:small-sample-hessian`

- Source: One exceptional atom and a finite classification; TeX label: `eq:small-sample-hessian`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_small_sample_hessian`.
- Status: **TODO**.
- Dependencies: `small_samples_hessian`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
qf_t''(q)+\mu\le0,\qquad
 \mu=\frac{f_t'(q)-f_t'(z)}{\log r},
```

### `eq:sharp-asymptotic`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:sharp-asymptotic`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_sharp_asymptotic`.
- Status: **TODO**.
- Dependencies: `thm:asymptotics`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac{h}{B_t(h)}
 =\log t+\log\log t+2
  +O_h\!\left(\frac{\log\log t}{\log t}\right).
```

### `eq:optimizer-scales`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:optimizer-scales`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_optimizer_scales`.
- Status: **TODO**.
- Dependencies: `optimizer_scales`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
L_t\sim\frac h{\log t},\qquad
 q_t\sim\frac1{t\log t},\qquad
 m_t\sim ht.
```

### `eq:L-entropy-objective`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:L-entropy-objective`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_L_entropy_objective`.
- Status: **TODO**.
- Dependencies: `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{aligned}
 h&=-(1-L)\log(1-L)-L\log q,\\
 \Phi_t(p)&=(1-L)L^t+L(1-q)^t.
 \end{aligned}
```

### `eq:A-L`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:A-L`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_A_L`.
- Status: **TODO**.
- Dependencies: `heavy_L_identities`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
A(L)=-\frac{1-L}{L}\log(1-L)
     =1-\frac L2+O(L^2)\qquad(L\downarrow0).
```

### `eq:d-lower-candidate`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:d-lower-candidate`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_d_lower_candidate`.
- Status: **TODO**.
- Dependencies: `asymptotic_lower`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
d=T+\log T+1+O_h\!\left(\frac{\log T}{T}\right).
```

### `eq:reciprocal-upper`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:reciprocal-upper`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_reciprocal_upper`.
- Status: **TODO**.
- Dependencies: `reciprocal_upper`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_reciprocal_uniform`.
- Status: **TODO**.
- Dependencies: `reciprocal_lower`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\frac h{B_t(h)}
 \ge de^u-O_h(T^2\rho_h^t)
 =de^u-o_h(T^{-1}).
```

### `eq:scalar-gap`

- Source: Sharp asymptotics and occupancy consequences; TeX label: `eq:scalar-gap`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_scalar_gap`.
- Status: **TODO**.
- Dependencies: `reciprocal_lower`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_occupancy_extrema`.
- Status: **TODO**.
- Dependencies: `cor:occupancy`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_kernel`.
- Status: **TODO**.
- Dependencies: `kernel_remainder`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
J_*(a)\ge\frac{2(9-a)}{15(a+1)}
 =\frac{13}{15}-\frac a3+\frac{(a-1)^2}{3(a+1)}.
```

### `eq:mixture`

- Source: The entropy-curvature estimate; TeX label: `eq:mixture`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_mixture`.
- Status: **TODO**.
- Dependencies: `mixture_bound`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_heavy_crossing_sign`.
- Status: **TODO**.
- Dependencies: `thm:heavy-crossing`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{cases}
 b_j(s)<b_i(s),&0<s<\tau_{ij},\\
 b_j(s)>b_i(s),&s>\tau_{ij}.
 \end{cases}
```

### `eq:light-crossing-sign`

- Source: Crossing structure of the candidate family; TeX label: `eq:light-crossing-sign`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_light_crossing_sign`.
- Status: **TODO**.
- Dependencies: `thm:light-crossing`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
b_m(s)>\ell(s)\quad\Longleftrightarrow\quad
 \alpha_m<s<\beta_m\qquad(s>0).
```

### `eq:light-strict-small`

- Source: Crossing structure of the candidate family; TeX label: `eq:light-strict-small`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_light_strict_small`.
- Status: **TODO**.
- Dependencies: `light_crossing_inputs`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_finite_stationarity`.
- Status: **TODO**.
- Dependencies: `finite_slack`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
f_t'(z)=f_t'\!\left(\frac{1-z}{N-1}\right)
```

### `eq:finite-polynomial`

- Source: A fixed finite alphabet; TeX label: `eq:finite-polynomial`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_finite_polynomial`.
- Status: **TODO**.
- Dependencies: `finite_polynomial`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
\begin{aligned}
 &(N-1)^t(1-z)^{t-1}\bigl(1-(t+1)z\bigr)\\
 &\qquad-(N-2+z)^{t-1}\bigl((t+1)z+N-t-2\bigr)=0.
 \end{aligned}
```

### `eq:nonunimodal-example`

- Source: Certified nonmonotonicity examples; TeX label: `eq:nonunimodal-example`.
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_nonunimodal_example`.
- Status: **TODO**.
- Dependencies: `nonunimodal`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

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
- Intended Lean declaration: `EntropyConstrainedMissingMass.eq_log_certificate`.
- Status: **TODO**.
- Dependencies: `log_certificate`.
- Reformulation/equivalence/alternate proof: pending under the policy above.

Exact manuscript statement/display:

```tex
0\le\log y-2\sum_{r=0}^{R-1}\frac{v^{2r+1}}{2r+1}
 \le\frac{2v^{2R+1}}{(2R+1)(1-v^2)}.
```
