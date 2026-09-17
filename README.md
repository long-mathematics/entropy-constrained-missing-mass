# Extremizers of the Expected Missing Mass under an Entropy Constraint

Research repository for the manuscript by Christopher D. Long.

- [LaTeX source](missing_mass_extremizers.tex)
- [Compiled PDF](missing_mass_extremizers.pdf)
- [Exact certificate script](scripts/missing_mass_extremizers_certificates.py)
- [Certificate output](scripts/missing_mass_extremizers_certificates.out)

## Abstract

For a discrete probability distribution $p=(p_i)$, the expected mass of symbols absent from $t$ independent samples is

$$
\Phi_t(p)=\sum_i p_i(1-p_i)^t.
$$

For every positive integer $t$ and finite entropy budget $h\ge 0$, we prove that every $\ell^1$-local maximizer under $H(p)\le h$ has at most two distinct positive coordinate values, and all but at most one positive coordinate are equal. This holds on finite and countably infinite alphabets and improves the four-size bound of Berend, Kontorovich, and Zagdanski (2017). On a countably infinite alphabet, we give an exact finite classification of all global maximizers: a unique one-light or uniform candidate is compared with an explicitly bounded family of one-heavy candidates, whose masses are uniquely specified by entropy equations. The one-light or uniform candidate is uniquely optimal for $t=1,2$. For fixed $h>0$, the optimal value $B_t(h)$ satisfies

$$
\frac{h}{B_t(h)}=\log t+\log\log t+2+O_h\left(\frac{\log\log t}{\log t}\right).
$$

Every optimizer is eventually one-heavy, with $m_t\sim ht$ equal light atoms of size $q_t\sim1/(t\log t)$. The two-size proof combines a three-coordinate entropy-curvature estimate with a finite coefficient comparison. Crossing theorems describe the winning intervals of the candidate distributions, and the classification gives exact extrema for singleton counts, discovery increments, and expected coverage.

## Repository contents

- `missing_mass_extremizers.tex` — manuscript source.
- `missing_mass_extremizers.pdf` — compiled manuscript.
- `scripts/missing_mass_extremizers_certificates.py` — exact rational certificates for the certified examples in the manuscript; Python standard library only.
- `scripts/missing_mass_extremizers_certificates.out` — output of the certificate script for the tracked verification cases.
- `CITATION.cff` — citation metadata.
- `AGENTS.md` — repository instructions for manuscript edits and validation.
- `LICENSE` — MIT license.

## Verification

Run the exact certificates with

```bash
python3 scripts/missing_mass_extremizers_certificates.py
```

The tracked output is available in [`scripts/missing_mass_extremizers_certificates.out`](scripts/missing_mass_extremizers_certificates.out). Its final lines are

```text
Certified: heavy-branch unimodality fails.
Certified: at t=3 and h=11/10, 6/5, 7/5 the unique types are light, heavy, light.
All exact rational certificates passed.
```

The manuscript can be compiled with a standard LaTeX installation, for example

```bash
latexmk -pdf missing_mass_extremizers.tex
```

## Lean formalization

All **18 named results** and their proof-critical dependencies are formalized in
`EntropyConstrainedMissingMass/`. The final audit covers 152 ledger obligations,
including equality cases, endpoints, countable alphabets, asymptotic uniformity,
finite classifications, occupancy statistics, and exact numerical certificates.
See [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the full correspondence
and [FORMALIZATION_AUDIT.md](FORMALIZATION_AUDIT.md) for the independent audit and
alternate proof routes.

With [elan](https://github.com/leanprover/elan) installed, run:

```bash
python3 scripts/fetch_mathlib_cache.py
lake build
lake env lean scripts/audit_lean.lean
python3 scripts/audit_source.py
python3 scripts/missing_mass_extremizers_certificates.py
```

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin Lean v4.34.0 and
all dependencies. `.lake/` and compiled Lean artifacts are not version controlled.
For a clean rebuild of the project while retaining the pinned dependency cache:

```bash
lake clean entropy_constrained_missing_mass
lake build
```

The main theorem uses the actual ℓ¹ topology, extended-valued Shannon entropy,
and arbitrary probability vectors; finite support is proved. The final kernel
axiom audit checks 2,133 project declarations (1,912 theorem constants, including
generated auxiliaries), using only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof holes or project-added axioms. The Python audit checks owned
sources, root import coverage, the named-result inventory, and ledger dependencies.

Principal entry points include `MainTheorem`, `EntropyCurvature`,
`FiniteClassification`, `AsymptoticOptimizerScales`, `SampleComplexity`,
`PhaseIntervals`, `FiniteAlphabetClassification`, `OccupancyExtrema`, and
`CertifiedExamples`. The root `EntropyConstrainedMissingMass.lean` imports the
complete formalization.

## Continuous integration

[Build and audit Lean](.github/workflows/lean-ci.yml) runs on pull requests to
`main` and pushes to `main`. It installs the pinned compiler, fetches the Mathlib
cache only for imported dependencies, rebuilds every project proof, audits
transitive axioms and source/ledger coverage, and runs the exact certificates.
The workflow has read-only repository permissions and pins its actions by commit.
The project proofs are built fresh on each run.

The release workflow is a feature branch, a pull request with **Build and audit
Lean** passing, and a squash merge. The main protection ruleset requires that
check and pull requests, prohibits force pushes/deletion, and has no owner/admin
bypass. Human approvals, signed commits, and strict branch freshness are not
required; ordinary feature branches remain unrestricted.
