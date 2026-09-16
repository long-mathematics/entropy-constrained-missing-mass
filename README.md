# Extremizers of the Expected Missing Mass under an Entropy Constraint

Research repository for the manuscript by Christopher D. Long.

- [LaTeX source](missing_mass_extremizers.tex)
- [Compiled PDF](missing_mass_extremizers.pdf)
- [Exact certificate script](scripts/missing_mass_extremizers_certificates.py)

## Abstract

For a discrete probability distribution \(p=(p_i)\), the expected mass of symbols absent from \(t\) independent samples is
\[
\Phi_t(p)=\sum_i p_i(1-p_i)^t.
\]
For every positive integer \(t\) and finite entropy budget \(h\ge 0\), we prove that every \(\ell^1\)-local maximizer under \(H(p)\le h\) has at most two distinct positive coordinate values, and all but at most one positive coordinate are equal. This holds on finite and countably infinite alphabets and improves the four-size bound of Berend, Kontorovich, and Zagdanski (2017). On a countably infinite alphabet, we give an exact finite classification of all global maximizers: a unique one-light or uniform candidate is compared with an explicitly bounded family of one-heavy candidates, whose masses are uniquely specified by entropy equations. The one-light or uniform candidate is uniquely optimal for \(t=1,2\). For fixed \(h>0\), the optimal value \(B_t(h)\) satisfies
\[
\frac{h}{B_t(h)}=\log t+\log\log t+2+O_h\!\left(\frac{\log\log t}{\log t}\right).
\]
Every optimizer is eventually one-heavy, with \(m_t\sim ht\) equal light atoms of size \(q_t\sim1/(t\log t)\). The two-size proof combines a three-coordinate entropy-curvature estimate with a finite coefficient comparison. Crossing theorems describe the winning intervals of the candidate distributions, and the classification gives exact extrema for singleton counts, discovery increments, and expected coverage.

## Repository contents

- `missing_mass_extremizers.tex` — manuscript source.
- `missing_mass_extremizers.pdf` — compiled manuscript.
- `scripts/missing_mass_extremizers_certificates.py` — exact rational certificates for the certified examples in the manuscript; Python standard library only.
- `CITATION.cff` — citation metadata.
- `AGENTS.md` — repository instructions for manuscript edits and validation.
- `LICENSE` — MIT license.

## Verification

Run the exact certificates with

```bash
python3 scripts/missing_mass_extremizers_certificates.py
```

The manuscript can be compiled with a standard LaTeX installation, for example

```bash
latexmk -pdf missing_mass_extremizers.tex
```
