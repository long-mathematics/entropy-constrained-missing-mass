# Repository instructions

This repository contains a mathematical research preprint.

## Primary document

The primary source is `missing_mass_extremizers.tex`.

Compile with:

```sh
latexmk -pdf missing_mass_extremizers.tex
```

If `missing_mass_extremizers.pdf` is present, it is the compiled preprint and is intentionally tracked.

## Mathematical integrity

- Do not alter theorem, proposition, lemma, corollary, or conjecture statements unless explicitly instructed.
- Do not silently weaken or strengthen hypotheses or conclusions.
- Do not silently repair a suspected mathematical error. Flag it and explain the issue first.
- Preserve mathematical notation unless a task explicitly concerns notation.
- When changing a proof, inspect downstream results that depend on the changed argument.
- Distinguish substantive mathematical changes from editorial, typographical, and repository changes.

## LaTeX conventions

- Preserve the existing document style and notation.
- Do not introduce unnecessary packages or macros.
- Keep existing labels stable whenever possible.
- Resolve broken references and citations caused by edits.
- The bibliography is contained directly in the TeX source; there is currently no external `.bib` file.

## Verification

The manuscript contains certified numerical examples checked by
`scripts/missing_mass_extremizers_certificates.py`. Run it with:

```sh
python3 scripts/missing_mass_extremizers_certificates.py
```

The script uses exact rational arithmetic and the Python standard library only.

Before completing a task that changes the manuscript:

1. Compile the paper with `latexmk -pdf missing_mass_extremizers.tex`.
2. Check the final LaTeX log for undefined references or citations.
3. Run `python3 scripts/missing_mass_extremizers_certificates.py` when changes touch the certified examples or their supporting classification.
4. Review the complete diff.
5. Report substantive mathematical changes separately from editorial or mechanical changes.

## Generated files

Do not commit LaTeX auxiliary files. The final compiled PDF is the exception and may remain tracked.
