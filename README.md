# Crouzeix Conjecture

This repository records a research workspace for a candidate proof of the
finite-dimensional scalar form of Crouzeix's conjecture.

## Status

- The candidate proof is written as a standalone LaTeX manuscript.
- Several independent computational and adversarial audits have found no
  specific mathematical error.
- Independent human expert review and formal peer review are still pending.
- The repository should therefore be read as a research draft, not as an
  established resolution of the conjecture.

## Contents

- `AnnMath/the_numerical_range_is_a_2_spectral_set.tex`: Annals-formatted
  submission manuscript.
- `AnnMath/the_numerical_range_is_a_2_spectral_set.pdf`: compiled submission
  manuscript.
- `AnnMath/aomart.cls`: Annals of Mathematics document class used for the
  submission build.
- `Lean/`: Lean 4 formalization, verification entry point, and axiom audit.
- `LaTeX/crouzeix_conjecture_proof.tex`: candidate proof manuscript.
- `LaTeX/crouzeix_conjecture_proof.pdf`: compiled manuscript.
- `LaTeX/main_problem.tex`: statement of the problem.
- `crouzeix_conjecture_prompt.txt`: project provenance and original task
  specification.

Locally collected third-party papers under `Literature/` are intentionally
excluded from version control and redistribution.

## Build

From the `AnnMath` directory, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error the_numerical_range_is_a_2_spectral_set.tex
```

## Lean verification

From the `Lean` directory, run:

```sh
lake run
```

This builds the complete library and runs the exported-theorem axiom audit.

## AI assistance

OpenAI ChatGPT contributed to proof development, manuscript preparation, and adversarial checking.
