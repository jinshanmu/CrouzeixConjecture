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

- `LaTeX/crouzeix_conjecture_proof.tex`: candidate proof manuscript.
- `LaTeX/crouzeix_conjecture_proof.pdf`: compiled manuscript.
- `LaTeX/main_problem.tex`: statement of the problem.
- `crouzeix_conjecture_prompt.txt`: project provenance and original task
  specification.

Locally collected third-party papers under `Literature/` are intentionally
excluded from version control and redistribution.

## Build

From the `LaTeX` directory, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error crouzeix_conjecture_proof.tex
```

## AI assistance

OpenAI Codex contributed to proof development, manuscript preparation, and
adversarial checking. Any human author or submitter must independently verify
the complete argument, accurately disclose the assistance under the target
journal's policy, and assume responsibility for every claim and citation.
