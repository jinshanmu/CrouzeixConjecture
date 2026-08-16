# Crouzeix Conjecture

This repository records a research workspace for a candidate proof of Crouzeix's conjecture.

## Status

- The candidate proof is written as a standalone LaTeX manuscript.
- Several independent computational and adversarial audits have found no
  specific mathematical error.
- Formal peer review is still pending.

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
- `conversation-019f7059-public/`: privacy-filtered record of the Codex
  proof-development conversation and all persisted subagent branches, including
  the formal reasoning summaries that OpenAI exposes for review.

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
The corresponding [public-review conversation record](conversation-019f7059-public/README.md)
contains visible messages and formal reasoning summaries while excluding hidden
reasoning blocks, platform instructions, credentials, and personal account
identifiers.
