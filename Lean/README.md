# Crouzeix conjecture manuscript formalization

This project audits and formalizes the proof architecture of
`../preprint/the_numerical_range_is_a_2_spectral_set_v2.tex`, 1,165 lines,
at SHA-256
`6bd029631d6b2207795a1bb4df1064b77e5c4323deb816b8a37dec7a969a80f4`.
All source-line references in the audit documents refer to that version.

It uses Lean 4.28.0 and Mathlib pinned at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The committed dependency
manifest records the transitive revisions needed for a reproducible build;
downloaded packages and build products remain local under `.lake/`.

The library proves the manuscript's polynomial Crouzeix estimate unconditionally.
Its public pointwise theorem is `CrouzeixConjecture.crouzeixConjecture`: for
every matrix on a finite nonempty complex Euclidean coordinate space and every
complex polynomial, the induced Euclidean operator norm of the matrix
polynomial is at most twice the maximum polynomial modulus on the numerical
range. The quantified form is
`CrouzeixConjecture.crouzeixConjecture_mainTheorem : MainTheoremStatement`.

The active fixed-domain proof follows the v2 auxiliary-basis simplification.
An auxiliary matrix `B` has simple spectrum, while the target
`T = f(B)` is diagonal in the same basis. The sampled values `f(βᵢ)` may
repeat or vanish. The positive-real defect belongs to `alg(Bᴴ)`, kernel
sampling permits repeated points, and the completion theorem concludes
`‖T‖ ≤ 2` without requiring `T` to have simple spectrum. For a polynomial
`p`, the proof treats the zero-supremum case directly and otherwise uses only
the normalization `f = p / M`. It then lets simple-spectrum matrices
`Bₖ → A` and finally lets the convex outer domains decrease to `W(A)`.

The superseded `f_eta` collision-avoidance, algebra-equality, and
`eta → 0` formalization has been deleted from the working tree. Git history
preserves the prior implementation if it is ever needed for historical
comparison. In the completion algebra, Lean names the manuscript matrices
`Q` and `Y` as `completionR` and `completionX` respectively; Lean's `P`
agrees with the manuscript's `P`.

The rational spectral-set discussion is formalized separately as
`CrouzeixConjecture.crouzeixRationalSpectralSetCorollary`, with pointwise form
`CrouzeixConjecture.crouzeixRationalBound`.

Run plain `lake build` for the complete library. Plain `lake run` is the
authoritative default verification script: it runs the build and then
`lake env lean AxiomAudit.lean`. Run these serially; do not overlap Lean/Lake
processes.

See `FORMALIZATION_MAP.md` for v2 source coverage,
`CONTINUATION_STATUS.md` for the proof route and verification procedure,
`MANUSCRIPT_AUDIT.md` for the mathematical audit, and `AXIOM_AUDIT.md` for
the trust boundary.
