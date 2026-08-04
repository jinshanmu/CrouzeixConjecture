# Crouzeix conjecture manuscript formalization

This project audits and formalizes the proof architecture of
`../preprint/the_numerical_range_is_a_2_spectral_set_v3.tex`, 1,066 lines,
at SHA-256
`f190178bc197c5f62fa8146f96c932a241379e90bf63145d542035058b92d154`.
Source-line references in the original Crouzeix audit sections refer to that
version.

The same library now also formalizes the spectral-set proof in
`../preprint/q_numerical_range_spectral_set.tex`, 660 lines, at SHA-256
`5939c6f76c0d2ab0aea076ae89af7d3c709fc49ba175917560da31733f061620`.

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

The active proof follows the v3 auxiliary-basis simplification.
An auxiliary matrix `B` has simple spectrum, while the target
`T = f(B)` is diagonal in the same basis. The sampled values `f(βᵢ)` may
repeat or vanish. The positive-real defect belongs to `alg(Bᴴ)`, kernel
sampling permits repeated points, and the completion theorem concludes
`‖T‖ ≤ 2` without requiring `T` to have simple spectrum. For a polynomial
`p`, the proof treats the zero-supremum case directly and otherwise uses only
the normalization `f = p / M`. It then lets simple-spectrum matrices
`Bₖ → A` inside each fixed outer domain and only afterward lets the convex
outer domains decrease to `W(A)`. The Gramian endpoint uses the first
nonconstant term directly, with no Stein identity. The direct Cayley algebra
is recorded by `isPositiveRealCompletion_of_direct_cayley_identity`; the
concrete polynomial contour provider still obtains its special Cauchy identity
through a uniform series bridge.

The superseded `f_eta` collision-avoidance, algebra-equality, and
`eta → 0` formalization has been deleted from the working tree. Git history
preserves the prior implementation if it is ever needed for historical
comparison. In the completion algebra, Lean names the manuscript matrices
`Q` and `Y` as `completionR` and `completionX` respectively; Lean's `P`
agrees with the manuscript's `P`.

The rational spectral-set discussion is formalized separately as
`CrouzeixConjecture.crouzeixRationalSpectralSetCorollary`, with pointwise form
`CrouzeixConjecture.crouzeixRationalBound`.

For the scaled `q`-numerical range, the public rational endpoint is
`CrouzeixConjecture.sharpRationalScaledQNumericalRangeBound`.  For every
finite complex matrix space of dimension at least two, every
`0 < ‖q‖ ≤ 1`, and every rational function pole-free on the scaled range, it
proves the spectral-set inequality with the displayed sharp constant

`max 1 (2 * ‖q‖ / (1 + √(1 - ‖q‖ ^ 2)))`.

The reusable theorem
`CrouzeixConjecture.rationalScaledQNumericalRangeBound_of_universal`
transfers any universal ordinary numerical-range constant `K` to
`max 1 (K / qKappa ‖q‖)`.  The proof includes phase reduction, Tsing's
disk-union characterization and nesting, rank-one positive stretches, exact
rational Möbius composition, rational spectral mapping, the similarity-orbit
extraction lemma, and the `M + epsilon` limit.  The theorem
`CrouzeixConjecture.sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex`
combines the upper bound with the constant and Jordan-block witnesses to show
that the displayed constant is least even for `2 × 2` matrices.

The manuscript and Lean development now have the same exact scope: the
rational spectral-set assertion, its polynomial specialization, and the
adapted rank-one stretches selected by extraction.  The disk formula,
stretch containment, extraction, rational transfer, constant-two
specialization, and complex-parameter sharpness proof are formalized in the
same order and at the same strength.

Run plain `lake build` for the complete library. Plain `lake run` is the
authoritative default verification script: it runs the build and then
`lake env lean AxiomAudit.lean`. Run these serially; do not overlap Lean/Lake
processes.

See `FORMALIZATION_MAP.md` for both source-coverage maps,
`CONTINUATION_STATUS.md` for the proof route and verification procedure,
`MANUSCRIPT_AUDIT.md` for the mathematical audit, and `AXIOM_AUDIT.md` for
the trust boundary.
