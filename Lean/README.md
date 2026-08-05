# Crouzeix conjecture manuscript formalization

This project audits and formalizes the proof architecture of
`../preprint/the_numerical_range_is_a_2_spectral_set_v4.tex`, 1,106 lines,
at SHA-256
`c8968d966d5564d9523d35b5d1bf7aa196c49c6769da4706c58d60876d9f5d18`.
Source-line references in the original Crouzeix audit sections refer to that
version.

The same library now also formalizes the spectral-set proof in
`../preprint/q_numerical_range_spectral_set.tex`, 669 lines, at SHA-256
`69862abf0f290975767dfd84dc998509da90c34982302927a19b45edcaa22771`.

It uses Lean 4.28.0 and Mathlib pinned at commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. The committed dependency
manifest records the transitive revisions needed for a reproducible build;
downloaded packages and build products remain local under `.lake/`.

The library proves the manuscript's finite-matrix holomorphic Crouzeix
estimate.  The functional calculus `CrouzeixConjecture.holomorphicMatrixEval`
is identified with every admissible contour integral, agrees with
`polynomialEval` and the reduced rational calculus, is local on a
neighborhood of the numerical range, and satisfies the additive and
multiplicative functional-calculus laws there.
The endpoint `CrouzeixConjecture.holomorphicCrouzeixBound` assumes exactly an
open set `U` containing `W(A)` and complex differentiability of `f` on `U`,
and proves the constant-`2` bound by the maximum of `|f|` on `W(A)`.

Its polynomial specialization remains available as the pointwise theorem
`CrouzeixConjecture.crouzeixConjecture`: for every matrix on a finite nonempty
complex Euclidean coordinate space and every complex polynomial, the induced
Euclidean operator norm of the matrix polynomial is at most twice the maximum
polynomial modulus on the numerical range. This is
`CrouzeixConjecture.crouzeixConjecture`. The exactness statement
`crouzeixConstantTwo_isLeast_finTwo` shows that `2` is least already for the
rational bounds restricted to `2 × 2` matrices.

The active proof follows the v4 holomorphic auxiliary-basis route.
An auxiliary matrix `B` has simple spectrum, while the target
`T = f(B)` is diagonal in the same basis. The sampled values `f(βᵢ)` may
repeat or vanish. The positive-real defect belongs to `alg(Bᴴ)`, kernel
sampling permits repeated points, and the completion theorem concludes
`‖T‖ ≤ 2` without requiring `T` to have simple spectrum. The radial boundary
map is explicitly bounded; exact power Cauchy identities feed its analytic
Cayley series. The proof treats the zero-maximum case directly and otherwise
uses only normalization by the maximum. It then lets simple-spectrum matrices
`Bₖ → A` inside each fixed outer domain and only afterward lets the convex
outer domains decrease to `W(A)`. The Gramian endpoint uses the first
nonconstant term directly, with no Stein identity. The direct Cayley algebra
is recorded by `isPositiveRealCompletion_of_direct_cayley_identity`; the
holomorphic contour route selects a convex buffer inside the supplied open
neighborhood, obtains the scalar Cauchy formula there, and transports it
entrywise through the auxiliary diagonalization. Power compatibility then
supplies exactly the Cauchy data used by the same double-layer completion
mechanism.

The superseded `f_eta` collision-avoidance, algebra-equality, and
`eta → 0` formalization has been deleted from the working tree. Git history
preserves the prior implementation if it is ever needed for historical
comparison. In the completion algebra, Lean names the manuscript matrices
`Q` and `Y` as `completionR` and `completionX` respectively; Lean's `P`
agrees with the manuscript's `P`.

Rational compatibility makes the finite rational estimate a direct
specialization of the holomorphic theorem. Its pointwise form is
`CrouzeixConjecture.holomorphicCrouzeixRationalBound`; the complete compactness,
spectrum-containment, and bound package is
`CrouzeixConjecture.finiteRationalSpectralSetCorollary`. The public aliases
`crouzeixRationalSpectralSetCorollary` and `crouzeixRationalBound` remain.

The manuscript's polynomial and rational matrix-function error estimates are
`holomorphicCrouzeixPolynomialErrorBound` and
`holomorphicCrouzeixRationalErrorBound`.

The checked Hilbert-space polynomial consequence is
`CrouzeixConjecture.hilbertSpacePolynomialCrouzeix`.  It transports the finite
theorem to finite-dimensional Hilbert spaces and then applies it to finite
Krylov compressions of an arbitrary bounded operator.

On the closed operator numerical range, `HilbertSpectralSet.lean` proves
convexity, compactness, `spectrum_subset_closedOperatorNumericalRange`, and the
rational constant-`2` bound. It defines `operatorRationalEval` as the unique
operator-norm limit supplied by the project's explicit finite-denominator
polynomial approximation, identifies this limit with the standard reduced
numerator-times-inverse-denominator calculus, proves polynomial compatibility, and packages
spectrum inclusion together with the rational estimate as
`hilbertSpaceRationalSpectralSet`. The full one-operator package, including
compactness, is `closedOperatorNumericalRange_isTwoSpectralSet`. This route
proves the needed special-purpose approximation internally rather than
assuming a general Runge or Mergelyan axiom.

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

The finite-matrix development now includes the manuscript's standard
holomorphic open-neighborhood statement as well as its polynomial and rational
specializations. The proof is direct: it uses convex-buffer Cauchy formulas
inside the supplied open neighborhoods, contour locality, and a tail of
canonical outer approximations. It
does not assume Runge's theorem, Mergelyan's theorem, or a custom analytic
axiom. The scaled `q` development separately matches its manuscript's exact
rational scope, including stretch containment, extraction, transfer,
constant-two specialization, and complex-parameter sharpness.

Run `lake build` for the complete library, followed serially by
`lake env lean AxiomAudit.lean`. Do not overlap Lean/Lake processes.

See `FORMALIZATION_MAP.md` for both source-coverage maps,
`CONTINUATION_STATUS.md` for the proof route and verification procedure,
`MANUSCRIPT_AUDIT.md` for the mathematical audit, and `AXIOM_AUDIT.md` for
the trust boundary.
