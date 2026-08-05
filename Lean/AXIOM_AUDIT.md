# Axiom audit

`AxiomAudit.lean` exposes the types and trust dependencies of the principal
results at every proof layer. Its ordinary Crouzeix audit follows the v4
holomorphic auxiliary-basis route:

- `IsPositiveRealCompletion` and `PositiveRealCompletionStatement`;
- `SimpleDiagonalization.functionEval` in the auxiliary eigenbasis;
- `exists_completionKernelModel_of_isPositiveRealCompletion`;
- arbitrary-finite-type and repeated-point kernel sampling;
- `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`;
- `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel`;
- `gramian_four_sub_one_sub_first_posSemidef` and the direct no-Stein norm
  endpoint;
- the bounded positive unital radial boundary map and its Cayley series;
- `parametric_direct_cayley_identity_of_powerCauchy`,
  `exists_positiveRealCompletion_of_parametricPowerCauchy`, and
  `norm_le_two_of_parametricPowerCauchy`;
- direct scalar and matrix holomorphic Cauchy formulas,
  `HasParametricPowerCauchyFormula`, and the holomorphic double-layer bound;
- the simple-matrix limit on a fixed radial domain and the subsequent
  canonical outer-domain limit;
- `holomorphicMatrixEval`, contour identification, neighborhood locality,
  the additive and multiplicative calculus laws, polynomial and rational
  compatibility, and `holomorphicCrouzeixBound`;
- the direct rational consequence, both matrix-function error estimates, and
  `finiteRationalSpectralSetCorollary`;
- the exact ordinary witness `jordanNilpotentTwo_attains_two` and endpoint
  `crouzeixConstantTwo_isLeast_finTwo`;
- finite-dimensional transport, Krylov compression, and
  `hilbertSpacePolynomialCrouzeix`;
- `spectrum_subset_closedOperatorNumericalRange`, the approximation-based
  `operatorRationalEval`, its identification with the standard reduced
  rational calculus, and the complete packages
  `hilbertSpaceRationalSpectralSet` and
  `closedOperatorNumericalRange_isTwoSpectralSet`.

The superseded normalized affine `f_eta`, collision-avoidance,
generated-algebra equality, and `eta → 0` formalization has been deleted from
the working tree and is absent from the audit. Git history preserves the
prior implementation. General matrix, numerical-range, generated-algebra,
Herglotz, contour, simple-spectrum-density, and outer-limit infrastructure
remains audited.

The expected trust boundary is ordinary Mathlib foundations:
`propext`, `Classical.choice`, and `Quot.sound`. Classical choice is used
openly for finite bases, eigenvalues, maxima, square roots, and
simple-spectrum approximants.

Repository scans prohibit `sorry`, `admit`, custom `axiom` declarations,
unsafe proof construction, native-decision shortcuts, compiler-trust
shortcuts, option overrides, warning suppression, and circular endpoint
aliases.

The holomorphic proof selects convex buffers inside the supplied open
neighborhoods, uses direct Cauchy formulas there, and takes a tail of canonical
outer approximations whose closures remain inside the supplied neighborhood.
It assumes no Runge theorem, Mergelyan theorem, or custom analytic axiom.

The audit also prints the fully elaborated endpoint types and axioms of
`parametricBoundaryIntegral_eq_holomorphicMatrixEval`,
`holomorphicCrouzeixBound`, the holomorphic algebra and rational-compatibility
laws, `holomorphicCrouzeixRationalBound`, both matrix-function error bounds,
`finiteRationalSpectralSetCorollary`,
`jordanNilpotentTwo_attains_two`, `crouzeixConstantTwo_isLeast_finTwo`,
`crouzeixConjecture`,
`crouzeixRationalSpectralSetCorollary`, `hilbertSpacePolynomialCrouzeix`,
`spectrum_subset_closedOperatorNumericalRange`,
`operatorRationalEval_eq_num_mul_inverse_denom`,
`hilbertSpaceRationalCrouzeix`, `hilbertSpaceRationalSpectralSet`, and
`closedOperatorNumericalRange_isTwoSpectralSet`.
For the scaled `q` development it additionally audits:

- phase reduction, the exact parameter identities, Tsing's disk-union
  theorem, and nesting;
- rank-one-stretch positivity, inverse, sharp norm product, and range
  inclusion;
- the rank-one-stretch extraction theorem;
- the reusable rational transfer theorem and its constant-two instance;
- the explicit sharp rational and polynomial endpoints;
- the exact Jordan-block maximum, lower branch, and complex-parameter
  dimension-two least-constant theorem.

The scaled `q` declarations have the same expected trust boundary:
`propext`, `Classical.choice`, and `Quot.sound`, with no custom axiom.
Authoritative verification is `lake build` followed serially by
`lake env lean AxiomAudit.lean`.
