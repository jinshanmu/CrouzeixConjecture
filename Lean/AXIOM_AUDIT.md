# Axiom audit

`AxiomAudit.lean` exposes the types and trust dependencies of the principal
results at every proof layer. Its central completion audit now follows the v2
auxiliary-basis route:

- `IsPositiveRealCompletion` and `PositiveRealCompletionStatement`;
- `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`;
- `exists_completionKernelModel_of_isPositiveRealCompletion`;
- arbitrary-finite-type and repeated-point kernel sampling;
- `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`;
- `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel`;
- `doubleLayerCayleySeries_isPositiveRealCompletion` and
  `HasDoubleLayerCompletionProvider`;
- the direct zero branch and
  `norm_polynomialEval_le_two_mul_of_simpleSpectrum`;
- the simple-matrix approximation and outer-domain limiting endpoints.

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

The audit also prints the fully elaborated endpoint types and axioms of
`crouzeixConjecture_mainTheorem`, `crouzeixConjecture`,
`crouzeixRationalSpectralSetCorollary`, and `crouzeixRationalBound`.
Authoritative verification is plain `lake build` followed serially by
plain `lake run`.
