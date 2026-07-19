# Axiom audit

`AxiomAudit.lean` prints the axioms of the principal exported results at every proof layer,
including the matrix/operator bridges, matrix Herglotz theorem, analytic diagonal correction,
positive-real completion theorem,
double-layer positivity/series reductions, Toeplitz--Hausdorff convexity,
perturbation/outer-limit reductions, convex projection and squared-distance calculus, inverse-gauge
radial geometry, the unconditional main theorem, and the separate rational corollary.

The confirmed output contains only ordinary Mathlib foundations: propositional extensionality,
classical choice, and quotient soundness.  Classical choice is used openly for finite bases,
eigenvalues, maxima, square roots, and selected perturbation parameters.

Repository scans prohibit `sorry`, `admit`, custom `axiom` declarations, `unsafe` proof
construction, native-decision shortcuts, compiler-trust shortcuts, option overrides, warning
suppression, and circular aliases.

The audit prints the fully elaborated endpoint types and axioms of
`crouzeixConjecture_mainTheorem`, `crouzeixConjecture`,
`crouzeixRationalSpectralSetCorollary`, and `crouzeixRationalBound`.  It also audits the critical
projection, `C¹` implicit-radius, orientation, scalar and matrix Cauchy, double-layer provider,
positive-real completion, Toeplitz--Hausdorff, perturbation, and limiting declarations on their
dependency path.  The former conditional contour statements remain printed as transparent
intermediate interfaces, but their hypotheses are now discharged by
`canonicalParallelOrientedRadialBoundaryStatement`.

The final plain `lake run` completed successfully and printed these same three dependencies for
the unconditional polynomial theorem, analytic diagonal correction, and rational corollary.
