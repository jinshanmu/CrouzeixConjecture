# Formalization status

- Baseline manuscript: all 453 lines read; SHA-256 verified as
  `037e9aafefe5fad57f0acee04b410093aa46f65c508156e80eda987ba1b1478f`.
- Submission article: `../AnnMath/the_numerical_range_is_a_2_spectral_set.tex`;
  audit line references intentionally use the preserved baseline source.
- Toolchain: Lean 4.28.0 with Mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; dependencies and build products are local under
  `.lake/`.
- Faithful target: proved.  `crouzeixConjecture` states the manuscript's matrices,
  polynomials, numerical range, induced Euclidean operator norm, and exact constant `2`.
  `[Nonempty n]` records the necessary positive-dimension convention.
- Euclidean matrix/operator model: proved, including the complex inner-product convention,
  adjoint bridge, norm bridge, polynomial evaluation bridge, spectrum, numerical range,
  generated algebra, and Toeplitz--Hausdorff convexity.
- Positive-real completion: proved, including matrix Herglotz kernel positivity, the explicit
  analytic diagonal correction `D`, diagonalization, cancellation, Gramian series, eigenvector
  and Stein arguments, square roots, and polar decomposition.  The source's general
  Herglotz-measure representation is not separately constructed; its exact kernel consequence is
  proved directly.
- Double layer: proved, including boundary support and resolvents, positive Bochner integration,
  the companion transform, Cayley series, positive-real completion, and generated-algebra
  membership.
- Convex-boundary geometry: proved.  The route is projection squared-distance `C¹`, inverse
  gauge, a scalar implicit-function argument for the `C¹` radius, projection normal and support,
  tangent orthogonality and positive orientation, and the exact normal/arclength relation.
- Cauchy/provider layer: proved.  Principal-log winding and polynomial one-form integration give
  the radial scalar Cauchy formula; explicit simple diagonalization gives the matrix resolvent
  formula and the double-layer completion provider.
- Final limit: proved.  Canonical parallel bodies, simple-spectrum perturbation, and the outer
  limit yield `crouzeixConjecture_mainTheorem : MainTheoremStatement` unconditionally.
- Rational result: proved separately as `crouzeixRationalSpectralSetCorollary`, with pointwise
  theorem `crouzeixRationalBound` and no Runge axiom.
- Adversarial audit: no mathematical flaw, counterexample, inconsistent assumption, or sign
  error found.
- Verification: the final authoritative serial plain `lake build` and plain `lake run` both pass
  with zero errors and zero warnings.  The default run rebuilds the library and checks
  `AxiomAudit.lean`.
