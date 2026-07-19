# Continuation status

The verified baseline manuscript is `../LaTeX/crouzeix_conjecture_proof.tex`, 453 lines, SHA-256
`037e9aafefe5fad57f0acee04b410093aa46f65c508156e80eda987ba1b1478f`.
The submission-formatted article is
`../AnnMath/the_numerical_range_is_a_2_spectral_set.tex`; the line-number
cross-references below intentionally use the preserved baseline source.

The project uses Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  The committed dependency
manifest pins the transitive dependency tree, while downloaded packages and
build products remain local under `.lake/`.

## Mathematical status

The manuscript's polynomial theorem is now proved unconditionally for every nonempty finite
complex Euclidean matrix space:

- `crouzeixConjecture_mainTheorem : MainTheoremStatement` proves the exact quantified target;
- `crouzeixConjecture A p` displays the estimate
  `‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulusOnNumericalRange A p`;
- `[Nonempty n]` makes the manuscript's implicit positive-dimension convention explicit;
- the norm is the induced Euclidean operator norm, and the matrix/operator and complex
  inner-product convention bridges are proved in the library.

The manuscript's rational spectral-set discussion is a separate proved corollary:
`crouzeixRationalSpectralSetCorollary`, with pointwise form `crouzeixRationalBound`.  It uses the
same constant `2`, the same numerical range and induced Euclidean matrix norm, and assumes that
the reduced rational denominator is pole-free on exactly the numerical range.

No mathematical flaw, false source proposition, counterexample, inconsistent assumption, or
sign error has been found.

## Completed proof route

1. The finite complex Euclidean model, inner-product convention, induced operator norm,
   numerical range, adjoint, polynomial evaluation, positivity, spectrum, generated algebra,
   compactness, nonemptiness, spectral inclusion, and Toeplitz--Hausdorff convexity are proved.
2. The positive-real completion argument is proved through diagonalization, kernel sampling,
   cancellation, the three auxiliary matrices, Gramian series, the eigenvector argument, Stein
   identity, square roots, and polar decomposition.  The matrix Herglotz kernel theorem is
   proved without an axiom.  The manuscript's analytic diagonal correction `D` is explicitly
   constructed as `(Sᴴ X(z) S) G⁻¹`, proved analytic and diagonal, normalized at zero, and proved
   to reconstruct the correction as `D(z)G`.  The matrix-valued Herglotz measure is not separately
   packaged; its exact kernel consequence is proved directly.
3. The double-layer support/resolvent algebra, positive operator-valued Bochner integration,
   boundary map, companion transform, Cayley coefficients, analytic positive-real completion,
   and generated-algebra membership are proved.
4. For a nonempty compact convex planar set `K` and `r > 0`, the metric projection is developed
   through its variational inequality and firm nonexpansiveness.  The squared distance to `K`
   is proved `C¹`, with derivative twice the projection residual.
5. The boundary of `Metric.thickening r K` is parametrized by the inverse gauge about a point of
   `K`.  A scalar implicit-function theorem applied to the squared-distance level equation proves
   the inverse-gauge radius is `C¹`.  Projection residuals supply the continuous outward unit
   normal, support inequality, orthogonality, and positive radial component; these yield the
   exact counterclockwise identity `tangent = i * normal * speed`.
6. The radial contour proof establishes winding one by the principal logarithm and the
   fundamental theorem of calculus, proves the polynomial Cauchy formula, and obtains the matrix
   resolvent formula entrywise from explicit simple diagonalization.  This constructs
   `HasParametricPolynomialCauchyFormula` and then the full double-layer completion provider.
7. Canonical positive parallel bodies of the numerical range provide the required oriented
   boundaries.  Simple-spectrum perturbation and the canonical outer-domain limit then prove
   `crouzeixConjecture_mainTheorem`.
8. Convex separation, explicit geometric polynomials, denominator factorization, and the matrix
   and maximum limits prove the separate rational corollary without a Runge axiom.

## Verification checkpoint

There are no remaining mathematical or formalization obligations for the stated polynomial or
rational results.  Focused target builds and the final authoritative plain `lake build` are clean.
The final plain `lake run` also passes: its internal plain build succeeds and
`lake env lean AxiomAudit.lean` prints only `propext`, `Classical.choice`, and `Quot.sound` for
every audited theorem.  All Lean/Lake invocations were run serially.
