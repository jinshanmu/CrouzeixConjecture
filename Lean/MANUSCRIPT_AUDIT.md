# Manuscript audit

## Source identity

- Baseline file: `../LaTeX/crouzeix_conjecture_proof.tex`
- Lines: 453
- SHA-256: `037e9aafefe5fad57f0acee04b410093aa46f65c508156e80eda987ba1b1478f`
- Verification result: exact match.
- Submission-formatted article: `../AnnMath/the_numerical_range_is_a_2_spectral_set.tex`.
  Line references in this audit intentionally refer to the preserved baseline.
- Formalization toolchain: Lean 4.28.0 and Mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365` from the pinned dependency tree.

The source was read in full and treated as an unverified research proof.  The audit found no
false proposition, counterexample, inconsistent or empty hypothesis, sign error, or attempt to
replace the stated theorem by a weaker one.  The source's implicit convention `n ≥ 1` at line 16
is mathematically necessary because otherwise the numerical range is empty and its displayed
maximum is undefined.  Every final Lean theorem records it as `[Nonempty n]`.

## Positive-real completion audit, lines 30--228

The following calculations were recomputed independently and then checked in Lean:

- the scalar Herglotz identity and rank-one positive-kernel factorization;
- the pullback kernel, including the order of the noncommuting factors;
- the substitution `v = -G⁻¹ P u` and complete cancellation of the unknown diagonal correction;
- the sampled blocks `4R - 2P`, `G + R`, and `2G`, and the ordered expression
  `4X - XG⁻¹P - PG⁻¹X`;
- both Gramian series, positivity of their difference, the eigenvector contradiction, the Stein
  identity, and the square-root and polar-decomposition transfer of the Euclidean operator norm.

The matrix Herglotz kernel theorem is proved without an axiom.  The analytic diagonal correction
from lines 87--92 is also formalized exactly: `completionAnalyticDiagonalCorrection` is the
explicit matrix function `(Sᴴ X(z) S) G⁻¹`; it is proved analytic, diagonal on the disk, zero at
the origin, and reconstructive through multiplication by `G`.  The matrix-valued Herglotz measure
representation at lines 59--65 is not separately packaged, because the library instead proves
its exact required consequence directly by regularized circle averages and a limit.  Thus no
unproved measure or analytic-function representation is imported or hidden in the final theorem.

## Double-layer and convex-boundary audit, lines 230--353

The orientation and normalization were checked independently: the counterclockwise relation is
`dσ = i ν ds`, the total double-layer mass is `2I`, `Phi` carries the factor `1/2`, and the
companion term has the manuscript's adjoint sign.  Lean proves resolvent/support positivity,
positive operator-valued Bochner integration, the unital star-preserving positive boundary map,
the companion identity, every Cayley coefficient, analytic convergence, positive real part, and
closed generated-algebra membership.

The former boundary-infrastructure obligation at lines 254--283 is now closed by the following
explicit route.

1. For a nonempty compact real-convex `K ⊆ ℂ`, `convexProjection` is proved variationally
   characterized, unique, firmly nonexpansive, and continuous.  The squared distance
   `convexSquaredDistance` is proved `C¹`, with Fréchet derivative
   `2 innerSL (z - convexProjection z)`.
2. For `c ∈ K` and `r > 0`, the translated positive parallel body is open, bounded, convex, and
   contains zero.  Its inverse gauge along `exp(it)` gives a positive continuous periodic radius;
   the resulting radial point lies on exactly the frontier of `Metric.thickening r K`.
3. The squared-distance level equation is `C¹`, and its radial derivative is strictly positive.
   The proved scalar implicit-function theorem identifies the local implicit root with the
   inverse-gauge radius and yields `contDiff_one_parallelGaugeRadius` globally.
4. The normalized projection residual gives the continuous outward unit normal.  Projection
   variational inequalities prove the supporting-half-plane condition and its strictly positive
   component in the outward radial direction.
5. Differentiating the constant squared-distance boundary equation proves normal--tangent
   orthogonality.  The positive radial component fixes the sign and proves the exact
   counterclockwise identity
   `tangent = Complex.I * normal * ‖tangent‖`.
6. The radial contour proof uses the principal complex logarithm to show winding one for every
   point of the convex interior.  The fundamental theorem of calculus and polynomial one-form
   integration prove the scalar polynomial Cauchy formula.  Entrywise integration after explicit
   simple diagonalization proves the matrix resolvent Cauchy formula.
7. These results construct `HasParametricPolynomialCauchyFormula`, then
   `hasDoubleLayerCompletionProvider_of_simpleDiagonalization`; no contour formula remains as a
   hypothesis of the final theorem.

The manuscript phrases parts of this layer for a general analytic boundary function.  The exact
polynomial and Cayley instances used by the proof, including their holomorphic matrix-algebra and
convergence consequences, are proved.  A broader unused representation theorem is not assumed in
place of them.

## Perturbation, outer limit, and main estimate, lines 355--438

The audit checked the simple-spectrum perturbation normalization, the finite exceptional set,
the generated-algebra interpolation step, numerical-range perturbation, and both limiting
arguments.  Toeplitz--Hausdorff convexity, compactness and nonemptiness of the numerical range,
simple-spectrum density, and the compact outer-set maximum limit are proved.

Canonical outer domains are the positive parallel bodies
`parallelOuterDomain (numericalRange A) k`.  Their compact/convex/Hausdorff properties and strict
containment of the perturbed numerical range are proved.  The boundary construction above gives
`canonicalParallelOrientedRadialBoundaryStatement`, which supplies the double-layer provider;
the canonical outer-limit theorem then proves
`crouzeixConjecture_mainTheorem : MainTheoremStatement`.  The exported pointwise theorem
`crouzeixConjecture A p` has exactly the manuscript's matrices, complex polynomials, numerical
range, constant `2`, and induced Euclidean operator norm.

## Rational spectral-set corollary, lines 439--450

The rational discussion is kept separate from the polynomial theorem.  The library uses
Mathlib's canonical reduced numerator and denominator, defines pole-freeness on exactly the
numerical range, proves uniform polynomial approximation by convex separation and explicit
geometric polynomials, and proves convergence of both matrix evaluations and numerical-range
maxima.  No Runge axiom is used.  The final declarations are
`crouzeixRationalSpectralSetCorollary` and its pointwise specialization
`crouzeixRationalBound`, with the same constant `2` and induced Euclidean norm.

## Gap determination and verification boundary

No mathematical flaw has been established, and no mathematical or formalization hypothesis
remains in the polynomial theorem or rational corollary.  In particular, the previously isolated
`CanonicalParallelDoubleLayerStatement` is now proved from constructed radial boundary data; it
is not an assumption of `crouzeixConjecture_mainTheorem`.

The permanent proof avoids `sorry`, `admit`, custom axioms, unsafe proof construction, native
decision shortcuts, runtime-generated proofs, and compiler-trust shortcuts.  Classical choice
used to select points/eigenvalue data is exposed to the axiom audit.  Focused targets along the
completed geometry and final-theorem path are clean.  The authoritative final plain `lake build`
and plain `lake run` both pass with zero errors and zero warnings; the latter prints only
propositional extensionality, classical choice, and quotient soundness for every audited result.
All verification commands were executed serially.
