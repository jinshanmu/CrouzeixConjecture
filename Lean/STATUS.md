# Formalization status

- Active manuscript: all 1,106 lines of
  `../preprint/the_numerical_range_is_a_2_spectral_set_v4.tex` were reviewed;
  SHA-256
  `5713de029c4a7486e25e86d16e6413d04929bdf5f92439c3237d4a930b1c9242`.
- Toolchain: Lean 4.28.0 with Mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; dependencies and build
  products are local under `.lake/`.
- Faithful finite-matrix target: proved. `holomorphicCrouzeixBound` assumes an
  open neighborhood `U` of the numerical range and complex differentiability
  of `f` on `U`, and gives the exact constant `2` for
  `holomorphicMatrixEval A f`. The calculus is identified with admissible
  contour integrals, is local near `W(A)`, satisfies the algebra laws, and
  agrees with polynomial and reduced-rational evaluation. `crouzeixConjecture`
  is the direct polynomial specialization;
  `[Nonempty n]` records the necessary positive-dimension convention.
- Euclidean matrix/operator model: proved, including the complex inner-product
  convention, adjoint and norm bridges, polynomial evaluation, spectrum,
  numerical range, generated algebra, and Toeplitz--Hausdorff convexity.
- Auxiliary-basis completion: proved. `PositiveRealCompletionStatement`
  accepts a simple diagonalization of `B`, an arbitrary target diagonal
  `lambda` in that same basis, and a completion whose defect lies in
  `alg(Bᴴ)`. Neither `lambda` nor the target matrix needs simple spectrum.
- Shared-basis functional calculus: proved by
  `SimpleDiagonalization.functionEval`. Thus `T = f(B)` has the required
  common basis even when the values `f(βᵢ)` repeat.
- Kernel sampling and endpoint: proved for arbitrary finite sample index types
  and repeated sample points, through
  `finite_type_sampling_quadratic_nonneg`,
  `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`, and
  `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel`.
- Simplified Gramian endpoint: proved directly from the first nonconstant
  Gramian term by `gramian_four_sub_one_sub_first_posSemidef`; the former
  Stein machinery and wrapper module have been removed.
- Double layer: proved relative to the auxiliary matrix, including the
  companion transform in `alg(B)`, the direct Cayley algebraic implication,
  positive-real completion,
  and the absence of any generated-algebra equality requirement between
  `B` and `f(B)`.
- Holomorphic simple-spectrum estimate: proved by direct scalar and matrix
  Cauchy formulas and `HasParametricPowerCauchyFormula`, followed by the same
  positive-real completion theorem. The parameter-space positive map is
  explicitly bounded, which gives analyticity of the Cayley series. For the
  manuscript's arbitrary open neighborhood of the compact closed domain, the
  formal proof selects a convex thickening inside that neighborhood.
- Final limit: proved in v4 order. For each fixed outer body, simple-spectrum
  `Bₖ → A` gives the fixed-domain estimate; only then do the canonical
  parallel bodies shrink to `W(A)`. For the holomorphic theorem the proof uses
  a sufficiently small tail whose closed bodies remain inside the given open
  neighborhood.
- Superseded route removed: the `f_eta`, collision-avoidance,
  interpolation-based algebra-equality, and `eta → 0` formalization has been
  deleted from the working tree. Git history preserves the prior version.
- Notation: Lean `completionR` and `completionX` correspond to manuscript
  `Q` and `Y`; `completionP` corresponds to `P`.
- Finite consequences: `holomorphicMatrixEval_rational` and
  `holomorphicCrouzeixRationalBound` derive the rational estimate directly
  from the holomorphic theorem. `finiteRationalSpectralSetCorollary` packages
  compactness, spectrum containment, and the bound. Both polynomial and
  rational matrix-function error estimates are proved.
- Ordinary sharpness: `crouzeixConstantTwo_isLeast_finTwo` proves that the
  constant `2` is least even after restricting the rational statement to
  `2 × 2` matrices.
- Hilbert polynomial consequence: proved by
  `hilbertSpacePolynomialCrouzeix`, using finite-dimensional transport and
  finite Krylov compression for arbitrary complete nonzero complex Hilbert
  spaces.
- Hilbert rational consequence: `spectrum_subset_closedOperatorNumericalRange`
  proves the required spectral containment; `operatorRationalEval` is the
  approximation-based rational calculus on the compact convex closed
  numerical range; and `hilbertSpaceRationalSpectralSet` packages containment
  with `hilbertSpaceRationalCrouzeix`. Polynomial compatibility is proved by
  `operatorRationalEval_algebraMap_polynomial`, while
  `operatorRationalEval_eq_num_mul_inverse_denom` identifies the construction
  with the standard reduced rational calculus.
  `closedOperatorNumericalRange_isTwoSpectralSet` is the complete
  compactness, spectrum-containment, and rational-bound package. The
  construction proves the required finite-denominator approximation rather
  than assuming a Runge or Mergelyan axiom.
- Scaled `q` source: all 669 lines of
  `../preprint/q_numerical_range_spectral_set.tex` were reviewed; SHA-256
  `69862abf0f290975767dfd84dc998509da90c34982302927a19b45edcaa22771`.
- Scaled `q` geometry: proved.  The formal development includes phase
  reduction, parameter identities, compactness/nonemptiness, Tsing's exact
  disk-union formula, nesting, numerical-range inclusion, and spectral
  inclusion.  Tsing convexity is not assumed as an axiom.
- Reusable transfer: proved for rational functions by
  `rationalScaledQNumericalRangeBound_of_universal`.  It transfers `K` to
  `max 1 (K / qKappa ‖q‖)` through adapted rank-one positive stretches,
  Möbius transforms, spectral mapping, orbit extraction, and an
  `M + epsilon` argument.
- Sharp scaled `q` endpoint: proved by
  `sharpRationalScaledQNumericalRangeBound`, with polynomial specialization
  `sharpPolynomialScaledQNumericalRangeBound`.  The constant is exactly
  `max 1 (2 * ‖q‖ / (1 + √(1 - ‖q‖ ^ 2)))`.
- Scaled `q` optimality: proved.  Constant functions force the branch `1`,
  the `2 × 2` Jordan nilpotent forces `2 / qKappa r`, and
  `sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex` packages the
  exact least-constant result for every admissible complex `q`.
- Scaled `q` manuscript match: complete.  The paper states the exact rational
  spectral-set assertion and uses only the adapted rank-one stretches.  Lean
  formalizes the same hypotheses, intermediate lemmas, transfer theorem,
  polynomial specialization, and fixed-complex-parameter sharpness result.
- Authoritative verification: run `lake build`, followed serially by
  `lake env lean AxiomAudit.lean`.
