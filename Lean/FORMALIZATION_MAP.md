# Formalization map

Source locations refer to
`../preprint/the_numerical_range_is_a_2_spectral_set_v2.tex`
(1,165 lines), verified at SHA-256
`11235d02fd0d91d982cbc113495c5c6f426ce9fba75332de5d10e7bf6a1ed315`.

Statuses mean: **proved** is a checked proof term; **defined** is a
faithful encoded object or target proposition; **proved reduction** is a
checked implication used by an endpoint; and **not separately formalized**
records a statement broader than the specialization used by the completed
proof.

## Main theorem and conventions, lines 91--175

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 94--127 | Matrices, numerical range, polynomial functional calculus, Euclidean operator norm, and the constant-`2` theorem | `SquareMatrix`, `euclideanOperator`, `numericalRange`, `polynomialEval`, `PolynomialCrouzeixBound`, `MainTheoremStatement`, `crouzeixConjecture_mainTheorem`, `crouzeixConjecture` | **defined and proved**. `[Nonempty n]` records the positive-dimension convention. |
| 94--114 | Inner product, adjoint, matrix/operator norm, and polynomial-evaluation bridges | `inner_euclideanOperator_eq_star_dotProduct`, `euclideanOperator_conjTranspose`, `matrix_norm_eq_euclidean_operator_norm`, `euclideanOperator_polynomialEval` | **proved** |
| 94--127 | Compact, nonempty, convex numerical range; spectral inclusion; maximum modulus | `numericalRange_nonempty`, `isCompact_numericalRange`, `numericalRange_convex`, `matrixSpectrum_subset_numericalRange`, `exists_maxPolynomialModulusOnNumericalRange` | **proved** |
| 129--175 | Generated matrix algebra and positivity conventions | `generatedAlgebra`, `generatedAlgebra_mem_iff_exists_polynomial`, `isClosed_generatedAlgebra`, `rePart`, `IsPositiveMatrix` | **defined/proved** |

## V2 auxiliary-basis mechanism, lines 217--253

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 231--236 | For simple-spectrum `B`, build a positive-real completion of `T = f(B)` with defect in `alg(B*)` | `HasDoubleLayerCompletionProvider`, `doubleLayerCayleySeries_isPositiveRealCompletion`, `IsPositiveRealCompletion` | **proved for the polynomial specialization used by the endpoint** |
| 238--244 | `B` and `f(B)` share an eigenbasis even when the values of `f` collide; repeated sampling points are allowed | `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`, `finite_type_sampling_quadratic_nonneg`, `completionSamplePoint`, `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel` | **proved**; no injectivity condition on the target diagonal |
| 246--248 | Gramian/eigenvector/Stein argument yields `‖T‖ ≤ 2` | `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel`, `positiveRealCompletionStatement` | **proved** |
| 251--253 | The matrix and outer-domain limits yield the general case | `norm_polynomialEval_le_two_mul_of_simpleSpectrum`, `polynomialCrouzeixBound_of_simple_outer_approximants`, `crouzeixConjecture_mainTheorem` | **proved** |

## Positive-real kernels, lines 255--336

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 255--336 | Matrix Herglotz kernel and finite-sampling positivity | `matrixHerglotzKernel`, `IsPositiveMatrixKernelOn`, `finite_sampling_quadratic_nonneg`, `finite_type_sampling_quadratic_nonneg`, `matrixHerglotzKernel_isPositiveMatrixKernelOn` | **proved without a custom axiom** |
| 290--326 | Scalar Herglotz factorization and matrix positivity | `scalar_herglotz_kernel_identity`, `scalar_herglotz_kernel_factorization`, `matrixHerglotzAtom_isPositiveMatrixKernelOn` | **proved** |
| 255--336 | Positive matrix-valued Herglotz representation | The exact kernel consequence is proved directly in `MatrixHerglotz` using regularized circle averages and a limit. | The broader measure representation is **not separately formalized** and is not assumed by an endpoint. |

## Auxiliary positive-real completion, lines 338--580

| Source | Claim / formula | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 345--370 | `B = S diag(beta) S⁻¹` with distinct `beta`; `T = S diag(lambda) S⁻¹` with arbitrary `lambda` in the closed disk; defect in `alg(B*)`; conclude `‖T‖ ≤ 2` | `SimpleDiagonalization`, `IsPositiveRealCompletion`, `PositiveRealCompletionStatement`, `positiveRealCompletionStatement` | **proved**. Only the auxiliary diagonal entries are distinct. |
| 372--404 | Membership in `alg(B*)` gives the diagonal correction needed in the `B` basis, so the pullback has form `G(I-zΛ)⁻¹ + D(z)G` | `exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose`, `exists_completionDiagonalCorrection`, `exists_completionKernelModel_of_isPositiveRealCompletion` | **proved in the direction used by the endpoint**; the standalone full algebra equality is not packaged, and no algebra equality involving `T` is used. |
| 406--414 | Hermitian matrices `P,Q,Y = Q-P` | `completionP`, `completionR`, `completionX` | **defined/proved**. Lean `R` is manuscript `Q`, and Lean `X` is manuscript `Y`. |
| 415--430 | Samples `conj(lambda i)/2`, sparse vectors, and the compensating origin sample | `completionSamplePoint`, `completionSampleVector`, `completionSubstitutionMatrix`, `completion_mulVec_add_eq_zero` | **proved**. The index type is `Option n`; repeated points and `lambda i = 0` are permitted. |
| 431--451 | Exact cancellation of the unknown diagonal analytic correction | `completionUnknownHalfContribution_eq_zero`, `completionUnknownContribution_eq_zero`, `completionCorrectionKernel_sampling_eq_zero` | **proved** |
| 453--485 | Sampled blocks and `4Y-YG⁻¹P-PG⁻¹Y ⪰ 0` | `completionResolventKernel_sampling_eq_sampleCoefficient`, `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`, `completion_X_inequality_of_positiveKernel` | **proved**, with the noncommuting factor order preserved |
| 488--523 | Balancing and the two weighted Gramian series | `CompletionSquareRootData`, `completionSimilarity`, `gramian`, `completionP_congruence_eq_gramian_four`, `completionR_congruence_eq_gramian_two`, `gramian_two_sub_gramian_four_eq_tsum` | **proved with norm convergence** |
| 525--548 | Eigenvector contradiction and `I ⪯ P̂ ⪯ 2I` | `gramian_four_eigenvalues_le_two`, `gramian_four_upper_bound_posSemidef` | **proved** |
| 550--568 | Stein identity, norm estimate, and polar-unitary transfer | `gramian_stein_identity`, `norm_le_two_of_gramian_inequality`, `completionDiagonalizableMatrix_eq_unitary_conjugate`, `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel` | **proved** |
| 570--580 | Distinctness is required only for the eigenvalues of `B` | The types of `PositiveRealCompletionStatement` and `positiveRealCompletionStatement` impose no injectivity or distinct-spectrum hypothesis on `lambda` or `T`. | **encoded and proved** |

## Double-layer completion, lines 582--805

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 593--703 | Positive unital boundary map, star preservation, double-layer identity, and companion | `boundaryPhi`, `boundaryPhi_one`, `boundaryPhi_star`, `boundaryPhi_posSemidef`, `two_smul_boundaryPhi_parametricPolynomial_eq`, `parametricPolynomialCompanion_mem_generatedAlgebra` | **proved for the polynomial instances used below** |
| 705--724 | Cayley completion for the auxiliary pair `(B,T)` with `T=f(B)` and defect in `alg(B*)` | `doubleLayerCayleySeries_isPositiveRealCompletion`, `hasDoubleLayerCompletionProvider_of_boundary_data`, `hasDoubleLayerCompletionProvider_of_parametricBoundary` | **proved**; the interface explicitly carries both `B` and `T`. |
| 726--781 | Cayley series, Neumann-series subtraction, and closed-algebra membership | `doubleLayerCayleySeries_analyticOnNhd`, `doubleLayerCayleySeries_rePart_posSemidef`, `completion_sub_resolvent_mem_generatedAlgebra_conjTranspose` | **proved** |
| 783--805 | Auxiliary sharp bound for simple `B`, with possibly repeated `f(beta i)` | `HasDoubleLayerCompletionProvider`, `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`, `norm_polynomialEval_le_two_mul_of_simpleSpectrum` | **proved** |

The manuscript states parts of the double-layer layer for an arbitrary
holomorphic `f`. The endpoint needs only polynomials and their powers; that
specialization, including the contour companion and convergence statements,
is proved. The unused broader representation is not assumed.

## Boundary construction used by the provider

| Manuscript role | Lean declaration(s) | Status |
|---|---|---|
| Metric projection and `C¹` squared distance on compact convex planar sets | `convexProjection`, `convexProjection_variational`, `convexProjection_firm_nonexpansive`, `contDiff_one_convexSquaredDistance` | **proved** |
| Positive parallel-body radius, outward normal/support, and counterclockwise orientation | `contDiff_one_parallelGaugeRadius`, `outwardBoundarySupport_thickening`, `radialTangent_eq_I_mul_normal_mul_norm`, `orientedRadialConvexBoundary_thickening` | **proved** |
| Winding-one scalar Cauchy formula and matrix resolvent formula | `RadialConvexDomain.integral_polynomial_cauchy`, `integral_polynomial_cauchy_resolvent_of_simpleDiagonalization`, `hasParametricPolynomialCauchyFormula_of_simpleDiagonalization` | **proved** |
| Double-layer provider on canonical outer parallel domains | `PositivePeriodicRadialData.OrientedRadialConvexBoundary.hasDoubleLayerCompletionProvider_of_simpleDiagonalization`, `canonicalParallelOrientedRadialBoundaryStatement`, `canonicalParallelDoubleLayerStatement_of_orientedRadialBoundaries` | **proved** |

## Passage to arbitrary matrices, lines 807--959

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 813--833 | Density of simple-spectrum matrices and numerical-range perturbation | `exists_hasDistinctEigenvalues_norm_sub_lt`, `simpleSpectrumApproximation`, `tendsto_simpleSpectrumApproximation`, `numericalRange_perturbation` | **proved** |
| 835--876 | Smooth/`C¹` convex outer approximation and convergence of scalar maxima | `parallelOuterDomain`, `parallelOuterDomain_data`, `tendsto_hausdorffDist_parallelOuterDomain_closure`, `tendsto_maxPolynomialModulusOnSet_of_outerApproximation` | **proved** for the canonical positive parallel bodies |
| 892--900, 925--926 | Choose simple `Bₖ → A`, keep `W(Bₖ)` in the fixed outer domain, and pass `p(Bₖ) → p(A)` | `numericalRange_simpleSpectrumApproximation_subset_parallelOuterDomain`, `tendsto_polynomialEval`, `polynomialCrouzeixBound_of_simple_outer_approximants` | **proved** |
| 902--924 | Zero branch; otherwise direct normalization `f=p/m_Ω` and auxiliary bound | `polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero`, `norm_polynomialEval_le_two_mul_of_simpleSpectrum` | **proved**; no `f_eta` is introduced. |
| 928--939 | Let outer domains decrease to `W(A)` and pass maxima to the limit | `polynomialCrouzeixBound_of_parallelOuterDomains`, `polynomialCrouzeixBound_of_canonicalParallelOuterDomains`, `mainTheoremStatement_of_canonicalParallelDoubleLayer`, `crouzeixConjecture_mainTheorem` | **proved** |
| 941--958 | Rational constant-`2` consequence | `rationalSpectralSetCorollary_of_mainTheorem`, `crouzeixRationalSpectralSetCorollary`, `crouzeixRationalBound` | **proved separately** |

## Deleted superseded formalization

The older normalized affine `f_eta` perturbation, finite collision-set,
injective perturbed-sample, interpolation-based generated-algebra equality,
and `eta → 0` formalization has been deleted from the working tree. Those
modules and declarations are therefore absent from the current inventory and
dependency graph. Git history preserves the prior implementation.

## Active endpoint dependency chain

1. A simple auxiliary matrix `B` supplies a basis.
2. Polynomial functional calculus puts `T=f(B)` in the same basis, with
   arbitrary repeated target entries.
3. The double-layer Cayley construction gives an `alg(Bᴴ)` positive-real
   completion of `T`.
4. Repeated-point Herglotz-kernel sampling and the auxiliary completion
   theorem give `‖f(B)‖ ≤ 2`.
5. Direct normalization gives the fixed-simple polynomial estimate.
6. The simple-spectrum approximation `Bₖ → A` and the independent
   outer-domain limit give the unconditional main theorem.
7. Polynomial approximation gives the separate rational endpoint.

No collision-avoidance parameter, algebra equality
`alg(f_eta(B)) = alg(B)`, or `eta → 0` occurs in this chain.
