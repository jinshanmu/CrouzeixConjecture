# Formalization map

Source locations refer to
`../preprint/the_numerical_range_is_a_2_spectral_set_v3.tex`
(1,066 lines), verified at SHA-256
`f190178bc197c5f62fa8146f96c932a241379e90bf63145d542035058b92d154`.

Statuses mean: **proved** is a checked proof term; **defined** is a
faithful encoded object or target proposition; **proved reduction** is a
checked implication used by an endpoint; and **not separately formalized**
records a statement broader than the specialization used by the completed
proof.

## Main theorem and conventions, lines 92--257

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 95--130 | Matrices, numerical range, Euclidean operator norm, and the constant-`2` theorem | `SquareMatrix`, `euclideanOperator`, `numericalRange`, `polynomialEval`, `PolynomialCrouzeixBound`, `MainTheoremStatement`, `crouzeixConjecture_mainTheorem`, `crouzeixConjecture` | **proved for the polynomial specialization**. The manuscript's broader holomorphic-function statement is not separately encoded. |
| 95--151 | Inner product, adjoint, compact convex numerical range, spectral inclusion, and positivity conventions | `inner_euclideanOperator_eq_star_dotProduct`, `euclideanOperator_conjTranspose`, `numericalRange_convex`, `matrixSpectrum_subset_numericalRange`, `rePart`, `IsPositiveMatrix` | **defined/proved** |

## V3 auxiliary-basis mechanism, lines 220--257

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 225--239 | For simple-spectrum `B`, build a positive-real completion of `T = f(B)` with defect in `alg(B*)` | `HasDoubleLayerCompletionProvider`, `parametric_direct_cayley_identity`, `isPositiveRealCompletion_of_direct_cayley_identity`, `IsPositiveRealCompletion` | **proved for the polynomial specialization used by the endpoint** |
| 241--247 | `B` and `f(B)` share an eigenbasis even when values collide; repeated sampling points are allowed | `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`, `finite_type_sampling_quadratic_nonneg`, `completionSamplePoint` | **proved** |
| 249--252 | The positive Gramian difference and first nonconstant term yield `‖T‖ ≤ 2` | `gramian_four_eigenvalues_le_two`, `gramian_four_sub_one_sub_first_posSemidef`, `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel` | **proved without a Stein identity** |
| 255--257 | First pass simple matrices to `A` in a fixed outer domain, then shrink the domain | `norm_polynomialEval_le_two_mul_max_on_fixed_outerDomain`, `polynomialCrouzeixBound_of_parallelOuterDomains`, `crouzeixConjecture_mainTheorem` | **proved** |

## Positive-real kernels, lines 259--313

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 259--313 | Matrix Herglotz kernel and finite-sampling positivity | `matrixHerglotzKernel`, `IsPositiveMatrixKernelOn`, `finite_sampling_quadratic_nonneg`, `finite_type_sampling_quadratic_nonneg`, `matrixHerglotzKernel_isPositiveMatrixKernelOn` | **proved without a custom axiom** |
| 294--312 | Scalar Herglotz factorization and matrix positivity | `scalar_herglotz_kernel_identity`, `scalar_herglotz_kernel_factorization`, `matrixHerglotzAtom_isPositiveMatrixKernelOn` | **proved** |
| 259--313 | Positive matrix-valued Herglotz representation | The exact kernel consequence is proved directly in `MatrixHerglotz` using regularized circle averages and a limit. | The broader measure representation is **not separately formalized** and is not assumed by an endpoint. |

## Auxiliary positive-real completion, lines 315--544

| Source | Claim / formula | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 322--347 | `B = S diag(beta) S⁻¹` with distinct `beta`; `T = S diag(lambda) S⁻¹` with arbitrary `lambda` in the closed disk; defect in `alg(B*)`; conclude `‖T‖ ≤ 2` | `SimpleDiagonalization`, `IsPositiveRealCompletion`, `PositiveRealCompletionStatement`, `positiveRealCompletionStatement` | **proved**. Only the auxiliary diagonal entries are distinct. |
| 349--377 | Membership in `alg(B*)` gives the diagonal correction needed in the `B` basis, so the pullback has form `G(I-zΛ)⁻¹ + D(z)G` | `exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose`, `exists_completionDiagonalCorrection`, `exists_completionKernelModel_of_isPositiveRealCompletion` | **proved in the direction used by the endpoint**; the standalone full algebra equality is not packaged, and no algebra equality involving `T` is used. |
| 379--389 | Hermitian matrices `P,Q,Y = Q-P` | `completionP`, `completionR`, `completionX` | **defined/proved**. Lean `R` is manuscript `Q`, and Lean `X` is manuscript `Y`. |
| 390--405 | Samples `conj(lambda i)/2`, sparse vectors, and the compensating origin sample | `completionSamplePoint`, `completionSampleVector`, `completionSubstitutionMatrix`, `completion_mulVec_add_eq_zero` | **proved**. The index type is `Option n`; repeated points and `lambda i = 0` are permitted. |
| 406--426 | Exact cancellation of the unknown diagonal analytic correction | `completionUnknownHalfContribution_eq_zero`, `completionUnknownContribution_eq_zero`, `completionCorrectionKernel_sampling_eq_zero` | **proved** |
| 428--463 | Sampled blocks and `4Y-YG⁻¹P-PG⁻¹Y ⪰ 0` | `completionResolventKernel_sampling_eq_sampleCoefficient`, `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`, `completion_X_inequality_of_positiveKernel` | **proved**, with the noncommuting factor order preserved |
| 465--493 | Balancing and the two weighted Gramian series | `CompletionSquareRootData`, `completionSimilarity`, `gramian`, `completionP_congruence_eq_gramian_four`, `completionR_congruence_eq_gramian_two`, `gramian_two_sub_gramian_four_eq_tsum` | **proved with norm convergence** |
| 495--519 | Eigenvector contradiction and `I ⪯ P̂ ⪯ 2I` | `gramian_four_eigenvalues_le_two`, `gramian_four_upper_bound_posSemidef` | **proved** |
| 520--530 | First-term Gramian estimate, norm bound, and polar-unitary transfer | `gramian_mulVec_eq_of_mulVec_eq_zero`, `gramian_four_sub_one_sub_first_posSemidef`, `norm_le_two_of_gramian_inequality`, `completionDiagonalizableMatrix_eq_unitary_conjugate`, `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel` | **proved without Stein machinery** |
| 333--335, 540--543 | Distinctness is required only for the eigenvalues of `B` | The types of `PositiveRealCompletionStatement` and `positiveRealCompletionStatement` impose no injectivity or distinct-spectrum hypothesis on `lambda` or `T`. | **encoded and proved** |

## Double-layer completion, lines 546--762

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 557--668 | Positive unital boundary map, star preservation, double-layer identity, and companion | `boundaryPhi`, `boundaryPhi_one`, `boundaryPhi_star`, `boundaryPhi_posSemidef`, `two_smul_boundaryPhi_parametric_eq`, `parametricBoundaryCompanion_mem_generatedAlgebra` | **proved for the polynomial instances used below** |
| 670--738 | Direct Cayley completion for `(B,T)` and defect `(g(B)ᴴ-I)/2` in `alg(B*)` | `matrixCayleyTransform_eq_two_resolvent_sub_one`, `isPositiveRealCompletion_of_direct_cayley_identity` | **proved as the direct algebraic implication** |
| 670--738 | Concrete polynomial contour provider | `doubleLayerCayleySeries_analyticOnNhd`, `doubleLayerCayleySeries_rePart_posSemidef`, `parametricBoundaryFirstPartIntegral_cayley_eq`, `parametricCayleyCompanion_mem_generatedAlgebra`, `parametric_direct_cayley_identity`, `hasDoubleLayerCompletionProvider_of_parametricBoundary` | **proved**. A uniform series bridge supplies the special Cayley Cauchy identity because the current contour calculus is polynomial-only. |
| 740--762 | Auxiliary sharp bound for simple `B`, with possibly repeated `f(beta i)` | `HasDoubleLayerCompletionProvider`, `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`, `norm_polynomialEval_le_two_mul_of_simpleSpectrum` | **proved** |

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

## Passage to arbitrary matrices, lines 764--881

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 770--791 | Density of simple-spectrum matrices and numerical-range perturbation | `exists_hasDistinctEigenvalues_norm_sub_lt`, `simpleSpectrumApproximation`, `tendsto_simpleSpectrumApproximation`, `numericalRange_perturbation` | **proved** |
| 793--825 | Smooth/`C¹` convex outer approximation and convergence of scalar maxima | `parallelOuterDomain`, `parallelOuterDomain_data`, `tendsto_maxPolynomialModulusOnSet_of_outerApproximation` | **proved** for the canonical positive parallel bodies |
| 827--864 | Fix an outer domain, choose eventual simple `Bₖ → A` inside it, and pass `p(Bₖ) → p(A)` | `eventually_numericalRange_subset_open_of_tendsto`, `norm_polynomialEval_le_two_mul_max_on_fixed_outerDomain` | **proved** |
| 848--859 | Zero branch; otherwise direct normalization and auxiliary bound | `polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero`, `norm_polynomialEval_le_two_mul_of_simpleSpectrum` | **proved**; no `f_eta` is introduced. |
| 867--875 | Let outer domains decrease to `W(A)` and pass maxima to the limit | `polynomialCrouzeixBound_of_parallelOuterDomains`, `polynomialCrouzeixBound_of_canonicalParallelOuterDomains`, `mainTheoremStatement_of_canonicalParallelDoubleLayer`, `crouzeixConjecture_mainTheorem` | **proved** |
| 877--880 | Rational constant-`2` consequence | `rationalSpectralSetCorollary_of_mainTheorem`, `crouzeixRationalSpectralSetCorollary`, `crouzeixRationalBound` | **proved separately** |

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
6. For each fixed outer domain, simple-spectrum `Bₖ → A`; the subsequent
   outer-domain limit gives the unconditional polynomial theorem.
7. Polynomial approximation gives the separate rational endpoint.

No collision-avoidance parameter, algebra equality
`alg(f_eta(B)) = alg(B)`, or `eta → 0` occurs in this chain.
