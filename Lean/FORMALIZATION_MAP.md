# Formalization map

Source locations refer to
`../preprint/the_numerical_range_is_a_2_spectral_set_v4.tex`
(1,106 lines), verified at SHA-256
`5713de029c4a7486e25e86d16e6413d04929bdf5f92439c3237d4a930b1c9242`.

Statuses mean: **proved** is a checked proof term; **defined** is a
faithful encoded object or target proposition; and **proved reduction** is a
checked implication used by an endpoint.

## Main theorem and conventions, lines 91--255

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 94--129 | Matrices, numerical range, holomorphic functional calculus, and the constant-`2` theorem | `SquareMatrix`, `euclideanOperator`, `numericalRange`, `holomorphicMatrixEval`, `parametricBoundaryIntegral_eq_holomorphicMatrixEval`, `holomorphicMatrixEval_congr_on_neighborhood`, `holomorphicCrouzeixBound` | **proved** with exactly an open neighborhood `U` of `W(A)` and `DifferentiableOn ℂ f U`. |
| 104--129 | Compactness, spectral containment, and the rational definition-level consequence | `isCompact_numericalRange`, `matrixSpectrum_subset_numericalRange`, `holomorphicMatrixEval_rational`, `holomorphicCrouzeixRationalBound`, `finiteRationalSpectralSetCorollary` | **proved** as a direct specialization of the holomorphic theorem. |
| 131--138 | Optimality already for `J = [[0,1],[0,0]]` and `p(z)=z` | `maxPolynomialModulusOnNumericalRange_X_jordanNilpotentTwo`, `jordanNilpotentTwo_attains_two`, `crouzeixConstantTwo_isLeast_finTwo` | **proved** with the manuscript's normalization. |
| 94--148 | Inner product, adjoint, compact convex numerical range, spectrum, and positivity conventions | `inner_euclideanOperator_eq_star_dotProduct`, `euclideanOperator_conjTranspose`, `numericalRange_convex`, `matrixSpectrum_subset_numericalRange`, `rePart`, `IsPositiveMatrix` | **defined/proved** |
| 218--255 | Auxiliary-basis de-symmetrization mechanism | `SimpleDiagonalization.functionEval`, `IsPositiveRealCompletion`, `finite_type_sampling_quadratic_nonneg`, `completionSamplePoint`, `gramian_four_sub_one_sub_first_posSemidef` | **proved** with repeated target values and repeated sampling points allowed. |

## Positive-real kernels, lines 257--310

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 260--310 | Matrix Herglotz kernel and finite-sampling positivity | `matrixHerglotzKernel`, `IsPositiveMatrixKernelOn`, `finite_sampling_quadratic_nonneg`, `finite_type_sampling_quadratic_nonneg`, `matrixHerglotzKernel_isPositiveMatrixKernelOn` | **proved by the same regularized circle-average argument and radial limit.** |

## Auxiliary positive-real completion, lines 312--543

| Source | Claim / formula | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 319--344 | `B = S diag(beta) S⁻¹` with distinct `beta`; `T = S diag(lambda) S⁻¹` with arbitrary `lambda` in the closed disk; defect in `alg(B*)`; conclude `‖T‖ ≤ 2` | `SimpleDiagonalization`, `IsPositiveRealCompletion`, `PositiveRealCompletionStatement`, `positiveRealCompletionStatement` | **proved**. Only the auxiliary diagonal entries are distinct. |
| 346--373 | Membership in `alg(B*)` gives the diagonal correction needed in the `B` basis | `exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose`, `exists_completionDiagonalCorrection`, `exists_completionKernelModel_of_isPositiveRealCompletion` | **proved in exactly the used direction**; no generated-algebra equality involving `T` is assumed. |
| 375--386 | Hermitian matrices `P,Q,Y = Q-P` | `completionP`, `completionR`, `completionX` | **defined/proved**. Lean `R` is manuscript `Q`, and Lean `X` is manuscript `Y`. |
| 387--423 | Samples `conj(lambda i)/2`, the origin sample, and cancellation of the unknown correction | `completionSamplePoint`, `completionSampleVector`, `completionSubstitutionMatrix`, `completion_mulVec_add_eq_zero`, `completionCorrectionKernel_sampling_eq_zero` | **proved**. Repeated points and `lambda i = 0` are permitted. |
| 425--462 | Sampled blocks and `4Y-YG⁻¹P-PG⁻¹Y ⪰ 0` | `completionResolventKernel_sampling_eq_sampleCoefficient`, `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`, `completion_X_inequality_of_positiveKernel` | **proved**, preserving noncommuting factor order. |
| 464--499 | Balancing and the two weighted Gramian series | `CompletionSquareRootData`, `completionSimilarity`, `gramian`, `completionP_congruence_eq_gramian_four`, `completionR_congruence_eq_gramian_two`, `gramian_two_sub_gramian_four_eq_tsum` | **proved with norm convergence**. |
| 501--530 | Eigenvector contradiction, first-term estimate, and polar-unitary transfer | `gramian_four_eigenvalues_le_two`, `gramian_four_sub_one_sub_first_posSemidef`, `norm_le_two_of_gramian_inequality`, `completionDiagonalizableMatrix_eq_unitary_conjugate`, `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel` | **proved without a Stein identity**. |

## Radial double-layer completion, lines 545--774

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 556--650 | Supported oriented radial boundary and a bounded positive unital parameter-space map | `ParametricConvexBoundary`, `boundaryPhi`, `boundaryPhi_one`, `boundaryPhi_star`, `boundaryPhi_posSemidef`, `boundaryPhi_norm_le`, `boundaryPhiCLM` | **defined/proved** for the compact contour parameter space; the interval parametrization is supplied by the radial boundary package. |
| 590--650 | Positive density, total mass, and boundedness | `doubleLayerResolvent_density_posSemidef`, `parametricPositiveBoundaryDensityOfMass`, `HasParametricPowerCauchyFormula.mass_eq_one`, `boundaryPhi_norm_le` | **proved** from the support and Cauchy identities used later. |
| 652--750 | Analytic Cayley series, power Cauchy identities, companion membership, and positive-real completion | `HasParametricPowerCauchyFormula`, `doubleLayerCayleySeries_analyticOnNhd`, `doubleLayerCayleySeries_rePart_posSemidef`, `parametricBoundaryFirstPartIntegral_cayley_eq_of_powerCauchy`, `parametricPowerCayleyCompanion_mem_generatedAlgebra`, `parametric_direct_cayley_identity_of_powerCauchy`, `exists_positiveRealCompletion_of_parametricPowerCauchy` | **proved** with exactly the powers consumed by the Cayley series. |
| 752--774 | Auxiliary sharp bound for simple `B`, with possibly repeated `f(beta i)` | `SimpleDiagonalization.functionEval`, `SimpleDiagonalization.functionEval_pow`, `hasParametricPowerCauchyFormula_of_holomorphic_of_simpleDiagonalization`, `norm_functionEval_le_two_of_holomorphic_of_simpleDiagonalization` | **proved** under the manuscript's bounded radial-domain, open-neighborhood, holomorphy, and unit-bound hypotheses. |

The holomorphic endpoint preserves the same scalar mechanism. A direct scalar
Cauchy formula on a convex neighborhood is lifted entrywise through the
auxiliary diagonalization. Compatibility with powers supplies exactly the
order-sensitive data needed by the Cayley series and positive-real
completion; no stronger representation theorem is assumed.

## Boundary construction used by the provider

| Manuscript role | Lean declaration(s) | Status |
|---|---|---|
| Metric projection and `C¹` squared distance on compact convex planar sets | `convexProjection`, `convexProjection_variational`, `convexProjection_firm_nonexpansive`, `contDiff_one_convexSquaredDistance` | **proved** |
| Positive parallel-body radius, outward normal/support, and counterclockwise orientation | `contDiff_one_parallelGaugeRadius`, `outwardBoundarySupport_thickening`, `radialTangent_eq_I_mul_normal_mul_norm`, `orientedRadialConvexBoundary_thickening` | **proved** |
| Winding-one scalar and matrix holomorphic Cauchy formulas | `RadialConvexDomain.integral_holomorphic_cauchy`, `integral_holomorphic_cauchy_resolvent_of_simpleDiagonalization`, `hasParametricPowerCauchyFormula_of_holomorphic_of_simpleDiagonalization` | **proved** by selecting an open convex buffer inside the supplied open neighborhood of the compact closed radial domain. |
| Supported oriented radial boundary on canonical outer parallel domains | `orientedRadialConvexBoundary_thickening`, `exists_orientedRadialConvexBoundary_thickening`, `canonicalParallelOrientedRadialBoundaryStatement` | **proved** |

## Holomorphic functional calculus and main limit, lines 776--910

| Claim | Lean declaration(s) | Status / translation |
|---|---|---|
| A fixed supported contour depends continuously on the matrix and agrees with simple-spectrum evaluation | `continuousOn_parametricBoundaryIntegral`, `parametricBoundaryIntegral_eq_functionEval`, `tendsto_simpleSpectrumHolomorphicEval` | **proved** |
| Contour independence and totalized finite-matrix calculus | `parametricBoundaryIntegral_eq_of_two_orientedRadialBoundaries`, `holomorphicMatrixEval`, `parametricBoundaryIntegral_eq_holomorphicMatrixEval` | **proved** under the local holomorphy assumptions; the totalized definition is only used through these identifications. |
| Locality and algebra laws | `holomorphicMatrixEval_congr_on_neighborhood`, `holomorphicMatrixEval_add`, `holomorphicMatrixEval_neg`, `holomorphicMatrixEval_sub`, `holomorphicMatrixEval_mul` | **proved** on the common open neighborhood used by the calculus. |
| Polynomial and reduced-rational compatibility | `holomorphicMatrixEval_polynomial`, `holomorphicMatrixEval_rational` | **proved**; the rational theorem assumes pole-freeness on exactly `W(A)`. |
| Exact maximum and shrinking outer bodies | `maxFunctionModulusOnSet`, `tendsto_maxFunctionModulusOnSet_of_outerApproximation`, `norm_holomorphicMatrixEval_le_two_mul_on_fixedRadialDomain`, `holomorphicCrouzeixBound` | **proved**. A sufficiently small tail of the canonical bodies has closure in the given open neighborhood; no global extension of `f` is required. |

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 782--803 | Density of simple-spectrum matrices and numerical-range perturbation | `exists_hasDistinctEigenvalues_norm_sub_lt`, `simpleSpectrumApproximation`, `tendsto_simpleSpectrumApproximation`, `numericalRange_perturbation` | **proved**. |
| 805--852 | Canonical convex parallel domains with supported oriented radial boundaries | `parallelOuterDomain`, `parallelOuterDomain_data`, `canonicalParallelOrientedRadialBoundaryStatement` | **proved**. |
| 854--910 | Fixed-domain simple-spectrum limit followed by the outer-domain limit | `tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood`, `norm_holomorphicMatrixEval_le_two_mul_on_fixedRadialDomain`, `tendsto_maxFunctionModulusOnSet_of_outerApproximation`, `holomorphicCrouzeixBound` | **proved in the manuscript's order**, including the zero-maximum branch through the general scaled auxiliary bound. |
| 906--910 | Rational constant-`2` consequence and full finite spectral-set package | `holomorphicMatrixEval_rational`, `holomorphicCrouzeixRationalBound`, `finiteRationalSpectralSetCorollary`, `crouzeixRationalSpectralSetCorollary`, `crouzeixRationalBound` | **proved directly from the holomorphic theorem**. |
| 119--129 | Polynomial specialization | `holomorphicMatrixEval_polynomial`, `crouzeixConjecture` | **proved directly from the holomorphic theorem**. |

## Consequences, lines 912--1001

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 919--961 | Polynomial bound for a bounded operator on a nonzero complex Hilbert space | `operatorNumericalRange`, `operatorPolynomialEval`, `finiteDimensionalHilbertPolynomialCrouzeix`, `hilbertSpacePolynomialCrouzeix` | **proved** by finite-dimensional transport and the manuscript's finite Krylov compression, including exact power agreement and numerical-range containment. |
| 963--986 | Compact closed numerical range, spectrum inclusion, and rational spectral-set consequence | `closedOperatorNumericalRange`, `closedOperatorNumericalRange_isCompact`, `spectrum_subset_closedOperatorNumericalRange`, `operatorRationalEval`, `operatorRationalEval_eq_num_mul_inverse_denom`, `hilbertSpaceRationalCrouzeix`, `HilbertRationalSpectralSetStatement`, `hilbertSpaceRationalSpectralSet`, `ClosedOperatorNumericalRangeIsTwoSpectralSet`, `closedOperatorNumericalRange_isTwoSpectralSet` | **proved**. Lean supplies the required polynomial approximation by the explicit finite-denominator construction and identifies its limit with the manuscript's reduced numerator-times-inverse-denominator value. |
| 988--997 | Polynomial matrix-function error | `holomorphicMatrixEval_sub`, `holomorphicMatrixEval_polynomial`, `holomorphicCrouzeixPolynomialErrorBound` | **proved** by applying the main theorem to `f - p`. |
| 988--997 | Rational matrix-function error | `holomorphicMatrixEval_sub`, `holomorphicMatrixEval_rational`, `holomorphicCrouzeixRationalErrorBound` | **proved** by applying the main theorem on the intersection of the supplied holomorphy neighborhood with the rational pole complement. |

## Deleted superseded formalization

The older normalized affine `f_eta` perturbation, finite collision-set,
injective perturbed-sample, interpolation-based generated-algebra equality,
and `eta → 0` formalization has been deleted from the working tree. Those
modules and declarations are therefore absent from the current inventory and
dependency graph. Git history preserves the prior implementation.

## Active endpoint dependency chain

1. A simple auxiliary matrix `B` supplies a basis, and holomorphic evaluation
   puts `T=f(B)` in that basis with arbitrary repeated target entries.
2. Direct scalar and matrix Cauchy formulas supply the power identities used
   by the Cayley series.
3. The double-layer Cayley construction gives an `alg(Bᴴ)` positive-real
   completion of `T`.
4. Repeated-point Herglotz-kernel sampling and the auxiliary completion
   theorem give the normalized bound `‖f(B)‖ ≤ 2`.
5. For each fixed outer domain, simple-spectrum `Bₖ → A`; contour
   continuity passes the holomorphic estimate to `A`.
6. A tail of canonical outer domains stays inside the supplied open
   holomorphy neighborhood, and shrinking their exact maxima proves
   `holomorphicCrouzeixBound`.
7. Polynomial and rational compatibility give both scalar-calculus
   specializations directly; subtraction gives both matrix-function error
   estimates.
8. Krylov compression gives the Hilbert polynomial bound, and the proved
   finite-denominator approximation and spectrum inclusion give the complete
   Hilbert spectral-set package.

No collision-avoidance parameter, algebra equality
`alg(f_eta(B)) = alg(B)`, or `eta → 0` occurs in this chain.
No Runge theorem, Mergelyan theorem, or custom analytic axiom occurs in the
finite-matrix holomorphic chain.

# Scaled `q`-numerical-range formalization map

The second active source is
`../preprint/q_numerical_range_spectral_set.tex` (669 lines), verified at
SHA-256
`69862abf0f290975767dfd84dc998509da90c34982302927a19b45edcaa22771`.

## Definitions and elementary geometry, lines 107--209

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 115--120 | Euclidean vector norm and induced Euclidean matrix operator norm | `EuclideanVector`, `euclideanOperator`, `matrix_norm_eq_euclidean_operator_norm` | **defined/proved**; the matrix norm used by the formalization is exactly the norm displayed in the manuscript. |
| 133--147 | `q`-numerical range, scaled range, compactness, and nonemptiness | `qUnitPairs`, `scaledQNumericalRange`, `isCompact_scaledQNumericalRange`, `scaledQNumericalRange_nonempty` | **defined/proved** for finite complex Euclidean matrix spaces; `[Nontrivial n]` is the manuscript convention `n ≥ 2`. |
| 181--209 | Phase reduction and the parameters `tau`, `kappa` | `scaledQNumericalRange_eq_norm`, `qTau`, `qKappa`, `qKappa_parameter_identity`, `two_div_qKappa` | **proved** |
| 149--166, 561--632 | Exact rational main theorem, polynomial specialization, and optimal constant | `sharpRationalScaledQNumericalRangeBound`, `sharpPolynomialScaledQNumericalRangeBound`, `sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex` | **proved** with the same hypotheses and fixed-complex-parameter sharpness statement. |

## Tsing disks, nesting, and spectral containment, lines 211--289

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 211--289 | Exact Tsing disk formula and nesting | `qResidual`, `qDiskUnion`, `scaledQNumericalRange_eq_qDiskUnion`, `qTau_div_antitone`, `scaledQNumericalRange_antitone` | **proved by the manuscript's argument**: Cauchy--Schwarz for one inclusion, then a normalized eigenvector, connected unit sphere, intermediate value, and explicit boundary pair for the reverse inclusion. |
| 233--237, 506--509 | `W(A) ⊆ Omega_q(A)` and `spectrum(A) ⊆ Omega_q(A)` | `numericalRange_subset_scaledQNumericalRange`, `matrixSpectrum_subset_scaledQNumericalRange` | **proved** |

## Rank-one stretch geometry, lines 291--357

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 291--357 | Positive rank-one stretch, explicit inverse, sharp norm product, and numerical-range containment | `rankOneProjection`, `stretchSimilarity`, `stretchInverseCandidate`, `stretchSimilarity_posDef`, `stretchSimilarity_inv`, `norm_stretch_product_le_half_add_inv`, `numericalRange_stretchSimilarity_subset_scaledQNumericalRange`, `numericalRange_stretchSimilarity_subset_scaledQNumericalRange_complex` | **proved exactly** for the stretch family and one-sided containment used later. |

## Rank-one stretch extraction, lines 359--462

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 408--446 | Orthogonality parameter and amplification identities | `exists_extractionParameter`, `extraction_vectors_inner_eq_zero`, `extraction_vectors_amplify` | **proved** |
| 359--462 | Exact Möbius family and rank-one stretch extraction lemma | `rotatedRealMobiusEval`, `norm_le_max_one_div_of_uniform_stretch_mobius` | **proved** with the manuscript's hypotheses `κ ≥ 1`, `K ∈ ℝ`, closed-disk spectrum, unit `v` and `omega`, and `0 ≤ a < 1`. |

## Rational transfer theorem, lines 464--557

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 470--493 | Universal rational base constant and transferred constant | `UniversalRationalNumericalRangeBound`, `qTransferredConstant` | **defined** with the same pole-free rational hypotheses and `K ≥ 1`. |
| 495--548 | `M + epsilon` normalization, rational spectral mapping, exact Möbius composition, similarity covariance, extraction, and limit | `matrixSpectrum_rationalMatrixEval_subset_image`, `rationalMatrixEval_mobiusComposeRatFunc_of_disk`, `rationalMatrixEval_similarity_of_rationalPoleFreeOn`, `rationalMatrixEval_le_qTransferredConstant_mul_max_add` | **proved** |
| 470--548 | General transfer `K ↦ max{1,K/kappa}` | `rationalScaledQNumericalRangeBound_of_universal` | **proved** for the exact rational spectral-set formulation. |
| 550--557 | Constant-two conclusion and polynomial specialization | `universalRationalNumericalRangeBound_two`, `rationalScaledQNumericalRangeBound_two`, `polynomialScaledQNumericalRangeBound_two`, `sharpRationalScaledQNumericalRangeBound`, `sharpPolynomialScaledQNumericalRangeBound` | **proved**. `sharpScaledQNumericalRangeConstant_eq_qTransferredConstant` identifies the result with the displayed formula. |

## Sharpness, lines 559--632

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 559--632 | Jordan nilpotent, exact identity-function maximum, both lower branches, and complex-parameter optimality | `jordanNilpotentTwo`, `norm_jordanNilpotentTwo`, `norm_le_qKappa_half_of_mem_scaledQNumericalRange_jordanNilpotentTwo`, `qKappa_half_mem_scaledQNumericalRange_jordanNilpotentTwo`, `maxRationalModulusOnScaledQNumericalRange_X_jordanNilpotentTwo`, `one_le_of_polynomialScaledQBoundOnFinTwo`, `two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo`, `max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo`, `sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex` | **proved**. For every admissible complex `q`, the displayed constant is least even after restriction to `2 × 2` matrices. |

## Active scaled `q` endpoint chain

1. Phase reduction replaces a complex `q` by `‖q‖`; the parameter identities
   produce `kappa`.
2. Tsing's disk-union formula proves nesting, hence numerical-range and
   spectrum containment.
3. Every adapted rank-one positive stretch used by extraction has numerical
   range inside the scaled `q`-range.
4. Rational spectral mapping and exact rational Möbius composition turn the
   universal numerical-range estimate into uniform Schur estimates over
   those stretches.
5. The extraction lemma and the `epsilon → 0` argument yield the transferred
   rational constant.
6. The proved ordinary constant `2` gives the displayed sharp upper bound.
7. Constant functions and the two-dimensional Jordan nilpotent give both
   lower branches, hence the least-constant theorem.
