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

# Scaled `q`-numerical-range formalization map

The second active source is
`../preprint/q_numerical_range_spectral_set.tex` (660 lines), verified at
SHA-256
`5939c6f76c0d2ab0aea076ae89af7d3c709fc49ba175917560da31733f061620`.

## Definitions and elementary geometry, lines 107--202

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 127--140 | `q`-numerical range, scaled range, compactness, and nonemptiness | `qUnitPairs`, `scaledQNumericalRange`, `isCompact_scaledQNumericalRange`, `scaledQNumericalRange_nonempty` | **defined/proved** for finite complex Euclidean matrix spaces; `[Nontrivial n]` is the manuscript convention `n ≥ 2`. |
| 174--202 | Phase reduction and the parameters `tau`, `kappa` | `scaledQNumericalRange_eq_norm`, `qTau`, `qKappa`, `qKappa_parameter_identity`, `two_div_qKappa` | **proved** |
| 142--159, 552--623 | Exact rational main theorem, polynomial specialization, and optimal constant | `sharpRationalScaledQNumericalRangeBound`, `sharpPolynomialScaledQNumericalRangeBound`, `sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex` | **proved** with the same hypotheses and fixed-complex-parameter sharpness statement. |

## Tsing disks, nesting, and spectral containment, lines 204--281

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 204--281 | Exact Tsing disk formula and nesting | `qResidual`, `qDiskUnion`, `scaledQNumericalRange_eq_qDiskUnion`, `qTau_div_antitone`, `scaledQNumericalRange_antitone` | **proved by the manuscript's argument**: Cauchy--Schwarz for one inclusion, then a normalized eigenvector, connected unit sphere, intermediate value, and explicit boundary pair for the reverse inclusion. |
| 227--230, 497--500 | `W(A) ⊆ Omega_q(A)` and `spectrum(A) ⊆ Omega_q(A)` | `numericalRange_subset_scaledQNumericalRange`, `matrixSpectrum_subset_scaledQNumericalRange` | **proved** |

## Rank-one stretch geometry, lines 283--349

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 283--349 | Positive rank-one stretch, explicit inverse, sharp norm product, and numerical-range containment | `rankOneProjection`, `stretchSimilarity`, `stretchInverseCandidate`, `stretchSimilarity_posDef`, `stretchSimilarity_inv`, `norm_stretch_product_le_half_add_inv`, `numericalRange_stretchSimilarity_subset_scaledQNumericalRange`, `numericalRange_stretchSimilarity_subset_scaledQNumericalRange_complex` | **proved exactly** for the stretch family and one-sided containment used later. |

## Rank-one stretch extraction, lines 351--453

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 399--437 | Orthogonality parameter and amplification identities | `exists_extractionParameter`, `extraction_vectors_inner_eq_zero`, `extraction_vectors_amplify` | **proved** |
| 351--453 | Exact Möbius family and rank-one stretch extraction lemma | `rotatedRealMobiusEval`, `norm_le_max_one_div_of_uniform_stretch_mobius` | **proved** with the manuscript's hypotheses `κ ≥ 1`, `K ∈ ℝ`, closed-disk spectrum, unit `v` and `omega`, and `0 ≤ a < 1`. |

## Rational transfer theorem, lines 455--548

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 461--484 | Universal rational base constant and transferred constant | `UniversalRationalNumericalRangeBound`, `qTransferredConstant` | **defined** with the same pole-free rational hypotheses and `K ≥ 1`. |
| 486--539 | `M + epsilon` normalization, rational spectral mapping, exact Möbius composition, similarity covariance, extraction, and limit | `matrixSpectrum_rationalMatrixEval_subset_image`, `rationalMatrixEval_mobiusComposeRatFunc_of_disk`, `rationalMatrixEval_similarity_of_rationalPoleFreeOn`, `rationalMatrixEval_le_qTransferredConstant_mul_max_add` | **proved** |
| 461--539 | General transfer `K ↦ max{1,K/kappa}` | `rationalScaledQNumericalRangeBound_of_universal` | **proved** for the exact rational spectral-set formulation. |
| 541--548 | Constant-two conclusion and polynomial specialization | `universalRationalNumericalRangeBound_two`, `rationalScaledQNumericalRangeBound_two`, `polynomialScaledQNumericalRangeBound_two`, `sharpRationalScaledQNumericalRangeBound`, `sharpPolynomialScaledQNumericalRangeBound` | **proved**. `sharpScaledQNumericalRangeConstant_eq_qTransferredConstant` identifies the result with the displayed formula. |

## Sharpness, lines 550--623

| Source | Claim | Lean declaration(s) | Status / translation |
|---|---|---|---|
| 550--623 | Jordan nilpotent, exact identity-function maximum, both lower branches, and complex-parameter optimality | `jordanNilpotentTwo`, `norm_jordanNilpotentTwo`, `norm_le_qKappa_half_of_mem_scaledQNumericalRange_jordanNilpotentTwo`, `qKappa_half_mem_scaledQNumericalRange_jordanNilpotentTwo`, `maxRationalModulusOnScaledQNumericalRange_X_jordanNilpotentTwo`, `one_le_of_polynomialScaledQBoundOnFinTwo`, `two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo`, `max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo`, `sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex` | **proved**. For every admissible complex `q`, the displayed constant is least even after restriction to `2 × 2` matrices. |

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
