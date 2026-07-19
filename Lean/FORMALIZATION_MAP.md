# Formalization map

Source locations refer to the preserved baseline
`../LaTeX/crouzeix_conjecture_proof.tex` (453 lines), verified at
SHA-256 `037e9aafefe5fad57f0acee04b410093aa46f65c508156e80eda987ba1b1478f`.
They are not line references into the submission-formatted
`../AnnMath/the_numerical_range_is_a_2_spectral_set.tex`.

Statuses mean: **proved** is a checked proof term; **defined** is a faithful encoded object or
target proposition; **proved reduction** is a checked implication used as an intermediate theorem;
and **not separately formalized** records a source claim broader than the specialization actually
needed by the completed proof.  No declaration classified as a reduction assumes the desired norm
inequality, and the final polynomial and rational theorems are unconditional.

## The theorem and foundational conventions, lines 15--28

| Source | Claim / formula | Exact Lean declaration | Dependencies and translation | Status |
|---|---|---|---|---|
| 15--24, (18), (22) | Matrices, `W(A)`, polynomial evaluation, induced Euclidean operator norm, and constant `2` | `SquareMatrix`, `EuclideanVector`, `euclideanOperator`, `numericalRange`, `polynomialEval`, `PolynomialCrouzeixBound`, `MainTheoremStatement` | `[Fintype n] [DecidableEq n] [Nonempty n]`; `Nonempty n` makes the source's positive-dimension convention explicit. | **defined; exact target** |
| 18 | `x*Ax` and complex inner-product convention | `inner_euclideanOperator_eq_star_dotProduct` | Mathlib is conjugate-linear in the first variable. | **proved** |
| 18, 22 | Matrix/continuous-operator bridge and norm equality | `matrix_norm_eq_euclidean_operator_norm`, `euclideanOperator_polynomialEval` | Scoped norm is `Matrix.Norms.L2Operator`, not an entrywise norm. | **proved** |
| 18 | `W(A)` nonempty and compact | `numericalRange_nonempty`, `numericalRange_eq_image_sphere`, `isCompact_numericalRange` | Image of the Euclidean unit sphere; positive dimension is explicit. | **proved** |
| 20--22 | Displayed maximum is attained | `exists_maxPolynomialModulusOnNumericalRange`, `norm_polynomial_eval_le_maxOnNumericalRange` | `maxPolynomialModulusOnNumericalRange` is the `sSup` of exactly the displayed value set. | **proved** |
| 26 | `Re X=(X+X*)/2`, adjoint, positivity | `rePart`, `euclideanOperator_conjTranspose`, `IsPositiveMatrix` | `IsPositiveMatrix` is exactly `Matrix.PosSemidef`. | **defined/proved bridge** |
| 27 | `alg(T)` | `generatedAlgebra`, `generatedAlgebra_mem_iff_exists_polynomial`, `isClosed_generatedAlgebra` | Algebraic unital algebra; closed because the ambient matrix space is finite dimensional. | **proved** |

`crouzeixConjecture_mainTheorem` has the unconditional type `MainTheoremStatement`, and
`crouzeixConjecture A p` is its pointwise form with exactly the displayed matrix norm, numerical
range, polynomial evaluation, and constant `2`.

## Positive-real completion, lines 30--228

| Source | Claim / displayed formula | Exact Lean declaration(s) | Status / translation |
|---|---|---|---|
| 30--42, (36)--(39) | Positive-real completion lemma | `HasDistinctEigenvalues`, `IsPositiveRealCompletion`, `PositiveRealCompletionStatement`, `positiveRealCompletionStatement` | **proved in full** |
| 32--33 | Simple spectrum and spectral disk hypothesis | `HasDistinctEigenvalues`; `closedUnitDisk`; `simpleDiagonalization_of_hasDistinctEigenvalues`; `SimpleDiagonalization.eigenvalues_norm_le_one` | **proved**; diagonalization is derived, not assumed. |
| 45--58, (48), (55)--(56) | Matrix Herglotz kernel positivity | `matrixHerglotzKernel`, `IsPositiveMatrixKernelOn`, `finite_sampling_quadratic_nonneg`, `matrixHerglotzKernel_isPositiveMatrixKernelOn` | **proved without an axiom**. |
| 59--65, (64) | Positive matrix-valued Herglotz measure representation | The required consequence is proved directly in `MatrixHerglotz` by regularized circle averages, scalar Cauchy/mean-value identities, and a limit. | The measure representation itself is **not separately constructed**; it is a source proof sketch replaced by a complete proof of the exact kernel theorem. |
| 66--77, (68)--(75) | Scalar kernel identity/factorization | `scalar_herglotz_kernel_identity`, `scalar_herglotz_kernel_factorization`, `matrixHerglotzAtom_isPositiveMatrixKernelOn` | **proved** |
| 79--86, (81)--(85) | `T=S Lambda S^-1`, `G=S* S` | `SimpleDiagonalization`, `completionGramMatrix`, `SimpleDiagonalization.eq_completionDiagonalizableMatrix` | **proved/defined** |
| 87--98, (95) | Analytic diagonal correction and `K=G(I-zLambda)^-1+D(z)G` | `completionAnalyticDiagonalCorrection`, `completionAnalyticDiagonalCorrection_analyticOnNhd`, `completionAnalyticDiagonalCorrection_eq_diagonal`, `completionAnalyticDiagonalCorrection_zero`, `completionAnalyticDiagonalCorrection_mul_completionGramMatrix`, `exists_analytic_completionDiagonalCorrection`, `exists_completionKernelModel_of_isPositiveRealCompletion` | **proved**.  The explicit coordinate is `(Sᴴ X(z) S) G⁻¹`; generated-algebra membership proves it is diagonal, and multiplication by `G` reconstructs the pulled-back correction with the exact factor order `D(z)G`. |
| 99--100 | Congruence preserves positive real part/kernel | `completionPullbackFunction_rePart_posSemidef`, `matrixHerglotzKernel_positive_congr_on` | **proved**; this supplies the positive kernel used after the pointwise decomposition. |
| 102--110, (104)--(109) | `P`, `R`, `X` and nonzero denominators/Hermitian symmetry | `completionP`, `completionR`, `completionX`; denominator and `*_isHermitian` theorems in `CompletionAlgebra` | **proved** |
| 111--123, (114)--(121) | Sample points/vectors and `v=-G^-1Pu` | `completionSamplePoint`, `completionSampleVector`, `completionSubstitutionMatrix`, `completion_mulVec_add_eq_zero` | **proved**; repeated sample points are allowed. |
| 124--137, (128)--(134) | Complete cancellation of the unknown diagonal correction | `completionUnknownHalfContribution_eq_zero`, `completionUnknownContribution_eq_zero`, `completionCorrectionKernel_sampling_eq_zero` | **proved** |
| 139--148, (142)--(148) | Blocks `4R-2P`, `G+R`, `2G` | `completionResolventKernel_sample_sample_apply`, `completionResolventKernel_sample_zero_apply`, `completionResolventKernel_zero_sample_apply`, `completionResolventKernel_zero_zero_apply` | **proved** |
| 149--161, (150)--(160) | Sampled quadratic form and `4X-XG^-1P-PG^-1X >= 0` | `completionKernelModel_kernel_eq_add`, `completionSampleCoefficient_quadratic_nonneg_of_positiveKernel`, `completion_X_inequality_of_positiveKernel` | **proved**, exact noncommutative order. |
| 163--170, (165)--(169) | Positive square root, inverse square root, normalized `C,P,R,X` | `completionPositiveSquareRoot`, `completionPositiveInvSquareRoot`, `CompletionSquareRootData`, `completionSimilarity` | **proved/defined** via continuous functional calculus. |
| 172--179, (175)--(178) | Two Gramian series | `gramianTerm`, `gramian`, `summable_gramianTerm`, `completionP_congruence_eq_gramian_four`, `completionR_congruence_eq_gramian_two` | **proved with norm convergence** |
| 180--192, (182)--(190) | Positive difference series, powers of `C`, uniform bound | `gramianDifferenceTerm`, `gramian_two_sub_gramian_four_eq_tsum`, `completionSimilarity_pow`, `completionSimilarity_pow_norm_le` | **proved**; no false `norm C <= 1` assumption. |
| 192--198, (195)--(197) | Congruenced anticommutator inequality | `completion_PRX_congruence_eq_gramian_expression`, `completion_gramian_expression_posSemidef_of_source` | **proved** |
| 200--212, (203), (210) | Eigenvector contradiction and `I <= P <= 2I` | `gramian_four_eigenvalues_le_two`, `gramian_four_upper_bound_posSemidef`, positivity lemmas in `CompletionSeries` | **proved** |
| 213--221, (215), (219)--(220) | Stein identity and `C*C <= 4I` | `gramian_stein_identity`, `four_sub_conjTranspose_mul_self_posSemidef_of_gramian_inequality`, `norm_le_two_of_gramian_inequality` | **proved** |
| 222--227, (225) | Polar decomposition/unitary equivalence and final norm | `completionPolarUnitary_mem_unitaryGroup`, `completionDiagonalizableMatrix_eq_unitary_conjugate`, `norm_unitary_conjugation`, `norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel` | **proved** |

## Double-layer construction, lines 230--353

| Source | Claim / displayed formula | Exact Lean declaration(s) | Status / translation |
|---|---|---|---|
| 232--242 | Completion provider from a convex boundary | `HasDoubleLayerCompletionProvider`; `hasDoubleLayerCompletionProvider_of_boundary_data`; `hasDoubleLayerCompletionProvider_of_parametricBoundary`; `PositivePeriodicRadialData.OrientedRadialConvexBoundary.hasDoubleLayerCompletionProvider_of_simpleDiagonalization` | The polynomial specialization used in the theorem is **proved** from the explicit radial matrix Cauchy theorem and the supported boundary package.  The source lemma stated for an arbitrary analytic `f` is broader and is **not separately formalized**; every `f` used at lines 377--421 is a polynomial, so no source hypothesis is strengthened. |
| 245--252, (247), (251) | `spectrum(B) subset W(B)` and polynomial spectral mapping | `matrixSpectrum_subset_numericalRange`, `matrixSpectrum_polynomialEval_subset_closedUnitDisk` | **proved** |
| 254--265, (257), (261)--(264) | `C¹` counterclockwise boundary, outward normal, arclength, resolvent density | `OutwardBoundarySupport`, `ParametricConvexBoundary`, `parametricBoundaryResolvent`, `parametricBoundaryFirstPart`, `parametricDoubleLayerDensity`; `orientedRadialConvexBoundary_thickening` | The supported compact parameter/arclength-Jacobian model is **defined**; resolvent/density continuity, integrability, and pointwise positivity are **proved**.  The complete positively oriented `C¹` package is **constructed** for every positive parallel body used below. |
| 266--276, (268)--(276) | Support matrix and density positivity by congruence | `doubleLayerSupportMatrix_eq_two_smul_rePart`, `doubleLayerSupportMatrix_posSemidef_of_outwardBoundarySupport`, `doubleLayerResolvent_congruence_density`, `normalizedDoubleLayerResolvent_density_posSemidef` | **proved** |
| 278--289, (281)--(288) | `d sigma=i nu ds`, scalar/matrix Cauchy resolvent integral, total mass `2I` | `parametricBoundaryFirstPart_eq_cauchyIntegrand`, `integral_polynomial_cauchy`, `integral_polynomial_cauchy_resolvent_of_simpleDiagonalization`, `hasParametricPolynomialCauchyFormula_of_simpleDiagonalization`, `parametricPositiveBoundaryDensity`, `doubleLayerIntegral_mass_eq_two_one` | The orientation identity, scalar Cauchy theorem, diagonalized matrix resolvent theorem, exact parametric Cauchy proposition, and its constant-mass consequence are all **proved**. |
| 290--296, (292)--(293) | `Phi` is bounded, complex-linear, unital, positive, and star preserving | `boundaryPhi`, `boundaryPhiCLM`, `boundaryPhi_norm_le`, `boundaryPhi_one`, `boundaryPhi_star`, `boundaryPhi_posSemidef` | **proved** from `PositiveBoundaryDensity`, including PSD Bochner integration (`integral_posSemidef_of_ae`). |
| 298--310, (300)--(308) | Companion transform and `2 Phi(h)=h(B)+g_h(B)*` | `parametricPolynomialCompanion`, `two_smul_boundaryPhi_parametricPolynomial_eq`, `parametricPolynomialCompanion_mem_generatedAlgebra`, `generatedAlgebra_integral_mem` | For every polynomial `h` needed later, the companion is **constructed**, the identity is **proved**, and its Bochner integral is **proved** to remain in `alg(B)`.  The broader arbitrary-analytic-function formulation is **not separately formalized** and is not used. |
| 312--324, (314), (318), (323) | Cayley boundary function, analytic `H`, `H(0)=I`, `Re H>=0` | `cayleyBoundaryFunction`, `doubleLayerCayleyValue`, `doubleLayerCayleySeries`, `doubleLayerCayleySeries_eq_value`, `doubleLayerCayleySeries_analyticOnNhd`, `doubleLayerCayleySeries_zero`, `doubleLayerCayleySeries_rePart_posSemidef` | **proved for the same constructed function**. |
| 325--336, (327), (333)--(335) | Uniform boundary geometric series and norm-convergent matrix expansion | `cayleyBoundarySeriesTerm_hasSum`, `doubleLayerCayleySeries_hasSum`, generic `matrixPowerSeries_hasSum` | **proved in boundary sup norm and matrix norm** |
| 337--352, (339)--(341) | Resolvent subtraction, companion series, and closed-algebra membership | `hasSum_resolventSeriesTerm_of_spectrum_subset_closedUnitDisk`, `companionTailTerm_hasSum_completion_sub_resolvent`, `completion_sub_resolvent_mem_generatedAlgebra_conjTranspose`, `parametricDoubleLayerCayleySeriesCoefficient_succ`, `doubleLayerCayleySeries_isPositiveRealCompletion` | **proved** from the explicit polynomial Cauchy formula; companion-integral algebra membership is no longer an input at this layer. |

## Explicit `C¹` parallel-body boundary, lines 254--289 and 355--435

| Source | Logically necessary geometric/analytic claim | Exact Lean declaration(s) | Dependencies and translation | Status |
|---|---|---|---|---|
| 254--276, 355--360, 426--435 | Metric projection onto a nonempty compact convex core, projection variational inequality, continuity, and the exact distance level describing a positive parallel-body frontier | `convexProjection`, `convexProjection_mem`, `convexProjection_variational`, `convexProjection_firm_nonexpansive`, `convexProjection_lipschitzWith_one`, `continuous_convexProjection`, `frontier_thickening_eq_infDist_level` | The construction is over the real Hilbert structure on `ℂ`; compactness supplies existence and convexity supplies uniqueness/firm nonexpansiveness. | **proved** |
| 254--278, 355--360 | Squared distance to the convex core is `C¹`, with derivative `h ↦ 2⟪z-P_Kz,h⟫_ℝ` | `convexSquaredDistance`, `convexSquaredDistance_remainder_bounds`, `hasFDerivAt_convexSquaredDistance`, `fderiv_convexSquaredDistance`, `contDiff_one_convexSquaredDistance`, `hasStrictFDerivAt_convexSquaredDistance` | The derivative is proved from two-sided quadratic remainder bounds, not by assuming differentiability of the projection. | **proved** |
| 254--278, 355--360 | Global positive periodic radial parametrization of a parallel body by inverse Minkowski gauge; the radial point is on the frontier and has squared distance `r²` | `translatedParallelDomain`, `parallelRadialDirection`, `parallelGaugeRadius`, `parallelRadialPoint`, `gauge_parallelRadialDirection_pos`, `parallelGaugeRadius_pos`, `continuous_parallelGaugeRadius`, `periodic_parallelGaugeRadius`, `parallelRadialPoint_mem_frontier_thickening`, `convexSquaredDistance_parallelRadialPoint` | Uses Mathlib's gauge theorems for the translated open convex neighborhood of `0`; boundedness of the compact core's thickening makes the gauge strictly positive. | **proved** |
| 254--278, 355--360 | The global inverse-gauge radius is continuously differentiable | `contDiff_one_of_continuous_implicit_scalar`, `parallelRadialDistanceEquation`, `parallelRadialDistanceEquation_root`, `fderiv_parallelRadialDistanceEquation_radial_pos`, `contDiff_one_parallelGaugeRadius` | A scalar `C¹` implicit-function theorem is globalized using the already-constructed continuous root.  The radial partial derivative is strictly positive by the projection variational inequality, so no regularity is assumed circularly. | **proved** |
| 254--276 | Continuous unit outward normal and supporting-line inequality on the parallel-body frontier | `parallelBoundaryNormal`, `continuous_parallelBoundaryNormal`, `norm_sub_convexProjection_eq_of_mem_frontier_thickening`, `real_inner_projectionResidual_sub_pos`, `outwardBoundarySupport_thickening` | The normal is the normalized metric-projection residual.  Its norm and support property are derived at the exact frontier distance level. | **proved** |
| 254--289 | Positive orientation and arclength identity `gamma'=i*nu*speed` | `parallelPositivePeriodicRadialData_normal_tangent_orthogonal`, `parallelPositivePeriodicRadialData_normal_direction_pos`, `radialTangent_eq_I_mul_normal_mul_norm`, `orientedRadialConvexBoundary_thickening` | Differentiating the constant squared-distance equation gives orthogonality; positivity of the outward radial component selects the counterclockwise sign; `speed=‖gamma'‖`. | **proved** |
| 234--242, 355--360, 426--435 | Existence of the exact oriented radial `C¹` package for every positive thickening, and hence for every canonical numerical-range outer domain | `PositivePeriodicRadialData`, `RadialConvexDomain`, `parallelPositivePeriodicRadialData`, `orientedRadialConvexBoundary_thickening`, `exists_orientedRadialConvexBoundary_thickening`, `canonicalParallelOrientedRadialBoundaryStatement` | The manuscript asks for smooth outer domains, while its double-layer lemma uses only continuously differentiable boundary.  The formal proof constructs that exact `C¹` boundary for the canonical positive parallel bodies; no unused `C∞` strengthening is assumed. | **proved** |
| 278--289 | Winding number one and polynomial Cauchy formula on the explicit radial contour | `sub_div_sub_mem_slitPlane_of_not_mem_segment`, `RadialConvexDomain.log_comparisonRatio_hasDerivAt`, `integral_tangent_div_point_sub_center`, `integral_tangent_div_point_sub`, `integral_polynomial_cauchy`, `doubleLayerResolvent_eq_innerConjugation_diagonal`, `polynomialResolventIntegrand_eq_innerConjugation_diagonal`, `integral_polynomial_cauchy_resolvent_of_simpleDiagonalization` | Winding constancy uses the principal logarithm after proving the comparison quotient avoids its slit; the matrix result is obtained entrywise from an explicit simple diagonalization and the proved resolvent conjugation formula. | **proved** |

## Perturbation and limiting argument, lines 355--438

| Source | Claim / displayed formula | Exact Lean declaration(s) | Status |
|---|---|---|---|
| 355--360 | Compactness and convexity of `W(A)`; regular convex outer domain | `isCompact_numericalRange`; `numericalRange_convex`; `parallelOuterDomain_data`; `canonicalParallelOrientedRadialBoundaryStatement` | Compactness, Toeplitz--Hausdorff convexity, canonical convex outer domains, and their complete oriented `C¹` boundary structures are **proved**.  `C¹` is exactly the hypothesis of lines 234--236; the stronger unused adjective “smooth” is not assumed. |
| 361--365, (363) | Fixed outer-set estimate | `norm_polynomialEval_le_two_mul_of_simpleSpectrum`; `polynomialCrouzeixBound_of_simple_outer_approximants` | **proved** from the double-layer provider and outer approximants; the canonical provider is discharged by the radial-boundary theorem. |
| 367--375, (370) | Density of simple-spectrum matrices, numerical-range perturbation, continuity | `exists_hasDistinctEigenvalues_norm_sub_lt`; `simpleSpectrumApproximation`; `numericalRange_perturbation`; `tendsto_polynomialEval` | **proved and integrated**. |
| 377--386, (380), (385) | `M`, `R`, and zero-maximum branch | `exists_maxPolynomialModulusOnSet`, `maxPolynomialModulusOnSet_nonneg`, `polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero` | **proved**; no empty-set argument. |
| 387--391, (389) | Normalized affine perturbation and unit bound | `normalizedLinearPerturbation`, `manuscriptPerturbationPolynomial`, `norm_normalizedLinearPerturbation_le_one` | **proved** |
| 392--399, (395)--(396) | Finite exceptional parameters and an admissible sequence tending to zero | `collisionParameters_finite`, `exists_small_injective_perturbation`, `admissiblePerturbation`, `tendsto_admissiblePerturbation_zero` | **proved** |
| 400--409, (401), (408) | Simple spectrum of `f_eta(B)` and `alg(f_eta(B))=alg(B)` | `hasDistinctEigenvalues_manuscriptPerturbation`, `generatedAlgebra_manuscriptPerturbation_eq_of_hasDistinctEigenvalues` | **proved** by interpolation. |
| 411--424, (417), (421) | Apply completion and pass `eta->0`, then `B->A` | `norm_polynomialEval_le_two_mul_of_simpleSpectrum`, limiting theorems in `Limiting`, `polynomialCrouzeixBound_of_simple_outer_approximants` | **proved** |
| 426--435, (431)--(433) | Convex outer approximations and convergence of maxima | `parallelOuterDomain`, `parallelOuterDomain_data`, `tendsto_hausdorffDist_parallelOuterDomain_closure`, `tendsto_maxPolynomialModulusOnSet_of_outerApproximation`; `exists_orientedRadialConvexBoundary_thickening` | **proved** for the canonical positive parallel bodies, including the `C¹` boundary model consumed by the contour theorem. |
| 436--438, (437) | Main inequality | `MainTheoremStatement`; `canonicalParallelDoubleLayerStatement_of_orientedRadialBoundaries`; `mainTheoremStatement_of_canonicalParallelOrientedRadialBoundaries`; `crouzeixConjecture_mainTheorem`; `crouzeixConjecture` | The exact constant-`2` inequality is **proved unconditionally** for every finite nonempty index type, matrix, and complex polynomial. |

## Rational spectral-set corollary, lines 439--450

| Source | Claim | Exact Lean declaration(s) | Status |
|---|---|---|---|
| 439--444 | Compact `W(A)`, spectrum inclusion, exact poles and pole-free rational evaluation | `rationalPoleSet`, `rationalPoleSet_finite`, `RationalPoleFreeOn`, `rationalScalarEval`, `rationalMatrixEval`, `polynomialEval_denom_isUnit_of_rationalPoleFreeOn_numericalRange` | **proved/defined**, using the canonical reduced denominator. |
| 445--448 | Uniform polynomial approximation and matrix/max convergence | `exists_polynomial_tendstoUniformlyOn_rationalScalarEval`, `tendsto_rationalMatrixEval_of_tendstoUniformlyOn_numericalRange`, `tendsto_maxPolynomialModulusOnNumericalRange_of_tendstoUniformlyOn_rationalScalarEval` | **proved** by convex separation, explicit geometric polynomials, and denominator factorization; no Runge axiom. |
| 448--450 | Rational constant-2 bound and separate spectral-set corollary | `RationalCrouzeixBound`, `RationalSpectralSetCorollaryStatement`, `rationalCrouzeixBound_of_mainTheorem_of_convex_numericalRange`, `rationalSpectralSetCorollary_of_mainTheorem`, `crouzeixRationalSpectralSetCorollary`, `crouzeixRationalBound` | The transfer theorem is **proved**, numerical-range convexity is discharged internally, and the separate rational corollary and its pointwise form are **proved unconditionally** from `crouzeixConjecture_mainTheorem`. |

## Completed dependency chain

The final polynomial theorem and rational corollary have no remaining logical source obligation.
The unused broader arbitrary-analytic double-layer formulation and Herglotz measure representation
are disclosed in their rows above; neither is assumed by an endpoint.  The principal dependency
chain is:

1. metric projection and the `C¹` squared-distance theorem give a scalar implicit equation with
   positive radial derivative;
2. inverse gauge plus the scalar implicit-function theorem gives a positive periodic `C¹` radius,
   while the projection residual gives the continuous outward supporting unit normal;
3. tangent orthogonality and the positive radial component establish the counterclockwise identity
   `gamma'=i*nu*speed`, producing `orientedRadialConvexBoundary_thickening`;
4. the principal-log winding argument proves the scalar polynomial Cauchy formula, and explicit
   simple diagonalization lifts it to `HasParametricPolynomialCauchyFormula` for matrices;
5. double-layer positivity, companion integration, the Cayley series, and the positive-real
   completion theorem give the fixed-domain estimate;
6. simple-spectrum perturbation and canonical parallel-body limits yield
   `crouzeixConjecture_mainTheorem`, whose pointwise alias is `crouzeixConjecture`;
7. explicit polynomial approximation of pole-free rational functions yields the separate
   unconditional `crouzeixRationalSpectralSetCorollary` and `crouzeixRationalBound`.

Every intermediate hypothesis in this chain is discharged by a checked declaration.  No empty or
inconsistent premise, equivalent restatement of the target estimate, strengthened source
hypothesis, or unrelated norm is used.
