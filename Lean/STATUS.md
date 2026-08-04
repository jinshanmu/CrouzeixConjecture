# Formalization status

- Active manuscript: all 1,066 lines of
  `../preprint/the_numerical_range_is_a_2_spectral_set_v3.tex` were reviewed;
  SHA-256
  `f190178bc197c5f62fa8146f96c932a241379e90bf63145d542035058b92d154`.
- Toolchain: Lean 4.28.0 with Mathlib commit
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; dependencies and build
  products are local under `.lake/`.
- Faithful target: proved. `crouzeixConjecture` states the manuscript's
  matrices, polynomials, numerical range, induced Euclidean operator norm, and
  exact constant `2`. `[Nonempty n]` records the necessary
  positive-dimension convention.
- Euclidean matrix/operator model: proved, including the complex inner-product
  convention, adjoint and norm bridges, polynomial evaluation, spectrum,
  numerical range, generated algebra, and Toeplitz--Hausdorff convexity.
- Auxiliary-basis completion: proved. `PositiveRealCompletionStatement`
  accepts a simple diagonalization of `B`, an arbitrary target diagonal
  `lambda` in that same basis, and a completion whose defect lies in
  `alg(Bᴴ)`. Neither `lambda` nor the target matrix needs simple spectrum.
- Shared-basis functional calculus: proved by
  `SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal`.
  Thus `T = f(B)` has the required common basis even when the values
  `f(βᵢ)` repeat.
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
- Fixed simple-spectrum estimate: proved by
  `norm_polynomialEval_le_two_mul_of_simpleSpectrum`. It handles `M = 0`
  directly and otherwise normalizes only by `f = p / M`.
- Final limit: proved in v3 order. For each fixed outer body, simple-spectrum
  `Bₖ → A` gives the fixed-domain estimate; only then do the canonical
  parallel bodies shrink to `W(A)`.
- Superseded route removed: the `f_eta`, collision-avoidance,
  interpolation-based algebra-equality, and `eta → 0` formalization has been
  deleted from the working tree. Git history preserves the prior version.
- Notation: Lean `completionR` and `completionX` correspond to manuscript
  `Q` and `Y`; `completionP` corresponds to `P`.
- Rational result: proved separately as
  `crouzeixRationalSpectralSetCorollary`, with pointwise theorem
  `crouzeixRationalBound` and no Runge axiom.
- Scaled `q` source: all 660 lines of
  `../preprint/q_numerical_range_spectral_set.tex` were reviewed; SHA-256
  `5939c6f76c0d2ab0aea076ae89af7d3c709fc49ba175917560da31733f061620`.
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
- Authoritative verification: run plain `lake build`, followed serially by
  plain `lake run`; the latter checks `AxiomAudit.lean`.
