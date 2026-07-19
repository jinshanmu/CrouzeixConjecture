module

public import CrouzeixConjecture.CompletionSampling

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal analytic correction `D(z)` in manuscript equation (3). -/
def completionDiagonalCorrection (d : ℂ → n → ℂ) (z : ℂ) : SquareMatrix n :=
  Matrix.diagonal (d z)

/-- The conjugated positive-real function from manuscript equation (3):
`K(z) = G (I - z Λ)⁻¹ + D(z)G`. -/
def completionKernelModel (G : SquareMatrix n) (lambda : n → ℂ)
    (d : ℂ → n → ℂ) (z : ℂ) : SquareMatrix n :=
  G * Matrix.diagonal (fun j ↦ (1 - z * lambda j)⁻¹) +
    completionDiagonalCorrection d z * G

/-- Entrywise form of the model, retaining both the known resolvent and the unknown diagonal
analytic correction. -/
theorem completionKernelModel_apply (G : SquareMatrix n) (lambda : n → ℂ)
    (d : ℂ → n → ℂ) (z : ℂ) (i j : n) :
    completionKernelModel G lambda d z i j =
      G i j * (1 - z * lambda j)⁻¹ + d z i * G i j := by
  simp [completionKernelModel, completionDiagonalCorrection, Matrix.mul_apply,
    Matrix.diagonal]

/-- The condition `D(0)=0` makes the transformed function take the value `G` at the origin. -/
theorem completionKernelModel_zero (G : SquareMatrix n) (lambda : n → ℂ)
    (d : ℂ → n → ℂ) (hd0 : d 0 = 0) :
    completionKernelModel G lambda d 0 = G := by
  ext i j
  simp [completionKernelModel_apply, hd0]

/-- The manuscript's distinguished sampling point `0` and one point
`conj(λᵢ)/2` for each eigenvalue. -/
def completionSamplePoint (lambda : n → ℂ) : Option n → ℂ
  | none => 0
  | some i => conj (lambda i) / 2

omit [Fintype n] [DecidableEq n] in
/-- All manuscript sampling points lie in the open unit disk when the eigenvalues lie in the
closed unit disk. -/
lemma completionSamplePoint_mem_openUnitDisk (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (a : Option n) :
    completionSamplePoint lambda a ∈ openUnitDisk := by
  cases a with
  | none => simp [completionSamplePoint, openUnitDisk]
  | some i =>
      have hhalf : ‖conj (lambda i) / (2 : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_conj]
        norm_num
        linarith [hlambda i]
      simpa [completionSamplePoint, openUnitDisk, Metric.mem_ball, dist_eq_norm] using hhalf

/-- The sparse vector `uᵢeᵢ` in manuscript line 116. -/
def completionSparseVector (u : n → ℂ) (i : n) : n → ℂ :=
  fun j ↦ if j = i then u i else 0

omit [Fintype n] in
@[simp]
lemma completionSparseVector_apply_same (u : n → ℂ) (i : n) :
    completionSparseVector u i i = u i := by
  simp [completionSparseVector]

omit [Fintype n] in
@[simp]
lemma completionSparseVector_apply_ne (u : n → ℂ) {i j : n} (hji : j ≠ i) :
    completionSparseVector u i j = 0 := by
  simp [completionSparseVector, hji]

/-- Multiplication by a sparse vector selects one matrix column. -/
theorem mulVec_completionSparseVector (A : SquareMatrix n) (u : n → ℂ) (i j : n) :
    (A *ᵥ completionSparseVector u i) j = A j i * u i := by
  simp [Matrix.mulVec, dotProduct, completionSparseVector, mul_ite]

/-- Pairing a sparse vector against a vector selects one coordinate. -/
theorem star_completionSparseVector_dotProduct (u : n → ℂ) (i : n) (x : n → ℂ) :
    star (completionSparseVector u i) ⬝ᵥ x = conj (u i) * x i := by
  change (∑ j, conj (completionSparseVector u i j) * x j) = conj (u i) * x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [completionSparseVector, hji]
  · simp

/-- The point/vector family used in manuscript lines 111--123. -/
def completionSampleVector (G : SquareMatrix n) (lambda : n → ℂ)
    (u : n → ℂ) : Option n → n → ℂ
  | none => completionV G (completionP G lambda) u
  | some i => completionSparseVector u i

/-- The unknown diagonal term is multiplied by the exact cancellation vector
`Gv + Pu`; this is the algebraic content of manuscript lines 124--137. -/
def completionUnknownHalfContribution (G : SquareMatrix n) (lambda : n → ℂ)
    (d : ℂ → n → ℂ) (u : n → ℂ) : ℂ :=
  ∑ i, conj (u i) * d (conj (lambda i) / 2) i *
    (G *ᵥ completionV G (completionP G lambda) u +
      completionP G lambda *ᵥ u) i

/-- The choice `v = -G⁻¹Pu` annihilates the complete unknown half-contribution. -/
theorem completionUnknownHalfContribution_eq_zero (G : SquareMatrix n)
    (lambda : n → ℂ) (d : ℂ → n → ℂ) (u : n → ℂ) (hG : IsUnit G) :
    completionUnknownHalfContribution G lambda d u = 0 := by
  rw [completionUnknownHalfContribution,
    completion_mulVec_add_eq_zero G (completionP G lambda) u hG]
  simp

/-- Consequently the contribution together with its adjoint is zero, matching the
`2 RePart` expression displayed in manuscript lines 128--136. -/
theorem completionUnknownContribution_eq_zero (G : SquareMatrix n)
    (lambda : n → ℂ) (d : ℂ → n → ℂ) (u : n → ℂ) (hG : IsUnit G) :
    completionUnknownHalfContribution G lambda d u +
      conj (completionUnknownHalfContribution G lambda d u) = 0 := by
  rw [completionUnknownHalfContribution_eq_zero G lambda d u hG]
  simp

/-- The known resolvent part `G(I-zΛ)⁻¹` of the transformed function. -/
def completionResolventModel (G : SquareMatrix n) (lambda : n → ℂ)
    (z : ℂ) : SquareMatrix n :=
  G * Matrix.diagonal (fun j ↦ (1 - z * lambda j)⁻¹)

theorem completionResolventModel_apply (G : SquareMatrix n) (lambda : n → ℂ)
    (z : ℂ) (i j : n) :
    completionResolventModel G lambda z i j = G i j * (1 - z * lambda j)⁻¹ := by
  simp [completionResolventModel, Matrix.mul_apply, Matrix.diagonal]

/-- At two nonzero manuscript sampling points, the known kernel block is exactly
`4R - 2P` (manuscript lines 139--146). -/
theorem completionResolventKernel_sample_sample_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (i j : n) :
    matrixHerglotzKernel (completionResolventModel G lambda)
        (conj (lambda i) / 2) (conj (lambda j) / 2) i j =
      ((4 : ℂ) • completionR G lambda - (2 : ℂ) • completionP G lambda) i j := by
  rw [completion_fourR_sub_twoP_apply G lambda hlambda i j]
  have h₂ := completionR_denominator_ne_zero lambda hlambda i j
  have h₄ := completionP_denominator_ne_zero lambda hlambda i j
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  have hfirst :
      1 - conj (lambda i) / 2 * lambda j =
        1 - conj (lambda i) * lambda j / 2 := by
    ring
  have houter :
      1 - conj (lambda i) / 2 * conj (conj (lambda j) / 2) =
        1 - conj (lambda i) * lambda j / 4 := by
    simp only [map_div₀, starRingEnd_self_apply, map_ofNat]
    ring
  have hstar :
      star (G j i * (1 - conj (lambda j) / 2 * lambda i)⁻¹) =
        G i j * (1 - conj (lambda i) * lambda j / 2)⁻¹ := by
    change conj (G j i * (1 - conj (lambda j) / 2 * lambda i)⁻¹) = _
    simp only [map_mul, map_inv₀, map_sub, map_one, map_div₀, map_ofNat,
      starRingEnd_self_apply, hGentry]
    congr 2
    ring
  simp only [matrixHerglotzKernel, completionResolventModel_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  rw [hfirst, houter, hstar]
  change (1 - conj (lambda i) * lambda j / 4)⁻¹ *
      (G i j * (1 - conj (lambda i) * lambda j / 2)⁻¹ +
        G i j * (1 - conj (lambda i) * lambda j / 2)⁻¹) =
    2 * G i j /
      ((1 - conj (lambda i) * lambda j / 2) *
        (1 - conj (lambda i) * lambda j / 4))
  field_simp [h₂, h₄]
  ring

/-- Between a nonzero sampling point and the origin, the known block is `G+R`
(manuscript line 147). -/
theorem completionResolventKernel_sample_zero_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (i j : n) :
    matrixHerglotzKernel (completionResolventModel G lambda)
        (conj (lambda i) / 2) 0 i j =
      (G + completionR G lambda) i j := by
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  have hfirst :
      1 - conj (lambda i) / 2 * lambda j =
        1 - conj (lambda i) * lambda j / 2 := by
    ring
  have hstar : star (G j i * (1 - 0 * lambda i)⁻¹) = G i j := by
    change conj (G j i * (1 - 0 * lambda i)⁻¹) = G i j
    simp [hGentry]
  simp only [matrixHerglotzKernel, completionResolventModel_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  rw [hfirst, hstar]
  simp only [map_zero, mul_zero, sub_zero, inv_one, one_smul, completionR]
  rw [div_eq_mul_inv]
  ring

/-- The reverse origin/sample block is also `G+R`, using Hermiticity. -/
theorem completionResolventKernel_zero_sample_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (i j : n) :
    matrixHerglotzKernel (completionResolventModel G lambda)
        0 (conj (lambda j) / 2) i j =
      (G + completionR G lambda) i j := by
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  have hstar :
      star (G j i * (1 - conj (lambda j) / 2 * lambda i)⁻¹) =
        G i j * (1 - conj (lambda i) * lambda j / 2)⁻¹ := by
    change conj (G j i * (1 - conj (lambda j) / 2 * lambda i)⁻¹) = _
    simp only [map_mul, map_inv₀, map_sub, map_one, map_div₀, map_ofNat,
      starRingEnd_self_apply, hGentry]
    congr 2
    ring
  simp only [matrixHerglotzKernel, completionResolventModel_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  rw [hstar]
  simp only [zero_mul, sub_zero, inv_one, one_smul, mul_one, completionR]
  rw [div_eq_mul_inv]
  ring

/-- At the origin, the known kernel block is `2G`. -/
theorem completionResolventKernel_zero_zero_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (i j : n) :
    matrixHerglotzKernel (completionResolventModel G lambda) 0 0 i j =
      ((2 : ℂ) • G) i j := by
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  have hstar : star (G j i * (1 - 0 * lambda i)⁻¹) = G i j := by
    change conj (G j i * (1 - 0 * lambda i)⁻¹) = G i j
    simp [hGentry]
  simp only [matrixHerglotzKernel, completionResolventModel_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  rw [hstar]
  simp
  ring

/-- Summing the sparse row pairings reconstructs the usual matrix quadratic form. -/
theorem sum_sparse_sparse_quadratic (A : SquareMatrix n) (u : n → ℂ) :
    (∑ i, ∑ j,
      star (completionSparseVector u i) ⬝ᵥ
        (A *ᵥ completionSparseVector u j)) =
      star u ⬝ᵥ (A *ᵥ u) := by
  simp_rw [star_completionSparseVector_dotProduct,
    mulVec_completionSparseVector]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    Complex.star_def]

/-- Summing sparse vectors in the first slot reconstructs the first vector of a pairing. -/
theorem sum_sparse_left_pairing (A : SquareMatrix n) (u x : n → ℂ) :
    (∑ i, star (completionSparseVector u i) ⬝ᵥ (A *ᵥ x)) =
      star u ⬝ᵥ (A *ᵥ x) := by
  simp_rw [star_completionSparseVector_dotProduct]
  rfl

/-- Summing sparse vectors in the second slot reconstructs the second vector of a pairing. -/
theorem sum_sparse_right_pairing (A : SquareMatrix n) (u x : n → ℂ) :
    (∑ j, star x ⬝ᵥ (A *ᵥ completionSparseVector u j)) =
      star x ⬝ᵥ (A *ᵥ u) := by
  have hsum : (∑ j, A *ᵥ completionSparseVector u j) = A *ᵥ u := by
    ext i
    simp only [Finset.sum_apply, mulVec_completionSparseVector]
    rfl
  calc
    (∑ j, star x ⬝ᵥ (A *ᵥ completionSparseVector u j)) =
        star x ⬝ᵥ (∑ j, A *ᵥ completionSparseVector u j) := by
      simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = star x ⬝ᵥ (A *ᵥ u) := by rw [hsum]

/-- The selected sample/sample scalar pairing uses precisely the `4R-2P` block. -/
theorem completionResolventKernel_selected_sample_sample {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (u : n → ℂ) (i j : n) :
    star (completionSparseVector u i) ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda)
          (conj (lambda i) / 2) (conj (lambda j) / 2) *ᵥ
            completionSparseVector u j) =
      star (completionSparseVector u i) ⬝ᵥ
        (((4 : ℂ) • completionR G lambda - (2 : ℂ) • completionP G lambda) *ᵥ
          completionSparseVector u j) := by
  simp only [star_completionSparseVector_dotProduct, mulVec_completionSparseVector]
  rw [completionResolventKernel_sample_sample_apply hG lambda hlambda i j]

/-- The selected sample/origin pairing uses precisely the `G+R` block. -/
theorem completionResolventKernel_selected_sample_zero {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (u x : n → ℂ) (i : n) :
    star (completionSparseVector u i) ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda)
          (conj (lambda i) / 2) 0 *ᵥ x) =
      star (completionSparseVector u i) ⬝ᵥ
        ((G + completionR G lambda) *ᵥ x) := by
  rw [star_completionSparseVector_dotProduct, star_completionSparseVector_dotProduct]
  congr 1
  simp only [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro j _
  change matrixHerglotzKernel (completionResolventModel G lambda)
      (conj (lambda i) / 2) 0 i j * x j =
    (G + completionR G lambda) i j * x j
  rw [completionResolventKernel_sample_zero_apply hG lambda i j]

/-- The selected origin/sample pairing uses precisely the `G+R` block. -/
theorem completionResolventKernel_selected_zero_sample {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (u x : n → ℂ) (j : n) :
    star x ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda)
          0 (conj (lambda j) / 2) *ᵥ completionSparseVector u j) =
      star x ⬝ᵥ
        ((G + completionR G lambda) *ᵥ completionSparseVector u j) := by
  simp only [dotProduct, mulVec_completionSparseVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [completionResolventKernel_zero_sample_apply hG lambda i j]

/-- The origin/origin scalar pairing is the `2G` block. -/
theorem completionResolventKernel_selected_zero_zero {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (x : n → ℂ) :
    star x ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda) 0 0 *ᵥ x) =
      star x ⬝ᵥ (((2 : ℂ) • G) *ᵥ x) := by
  have hmatrix :
      matrixHerglotzKernel (completionResolventModel G lambda) 0 0 =
        (2 : ℂ) • G := by
    ext i j
    exact completionResolventKernel_zero_zero_apply hG lambda i j
  rw [hmatrix]

/-- Full finite sampling calculation for the known resolvent part.  The four summands are
exactly the four terms on manuscript lines 152--153, before substituting the formula for `v`. -/
theorem completionResolventKernel_sampling_quadratic_eq {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (u : n → ℂ) :
    (∑ a : Option n, ∑ b : Option n,
      star (completionSampleVector G lambda u a) ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda)
          (completionSamplePoint lambda a) (completionSamplePoint lambda b) *ᵥ
            completionSampleVector G lambda u b)) =
      star (completionV G (completionP G lambda) u) ⬝ᵥ
          (((2 : ℂ) • G) *ᵥ completionV G (completionP G lambda) u) +
        star (completionV G (completionP G lambda) u) ⬝ᵥ
          ((G + completionR G lambda) *ᵥ u) +
        star u ⬝ᵥ
          ((G + completionR G lambda) *ᵥ completionV G (completionP G lambda) u) +
        star u ⬝ᵥ
          (((4 : ℂ) • completionR G lambda - (2 : ℂ) • completionP G lambda) *ᵥ u) := by
  simp only [Fintype.sum_option, completionSampleVector, completionSamplePoint]
  rw [completionResolventKernel_selected_zero_zero hG lambda]
  simp_rw [completionResolventKernel_selected_zero_sample hG lambda]
  simp_rw [completionResolventKernel_selected_sample_zero hG lambda]
  simp_rw [completionResolventKernel_selected_sample_sample hG lambda hlambda]
  rw [sum_sparse_right_pairing, Finset.sum_add_distrib,
    sum_sparse_left_pairing, sum_sparse_sparse_quadratic]
  abel

omit [DecidableEq n] in
/-- Conjugating a matrix pairing swaps its vectors and conjugate-transposes the matrix. -/
theorem conj_star_dotProduct_mulVec (A : SquareMatrix n) (x y : n → ℂ) :
    star (star x ⬝ᵥ (A *ᵥ y)) = star y ⬝ᵥ (Aᴴ *ᵥ x) := by
  calc
    star (star x ⬝ᵥ (A *ᵥ y)) =
        star (star (star (A *ᵥ y) ⬝ᵥ x)) := by
      rw [Matrix.star_dotProduct]
    _ = star (A *ᵥ y) ⬝ᵥ x := by rw [star_star]
    _ = (star y ᵥ* Aᴴ) ⬝ᵥ x := by rw [Matrix.star_mulVec]
    _ = star y ⬝ᵥ (Aᴴ *ᵥ x) := by rw [Matrix.dotProduct_mulVec]

/-- The diagonal matrix formed from the unknown values `dᵢ(conj(λᵢ)/2)`. -/
def completionSampleDiagonal (d : ℂ → n → ℂ) (lambda : n → ℂ) : SquareMatrix n :=
  Matrix.diagonal fun i ↦ d (conj (lambda i) / 2) i

/-- Right multiplication by the adjoint of the sample diagonal scales column `j` by the
conjugate of its sampled value. -/
theorem mul_completionSampleDiagonal_conjTranspose_apply
    (A : SquareMatrix n) (d : ℂ → n → ℂ) (lambda : n → ℂ) (i j : n) :
    (A * (completionSampleDiagonal d lambda)ᴴ) i j =
      A i j * conj (d (conj (lambda j) / 2) j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, completionSampleDiagonal,
    Matrix.diagonal]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- The unknown term `D(z)G` in the transformed positive-real function. -/
def completionCorrectionModel (G : SquareMatrix n) (d : ℂ → n → ℂ)
    (z : ℂ) : SquareMatrix n :=
  completionDiagonalCorrection d z * G

theorem completionCorrectionModel_apply (G : SquareMatrix n) (d : ℂ → n → ℂ)
    (z : ℂ) (i j : n) :
    completionCorrectionModel G d z i j = d z i * G i j := by
  simp [completionCorrectionModel, completionDiagonalCorrection, Matrix.mul_apply,
    Matrix.diagonal]

/-- The transformed function is the sum of its known resolvent and unknown correction parts. -/
theorem completionKernelModel_eq_resolvent_add_correction
    (G : SquareMatrix n) (lambda : n → ℂ) (d : ℂ → n → ℂ) (z : ℂ) :
    completionKernelModel G lambda d z =
      completionResolventModel G lambda z + completionCorrectionModel G d z := by
  rfl

omit [Fintype n] [DecidableEq n] in
/-- The Herglotz kernel construction is additive in the matrix-valued function. -/
theorem matrixHerglotzKernel_add {K₁ K₂ : ℂ → SquareMatrix n} (z w : ℂ) :
    matrixHerglotzKernel (fun a ↦ K₁ a + K₂ a) z w =
      matrixHerglotzKernel K₁ z w + matrixHerglotzKernel K₂ z w := by
  simp [matrixHerglotzKernel, smul_add, add_assoc, add_left_comm]

/-- At two nonzero samples, the compressed unknown block is `ΔP + PΔᴴ`. -/
theorem completionCorrectionKernel_sample_sample_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (d : ℂ → n → ℂ) (i j : n) :
    matrixHerglotzKernel (completionCorrectionModel G d)
        (conj (lambda i) / 2) (conj (lambda j) / 2) i j =
      (completionSampleDiagonal d lambda * completionP G lambda +
        completionP G lambda * (completionSampleDiagonal d lambda)ᴴ) i j := by
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  have houter :
      1 - conj (lambda i) / 2 * conj (conj (lambda j) / 2) =
        1 - conj (lambda i) * lambda j / 4 := by
    simp only [map_div₀, starRingEnd_self_apply, map_ofNat]
    ring
  rw [Matrix.add_apply,
    mul_completionSampleDiagonal_conjTranspose_apply]
  simp only [matrixHerglotzKernel, completionCorrectionModel_apply,
    Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    completionSampleDiagonal, completionP, Matrix.mul_apply]
  rw [houter]
  simp [Matrix.diagonal, hGentry, div_eq_mul_inv]
  ring

/-- The compressed sample/origin unknown block is `ΔG`. -/
theorem completionCorrectionKernel_sample_zero_apply {G : SquareMatrix n}
    (lambda : n → ℂ) (d : ℂ → n → ℂ) (hd0 : d 0 = 0) (i j : n) :
    matrixHerglotzKernel (completionCorrectionModel G d)
        (conj (lambda i) / 2) 0 i j =
      (completionSampleDiagonal d lambda * G) i j := by
  simp [matrixHerglotzKernel, completionCorrectionModel_apply,
    completionSampleDiagonal, Matrix.mul_apply, Matrix.diagonal, hd0]

/-- The compressed origin/sample unknown block is `GΔᴴ`. -/
theorem completionCorrectionKernel_zero_sample_apply {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (d : ℂ → n → ℂ)
    (hd0 : d 0 = 0) (i j : n) :
    matrixHerglotzKernel (completionCorrectionModel G d)
        0 (conj (lambda j) / 2) i j =
      (G * (completionSampleDiagonal d lambda)ᴴ) i j := by
  have hGentry : conj (G j i) = G i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun₂ hG.eq i j
  rw [mul_completionSampleDiagonal_conjTranspose_apply]
  simp [matrixHerglotzKernel, completionCorrectionModel_apply, hd0, hGentry]
  ring

/-- The origin/origin unknown block vanishes because `D(0)=0`. -/
theorem completionCorrectionKernel_zero_zero {G : SquareMatrix n}
    (d : ℂ → n → ℂ) (hd0 : d 0 = 0) :
    matrixHerglotzKernel (completionCorrectionModel G d) 0 0 = 0 := by
  ext i j
  simp [matrixHerglotzKernel, completionCorrectionModel_apply, hd0]

/-- Selected sample/sample pairing for the unknown term. -/
theorem completionCorrectionKernel_selected_sample_sample {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (d : ℂ → n → ℂ)
    (u : n → ℂ) (i j : n) :
    star (completionSparseVector u i) ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          (conj (lambda i) / 2) (conj (lambda j) / 2) *ᵥ
            completionSparseVector u j) =
      star (completionSparseVector u i) ⬝ᵥ
        ((completionSampleDiagonal d lambda * completionP G lambda +
            completionP G lambda * (completionSampleDiagonal d lambda)ᴴ) *ᵥ
          completionSparseVector u j) := by
  simp only [star_completionSparseVector_dotProduct, mulVec_completionSparseVector]
  rw [completionCorrectionKernel_sample_sample_apply hG lambda d i j]

/-- Selected sample/origin pairing for the unknown term. -/
theorem completionCorrectionKernel_selected_sample_zero {G : SquareMatrix n}
    (lambda : n → ℂ) (d : ℂ → n → ℂ) (hd0 : d 0 = 0)
    (u x : n → ℂ) (i : n) :
    star (completionSparseVector u i) ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          (conj (lambda i) / 2) 0 *ᵥ x) =
      star (completionSparseVector u i) ⬝ᵥ
        ((completionSampleDiagonal d lambda * G) *ᵥ x) := by
  rw [star_completionSparseVector_dotProduct, star_completionSparseVector_dotProduct]
  congr 1
  simp only [Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro j _
  change matrixHerglotzKernel (completionCorrectionModel G d)
      (conj (lambda i) / 2) 0 i j * x j =
    (completionSampleDiagonal d lambda * G) i j * x j
  rw [completionCorrectionKernel_sample_zero_apply lambda d hd0 i j]

/-- Selected origin/sample pairing for the unknown term. -/
theorem completionCorrectionKernel_selected_zero_sample {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (d : ℂ → n → ℂ)
    (hd0 : d 0 = 0) (u x : n → ℂ) (j : n) :
    star x ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          0 (conj (lambda j) / 2) *ᵥ completionSparseVector u j) =
      star x ⬝ᵥ
        ((G * (completionSampleDiagonal d lambda)ᴴ) *ᵥ
          completionSparseVector u j) := by
  simp only [dotProduct, mulVec_completionSparseVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [completionCorrectionKernel_zero_sample_apply hG lambda d hd0 i j]

/-- Full finite sampling calculation for the unknown diagonal correction. -/
theorem completionCorrectionKernel_sampling_quadratic_eq {G : SquareMatrix n}
    (hG : G.IsHermitian) (lambda : n → ℂ) (d : ℂ → n → ℂ) (hd0 : d 0 = 0)
    (u : n → ℂ) :
    (∑ a : Option n, ∑ b : Option n,
      star (completionSampleVector G lambda u a) ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          (completionSamplePoint lambda a) (completionSamplePoint lambda b) *ᵥ
            completionSampleVector G lambda u b)) =
      star (completionV G (completionP G lambda) u) ⬝ᵥ
          ((G * (completionSampleDiagonal d lambda)ᴴ) *ᵥ u) +
        star u ⬝ᵥ
          ((completionSampleDiagonal d lambda * G) *ᵥ
            completionV G (completionP G lambda) u) +
        star u ⬝ᵥ
          ((completionSampleDiagonal d lambda * completionP G lambda +
              completionP G lambda * (completionSampleDiagonal d lambda)ᴴ) *ᵥ u) := by
  simp only [Fintype.sum_option, completionSampleVector, completionSamplePoint]
  rw [completionCorrectionKernel_zero_zero (G := G) d hd0]
  simp only [Matrix.zero_mulVec, dotProduct_zero, zero_add]
  simp_rw [completionCorrectionKernel_selected_zero_sample hG lambda d hd0]
  simp_rw [completionCorrectionKernel_selected_sample_zero lambda d hd0]
  simp_rw [completionCorrectionKernel_selected_sample_sample hG lambda d]
  rw [sum_sparse_right_pairing, Finset.sum_add_distrib,
    sum_sparse_left_pairing, sum_sparse_sparse_quadratic]
  abel

/-- Matrix-pairing form of the unknown half-contribution. -/
theorem completionUnknownHalfContribution_eq_matrixPairing
    (G : SquareMatrix n) (lambda : n → ℂ) (d : ℂ → n → ℂ) (u : n → ℂ) :
    completionUnknownHalfContribution G lambda d u =
      star u ⬝ᵥ
        (completionSampleDiagonal d lambda *ᵥ
          (G *ᵥ completionV G (completionP G lambda) u +
            completionP G lambda *ᵥ u)) := by
  simp [completionUnknownHalfContribution, completionSampleDiagonal,
    Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, mul_assoc]

/-- The complete unknown sampling sum is one half-contribution plus its conjugate, exactly the
`2 RePart` term in manuscript lines 128--136. -/
theorem completionCorrectionKernel_sampling_eq_unknownContribution
    {G : SquareMatrix n} (hG : G.IsHermitian) (lambda : n → ℂ)
    (d : ℂ → n → ℂ) (hd0 : d 0 = 0) (u : n → ℂ) :
    (∑ a : Option n, ∑ b : Option n,
      star (completionSampleVector G lambda u a) ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          (completionSamplePoint lambda a) (completionSamplePoint lambda b) *ᵥ
            completionSampleVector G lambda u b)) =
      completionUnknownHalfContribution G lambda d u +
        star (completionUnknownHalfContribution G lambda d u) := by
  let Delta := completionSampleDiagonal d lambda
  let P := completionP G lambda
  let v := completionV G P u
  have hP : P.IsHermitian := completionP_isHermitian hG lambda
  have hhalf : completionUnknownHalfContribution G lambda d u =
      star u ⬝ᵥ ((Delta * G) *ᵥ v) +
        star u ⬝ᵥ ((Delta * P) *ᵥ u) := by
    rw [completionUnknownHalfContribution_eq_matrixPairing]
    change star u ⬝ᵥ (Delta *ᵥ (G *ᵥ v + P *ᵥ u)) = _
    rw [Matrix.mulVec_add, dotProduct_add,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hhalfStar : star (completionUnknownHalfContribution G lambda d u) =
      star v ⬝ᵥ ((G * Deltaᴴ) *ᵥ u) +
        star u ⬝ᵥ ((P * Deltaᴴ) *ᵥ u) := by
    rw [hhalf, star_add,
      conj_star_dotProduct_mulVec, conj_star_dotProduct_mulVec]
    simp only [Matrix.conjTranspose_mul, hG.eq, hP.eq]
  rw [completionCorrectionKernel_sampling_quadratic_eq hG lambda d hd0 u]
  change star v ⬝ᵥ ((G * Deltaᴴ) *ᵥ u) +
      star u ⬝ᵥ ((Delta * G) *ᵥ v) +
      star u ⬝ᵥ ((Delta * P + P * Deltaᴴ) *ᵥ u) = _
  rw [Matrix.add_mulVec, dotProduct_add, hhalfStar, hhalf]
  abel

/-- With the manuscript's choice `v=-G⁻¹Pu`, the entire sampled unknown correction vanishes. -/
theorem completionCorrectionKernel_sampling_eq_zero
    {G : SquareMatrix n} (hGherm : G.IsHermitian) (hG : IsUnit G)
    (lambda : n → ℂ) (d : ℂ → n → ℂ) (hd0 : d 0 = 0) (u : n → ℂ) :
    (∑ a : Option n, ∑ b : Option n,
      star (completionSampleVector G lambda u a) ⬝ᵥ
        (matrixHerglotzKernel (completionCorrectionModel G d)
          (completionSamplePoint lambda a) (completionSamplePoint lambda b) *ᵥ
            completionSampleVector G lambda u b)) = 0 := by
  rw [completionCorrectionKernel_sampling_eq_unknownContribution hGherm lambda d hd0 u,
    completionUnknownHalfContribution_eq_zero G lambda d u hG]
  simp

/-- Matrix form of the substitution `v=-G⁻¹Pu`. -/
def completionSubstitutionMatrix (G P : SquareMatrix n) : SquareMatrix n :=
  -(G⁻¹ * P)

/-- Applying the substitution matrix gives the vector chosen in manuscript equation (4). -/
theorem completionSubstitutionMatrix_mulVec (G P : SquareMatrix n) (u : n → ℂ) :
    completionSubstitutionMatrix G P *ᵥ u = completionV G P u := by
  simp only [completionSubstitutionMatrix, completionV, Matrix.neg_mulVec]
  rw [Matrix.mulVec_mulVec]

/-- Conjugate transpose of the substitution matrix under the manuscript's Hermiticity data. -/
theorem completionSubstitutionMatrix_conjTranspose {G P : SquareMatrix n}
    (hG : G.IsHermitian) (hP : P.IsHermitian) :
    (completionSubstitutionMatrix G P)ᴴ = -(P * G⁻¹) := by
  simp [completionSubstitutionMatrix, Matrix.conjTranspose_nonsing_inv,
    hG.eq, hP.eq]

omit [DecidableEq n] in
/-- A quadratic form pulled back along a matrix is the quadratic form of its congruence. -/
theorem quadratic_mulVec_eq_congruence (A V : SquareMatrix n) (u : n → ℂ) :
    star (V *ᵥ u) ⬝ᵥ (A *ᵥ (V *ᵥ u)) =
      star u ⬝ᵥ ((Vᴴ * A * V) *ᵥ u) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

omit [DecidableEq n] in
/-- Pullback identity for a mixed term with the substituted vector in the first slot. -/
theorem mixed_mulVec_left_eq (B V : SquareMatrix n) (u : n → ℂ) :
    star (V *ᵥ u) ⬝ᵥ (B *ᵥ u) =
      star u ⬝ᵥ ((Vᴴ * B) *ᵥ u) := by
  simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

omit [DecidableEq n] in
/-- Pullback identity for a mixed term with the substituted vector in the second slot. -/
theorem mixed_mulVec_right_eq (B V : SquareMatrix n) (u : n → ℂ) :
    star u ⬝ᵥ (B *ᵥ (V *ᵥ u)) =
      star u ⬝ᵥ ((B * V) *ᵥ u) := by
  rw [Matrix.mulVec_mulVec]

/-- The four compressed kernel blocks reduce exactly to the coefficient defined after the
substitution in manuscript line 154. -/
theorem completionCompressedCoefficient_eq {G P R : SquareMatrix n}
    (hGherm : G.IsHermitian) (hP : P.IsHermitian) (hG : IsUnit G) :
    let V := completionSubstitutionMatrix G P
    Vᴴ * ((2 : ℂ) • G) * V + Vᴴ * (G + R) + (G + R) * V +
        ((4 : ℂ) • R - (2 : ℂ) • P) =
      completionSampleCoefficient G P R := by
  dsimp
  rw [completionSubstitutionMatrix_conjTranspose hGherm hP]
  have hdet : IsUnit G.det := G.isUnit_iff_isUnit_det.mp hG
  have hleft := G.nonsing_inv_mul hdet
  have hright := G.mul_nonsing_inv hdet
  have hrightP : G * (G⁻¹ * P) = P := by
    rw [← Matrix.mul_assoc, hright, one_mul]
  simp only [completionSubstitutionMatrix, completionSampleCoefficient,
    Algebra.smul_def, map_ofNat]
  noncomm_ring [hleft, hright, hrightP]

/-- The known resolvent sampling sum is the quadratic form of the sampled coefficient. -/
theorem completionResolventKernel_sampling_eq_sampleCoefficient
    {G : SquareMatrix n} (hGherm : G.IsHermitian) (hG : IsUnit G)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (u : n → ℂ) :
    (∑ a : Option n, ∑ b : Option n,
      star (completionSampleVector G lambda u a) ⬝ᵥ
        (matrixHerglotzKernel (completionResolventModel G lambda)
          (completionSamplePoint lambda a) (completionSamplePoint lambda b) *ᵥ
            completionSampleVector G lambda u b)) =
      star u ⬝ᵥ
        (completionSampleCoefficient G (completionP G lambda) (completionR G lambda) *ᵥ u) := by
  let P := completionP G lambda
  let R := completionR G lambda
  let V := completionSubstitutionMatrix G P
  have hP : P.IsHermitian := completionP_isHermitian hGherm lambda
  rw [completionResolventKernel_sampling_quadratic_eq hGherm lambda hlambda]
  change star (completionV G P u) ⬝ᵥ
        (((2 : ℂ) • G) *ᵥ completionV G P u) +
      star (completionV G P u) ⬝ᵥ ((G + R) *ᵥ u) +
      star u ⬝ᵥ ((G + R) *ᵥ completionV G P u) +
      star u ⬝ᵥ (((4 : ℂ) • R - (2 : ℂ) • P) *ᵥ u) = _
  have hv : completionV G P u = V *ᵥ u :=
    (completionSubstitutionMatrix_mulVec G P u).symm
  rw [hv]
  change star (V *ᵥ u) ⬝ᵥ (((2 : ℂ) • G) *ᵥ (V *ᵥ u)) +
      star (V *ᵥ u) ⬝ᵥ ((G + R) *ᵥ u) +
      star u ⬝ᵥ ((G + R) *ᵥ (V *ᵥ u)) +
      star u ⬝ᵥ (((4 : ℂ) • R - (2 : ℂ) • P) *ᵥ u) = _
  rw [quadratic_mulVec_eq_congruence, mixed_mulVec_left_eq,
    mixed_mulVec_right_eq]
  rw [← dotProduct_add, ← Matrix.add_mulVec,
    ← dotProduct_add, ← Matrix.add_mulVec,
    ← dotProduct_add, ← Matrix.add_mulVec]
  rw [completionCompressedCoefficient_eq hGherm hP hG]

/-- Kernel decomposition corresponding to `K = K₀ + DG`. -/
theorem completionKernelModel_kernel_eq_add
    (G : SquareMatrix n) (lambda : n → ℂ) (d : ℂ → n → ℂ) (z w : ℂ) :
    matrixHerglotzKernel (completionKernelModel G lambda d) z w =
      matrixHerglotzKernel (completionResolventModel G lambda) z w +
        matrixHerglotzKernel (completionCorrectionModel G d) z w := by
  change matrixHerglotzKernel
      (fun a ↦ completionResolventModel G lambda a + completionCorrectionModel G d a) z w = _
  exact matrixHerglotzKernel_add z w

/-- Positivity of the model Herglotz kernel supplies the exact quadratic inequality for the
sampled coefficient after the unknown correction is cancelled. -/
theorem completionSampleCoefficient_quadratic_nonneg_of_positiveKernel
    {G : SquareMatrix n} (hGherm : G.IsHermitian) (hG : IsUnit G)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (d : ℂ → n → ℂ) (hd0 : d 0 = 0)
    (hKernel : IsPositiveMatrixKernelOn openUnitDisk
      (matrixHerglotzKernel (completionKernelModel G lambda d))) :
    ∀ u : n → ℂ,
      0 ≤ star u ⬝ᵥ
        (completionSampleCoefficient G (completionP G lambda) (completionR G lambda) *ᵥ u) := by
  intro u
  have hsample := finite_type_sampling_quadratic_nonneg hKernel
    (completionSamplePoint lambda)
    (completionSamplePoint_mem_openUnitDisk lambda hlambda)
    (completionSampleVector G lambda u)
  simp_rw [completionKernelModel_kernel_eq_add G lambda d] at hsample
  simp only [Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib] at hsample
  rw [completionResolventKernel_sampling_eq_sampleCoefficient
      hGherm hG lambda hlambda u,
    completionCorrectionKernel_sampling_eq_zero hGherm hG lambda d hd0 u,
    add_zero] at hsample
  exact hsample

/-- Manuscript equation (5), now derived from kernel positivity rather than assumed. -/
theorem completion_X_inequality_of_positiveKernel
    {G : SquareMatrix n} (hGherm : G.IsHermitian) (hG : IsUnit G)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (d : ℂ → n → ℂ) (hd0 : d 0 = 0)
    (hKernel : IsPositiveMatrixKernelOn openUnitDisk
      (matrixHerglotzKernel (completionKernelModel G lambda d))) :
    (4 * completionX G lambda - completionX G lambda * G⁻¹ * completionP G lambda -
      completionP G lambda * G⁻¹ * completionX G lambda).PosSemidef := by
  apply completion_X_inequality_of_sampling hGherm hG
  exact completionSampleCoefficient_quadratic_nonneg_of_positiveKernel
    hGherm hG lambda hlambda d hd0 hKernel

end CrouzeixConjecture
