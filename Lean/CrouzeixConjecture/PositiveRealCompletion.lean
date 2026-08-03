module

public import CrouzeixConjecture.CompletionKernelModel
public import CrouzeixConjecture.CompletionSquareRoot
public import CrouzeixConjecture.CompletionEigenvector

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The positive-real completion lemma after the manuscript's diagonalization and algebra
reduction have produced the explicit model `K(z)=G(I-zΛ)⁻¹+D(z)G`.  Unlike a conditional
Gramian lemma, this theorem constructs the actual positive square root of `G=SᴴS`, transports
the sampled kernel inequality through both Gramians, applies the direct first-term estimate,
and returns to `T=SΛS⁻¹` by the polar unitary. -/
theorem norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (d : ℂ → n → ℂ) (hd0 : d 0 = 0)
    (hKernel : IsPositiveMatrixKernelOn openUnitDisk
      (matrixHerglotzKernel
        (completionKernelModel (completionGramMatrix S) lambda d))) :
    ‖completionDiagonalizableMatrix S lambda‖ ≤ 2 := by
  let G := completionGramMatrix S
  let H := completionPositiveSquareRoot S
  let Hinv := completionPositiveInvSquareRoot S
  let C := completionSimilarity H Hinv lambda
  let M := ‖H‖ * ‖Hinv‖
  have hsqrt : CompletionSquareRootData G H Hinv := by
    exact completionSquareRootData_of_isUnit S hS
  have hGherm : G.IsHermitian := (completionGramMatrix_posSemidef S).isHermitian
  have hGunit : IsUnit G := completionGramMatrix_isUnit S hS
  have hsource :
      (4 * completionX G lambda -
          completionX G lambda * G⁻¹ * completionP G lambda -
        completionP G lambda * G⁻¹ * completionX G lambda).PosSemidef := by
    exact completion_X_inequality_of_positiveKernel
      hGherm hGunit lambda hlambda d hd0 hKernel
  have hineq :
      ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
          (gramian 2 C - gramian 4 C) * gramian 4 C -
        gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef := by
    have hineqRing := completion_gramian_expression_posSemidef_of_source
      hsqrt lambda hlambda hsource
    simpa only [C, Algebra.smul_def, map_ofNat] using hineqRing
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg H) (norm_nonneg Hinv)
  have hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M := by
    exact completionSimilarity_pow_norm_le hsqrt lambda hlambda
  rw [completionDiagonalizableMatrix_norm_eq_completionSimilarity_norm S hS lambda]
  exact norm_le_two_of_gramian_inequality hM C hbound hineq

end CrouzeixConjecture
