module

public import CrouzeixConjecture.CompletionGramianBridge
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Gram matrix `G = SᴴS`; it is positive definite when `S` is invertible, as in the
manuscript's diagonalization. -/
def completionGramMatrix (S : SquareMatrix n) : SquareMatrix n :=
  Sᴴ * S

/-- The canonical positive square root `G¹⁄²`, constructed by continuous functional calculus. -/
def completionPositiveSquareRoot (S : SquareMatrix n) : SquareMatrix n :=
  CFC.sqrt (completionGramMatrix S)

/-- The nonsingular inverse of the positive square root; when `S` is invertible this is the
genuine inverse `G⁻¹⁄²`. -/
def completionPositiveInvSquareRoot (S : SquareMatrix n) : SquareMatrix n :=
  (completionPositiveSquareRoot S)⁻¹

omit [DecidableEq n] in
/-- Every Gram matrix `SᴴS` is positive semidefinite. -/
theorem completionGramMatrix_posSemidef (S : SquareMatrix n) :
    (completionGramMatrix S).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self S

/-- An invertible `S` has an invertible Gram matrix. -/
theorem completionGramMatrix_isUnit (S : SquareMatrix n) (hS : IsUnit S) :
    IsUnit (completionGramMatrix S) := by
  change IsUnit (Sᴴ * S)
  have h := hS.star.mul hS
  change IsUnit (Sᴴ * S) at h
  exact h

/-- Consequently the manuscript's Gram matrix is positive definite. -/
theorem completionGramMatrix_posDef (S : SquareMatrix n) (hS : IsUnit S) :
    (completionGramMatrix S).PosDef :=
  (completionGramMatrix_posSemidef S).posDef_iff_isUnit.mpr
    (completionGramMatrix_isUnit S hS)

/-- An invertible change-of-basis matrix `S` produces all square-root data used by the
completion–Gramian argument.  In particular, this theorem discharges every field of
`CompletionSquareRootData`; none remains as an assumption. -/
theorem completionSquareRootData_of_isUnit (S : SquareMatrix n) (hS : IsUnit S) :
    CompletionSquareRootData (completionGramMatrix S)
      (completionPositiveSquareRoot S) (completionPositiveInvSquareRoot S) := by
  have hGnonneg : 0 ≤ completionGramMatrix S :=
    (completionGramMatrix_posSemidef S).nonneg
  have hGunit : IsUnit (completionGramMatrix S) := completionGramMatrix_isUnit S hS
  have hHunit : IsUnit (completionPositiveSquareRoot S) := by
    exact (CFC.isUnit_sqrt_iff (completionGramMatrix S) hGnonneg).2 hGunit
  have hHdet : IsUnit (completionPositiveSquareRoot S).det :=
    (completionPositiveSquareRoot S).isUnit_iff_isUnit_det.mp hHunit
  have hHhermitian : (completionPositiveSquareRoot S).IsHermitian := by
    have hHnonneg := CFC.sqrt_nonneg (completionGramMatrix S)
    exact (Matrix.nonneg_iff_posSemidef.mp hHnonneg).isHermitian
  refine
    { hH_selfAdjoint := hHhermitian.eq
      hHinv_selfAdjoint := hHhermitian.inv.eq
      hH_mul_H := ?_
      hH_mul_Hinv := ?_
      hHinv_mul_H := ?_ }
  · exact CFC.sqrt_mul_sqrt_self (completionGramMatrix S) hGnonneg
  · exact (completionPositiveSquareRoot S).mul_nonsing_inv hHdet
  · exact (completionPositiveSquareRoot S).nonsing_inv_mul hHdet

/-- The matrix `T = S Λ S⁻¹` in the manuscript's simple-spectrum reduction. -/
def completionDiagonalizableMatrix (S : SquareMatrix n) (lambda : n → ℂ) :
    SquareMatrix n :=
  S * completionEigenvalueDiagonal lambda * S⁻¹

/-- The unitary polar factor `U = S G⁻¹⁄²`. -/
def completionPolarUnitary (S : SquareMatrix n) : SquareMatrix n :=
  S * completionPositiveInvSquareRoot S

/-- The inverse of `S` recovered from the positive square-root data. -/
theorem completion_nonsing_inv_eq_invSquareRoot_sq_mul_conjTranspose
    (S : SquareMatrix n) (hS : IsUnit S) :
    S⁻¹ = completionPositiveInvSquareRoot S *
      completionPositiveInvSquareRoot S * Sᴴ := by
  apply Matrix.inv_eq_left_inv
  calc
    (completionPositiveInvSquareRoot S * completionPositiveInvSquareRoot S * Sᴴ) * S =
        (completionPositiveInvSquareRoot S * completionPositiveInvSquareRoot S) *
          (Sᴴ * S) := by noncomm_ring
    _ = (completionPositiveInvSquareRoot S * completionPositiveInvSquareRoot S) *
          completionGramMatrix S := rfl
    _ = 1 := completionSquareRoot_inverse_mul
      (completionSquareRootData_of_isUnit S hS)

/-- The explicit polar factor `S G⁻¹⁄²` is unitary. -/
theorem completionPolarUnitary_mem_unitaryGroup (S : SquareMatrix n) (hS : IsUnit S) :
    completionPolarUnitary S ∈ Matrix.unitaryGroup n ℂ := by
  have hsqrt := completionSquareRootData_of_isUnit S hS
  rw [Matrix.mem_unitaryGroup_iff']
  change (S * completionPositiveInvSquareRoot S)ᴴ *
      (S * completionPositiveInvSquareRoot S) = 1
  rw [Matrix.conjTranspose_mul, hsqrt.hHinv_selfAdjoint]
  calc
    (completionPositiveInvSquareRoot S * Sᴴ) *
          (S * completionPositiveInvSquareRoot S) =
        completionPositiveInvSquareRoot S * (Sᴴ * S) *
          completionPositiveInvSquareRoot S := by noncomm_ring
    _ = completionPositiveInvSquareRoot S *
          (completionPositiveSquareRoot S * completionPositiveSquareRoot S) *
            completionPositiveInvSquareRoot S := by
      rw [hsqrt.hH_mul_H]
      rfl
    _ = (completionPositiveInvSquareRoot S * completionPositiveSquareRoot S) *
          (completionPositiveSquareRoot S * completionPositiveInvSquareRoot S) := by
      noncomm_ring
    _ = 1 := by
      rw [hsqrt.hHinv_mul_H, hsqrt.hH_mul_Hinv]
      exact one_mul 1

/-- The original diagonalization is unitarily conjugate to the completion similarity
`C = G¹⁄² Λ G⁻¹⁄²`. -/
theorem completionDiagonalizableMatrix_eq_unitary_conjugate
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ) :
    completionDiagonalizableMatrix S lambda =
      completionPolarUnitary S *
        completionSimilarity (completionPositiveSquareRoot S)
          (completionPositiveInvSquareRoot S) lambda *
        (completionPolarUnitary S)ᴴ := by
  have hsqrt := completionSquareRootData_of_isUnit S hS
  rw [completionDiagonalizableMatrix, completionPolarUnitary, completionSimilarity,
    Matrix.conjTranspose_mul, hsqrt.hHinv_selfAdjoint,
    completion_nonsing_inv_eq_invSquareRoot_sq_mul_conjTranspose S hS]
  symm
  calc
    (S * completionPositiveInvSquareRoot S) *
          (completionPositiveSquareRoot S * completionEigenvalueDiagonal lambda *
            completionPositiveInvSquareRoot S) *
        (completionPositiveInvSquareRoot S * Sᴴ) =
        S * (completionPositiveInvSquareRoot S * completionPositiveSquareRoot S) *
          completionEigenvalueDiagonal lambda * completionPositiveInvSquareRoot S *
            completionPositiveInvSquareRoot S * Sᴴ := by
      noncomm_ring
    _ = S * completionEigenvalueDiagonal lambda *
          (completionPositiveInvSquareRoot S * completionPositiveInvSquareRoot S * Sᴴ) := by
      rw [hsqrt.hHinv_mul_H]
      simp only [mul_one]
      noncomm_ring

/-- The polar factor is an explicit unitary witness for the manuscript's bridge. -/
theorem exists_unitary_completion_polar_bridge
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ) :
    ∃ U : SquareMatrix n,
      U ∈ Matrix.unitaryGroup n ℂ ∧
        completionDiagonalizableMatrix S lambda =
          U * completionSimilarity (completionPositiveSquareRoot S)
            (completionPositiveInvSquareRoot S) lambda * Uᴴ := by
  exact ⟨completionPolarUnitary S, completionPolarUnitary_mem_unitaryGroup S hS,
    completionDiagonalizableMatrix_eq_unitary_conjugate S hS lambda⟩

/-- Unitary conjugation preserves the selected matrix norm, which is the induced Euclidean
operator norm in this project. -/
theorem completionDiagonalizableMatrix_norm_eq_completionSimilarity_norm
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ) :
    ‖completionDiagonalizableMatrix S lambda‖ =
      ‖completionSimilarity (completionPositiveSquareRoot S)
        (completionPositiveInvSquareRoot S) lambda‖ := by
  rw [completionDiagonalizableMatrix_eq_unitary_conjugate S hS lambda]
  have hU : completionPolarUnitary S ∈ unitary (SquareMatrix n) :=
    completionPolarUnitary_mem_unitaryGroup S hS
  have hUstar : (completionPolarUnitary S)ᴴ ∈ unitary (SquareMatrix n) := by
    exact Unitary.star_mem hU
  calc
    ‖completionPolarUnitary S *
          completionSimilarity (completionPositiveSquareRoot S)
            (completionPositiveInvSquareRoot S) lambda *
        (completionPolarUnitary S)ᴴ‖ =
        ‖completionSimilarity (completionPositiveSquareRoot S)
            (completionPositiveInvSquareRoot S) lambda *
          (completionPolarUnitary S)ᴴ‖ := by
      rw [mul_assoc]
      exact CStarRing.norm_mem_unitary_mul _ hU
    _ = ‖completionSimilarity (completionPositiveSquareRoot S)
          (completionPositiveInvSquareRoot S) lambda‖ :=
      CStarRing.norm_mul_mem_unitary _ hUstar

/-- Operator-level form of the same equality: these are induced Euclidean operator norms. -/
theorem completionDiagonalizableMatrix_euclideanOperator_norm_eq
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ) :
    ‖euclideanOperator (completionDiagonalizableMatrix S lambda)‖ =
      ‖euclideanOperator
        (completionSimilarity (completionPositiveSquareRoot S)
          (completionPositiveInvSquareRoot S) lambda)‖ := by
  rw [← matrix_norm_eq_euclidean_operator_norm,
    ← matrix_norm_eq_euclidean_operator_norm]
  exact completionDiagonalizableMatrix_norm_eq_completionSimilarity_norm S hS lambda

end CrouzeixConjecture
