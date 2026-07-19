module

public import CrouzeixConjecture.Definitions

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- The matrix real part `(A + Aᴴ) / 2` is Hermitian. -/
theorem rePart_isHermitian {n : Type*} (A : SquareMatrix n) :
    (rePart A).IsHermitian := by
  simp [rePart, Matrix.IsHermitian, add_comm]

/-- Under the Euclidean matrix/operator equivalence, matrix real part becomes operator
real part. -/
theorem euclideanOperator_rePart {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) :
    euclideanOperator (rePart A) =
      (2 : ℂ)⁻¹ •
        (euclideanOperator A + ContinuousLinearMap.adjoint (euclideanOperator A)) := by
  rw [rePart, map_smul, map_add, euclideanOperator_conjTranspose]

/-- Positive semidefiniteness of a complex matrix is exactly positivity of the associated
Euclidean linear operator. -/
theorem isPositiveMatrix_iff_euclideanOperator_toLinearMap_isPositive
    {n : Type*} [Fintype n] [DecidableEq n] (A : SquareMatrix n) :
    IsPositiveMatrix A ↔ (euclideanOperator A).toLinearMap.IsPositive := by
  change A.PosSemidef ↔ A.toEuclideanLin.IsPositive
  exact Matrix.isPositive_toEuclideanLin_iff.symm

/-- Continuous-linear-map form of the matrix/operator positivity bridge. -/
theorem isPositiveMatrix_iff_euclideanOperator_isPositive
    {n : Type*} [Fintype n] [DecidableEq n] (A : SquareMatrix n) :
    IsPositiveMatrix A ↔ (euclideanOperator A).IsPositive :=
  (isPositiveMatrix_iff_euclideanOperator_toLinearMap_isPositive A).trans
    (ContinuousLinearMap.isPositive_toLinearMap_iff (euclideanOperator A))

/-- Positive semidefiniteness is preserved by the congruence `A ↦ Sᴴ A S`. -/
theorem posSemidef_congruence {n : Type*} [Fintype n] {A : SquareMatrix n}
    (hA : A.PosSemidef) (S : SquareMatrix n) :
    (Sᴴ * A * S).PosSemidef :=
  hA.conjTranspose_mul_mul_same S

/-- If `4 I - Cᴴ C` is positive semidefinite, the associated Euclidean operator has
norm at most `2`. -/
theorem euclideanOperator_norm_le_two_of_four_sub_conjTranspose_mul_self_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] (C : SquareMatrix n)
    (hC : ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C).PosSemidef) :
    ‖euclideanOperator C‖ ≤ 2 := by
  let T := euclideanOperator C
  have hPos :
      (euclideanOperator ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C)).IsPositive := by
    rw [← ContinuousLinearMap.isPositive_toLinearMap_iff]
    change ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C).toEuclideanLin.IsPositive
    rwa [Matrix.isPositive_toEuclideanLin_iff]
  have hOp :
      euclideanOperator ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C) =
        (4 : ℂ) • (1 : EuclideanVector n →L[ℂ] EuclideanVector n) -
          ContinuousLinearMap.adjoint T * T := by
    dsimp [T]
    rw [map_sub, map_smul, map_one, map_mul, euclideanOperator_conjTranspose]
  apply T.opNorm_le_bound (by norm_num)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
  have hq := hPos.re_inner_nonneg_right x
  rw [hOp] at hq
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply, inner_sub_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, pow_two] at hq
  norm_num at hq
  nlinarith

/-- In the induced Euclidean (`L2`) operator norm on matrices, positivity of
`4 I - Cᴴ C` implies `‖C‖ ≤ 2`. -/
theorem matrix_norm_le_two_of_four_sub_conjTranspose_mul_self_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n] (C : SquareMatrix n)
    (hC : ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C).PosSemidef) :
    ‖C‖ ≤ 2 := by
  rw [matrix_norm_eq_euclidean_operator_norm]
  exact euclideanOperator_norm_le_two_of_four_sub_conjTranspose_mul_self_posSemidef C hC

end CrouzeixConjecture
