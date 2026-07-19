module

public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

noncomputable section

open WithLp
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- The manuscript's column space `\mathbb C^n`, equipped with its Euclidean norm. -/
abbrev EuclideanVector (n : Type*) := EuclideanSpace ℂ n

/-- The manuscript's square complex matrices. -/
abbrev SquareMatrix (n : Type*) := Matrix n n ℂ

/-- A square matrix acting on Euclidean space.  This is Mathlib's star-algebra equivalence,
so its norm is the induced Euclidean operator norm and its star is the Hilbert adjoint. -/
def euclideanOperator {n : Type*} [Fintype n] [DecidableEq n] :
    SquareMatrix n ≃⋆ₐ[ℂ] (EuclideanVector n →L[ℂ] EuclideanVector n) :=
  Matrix.toEuclideanCLM

/-- The same matrix-to-operator identification, bundled as a continuous linear map. -/
def euclideanOperatorCLM {n : Type*} [Fintype n] [DecidableEq n] :
    SquareMatrix n →L[ℂ] (EuclideanVector n →L[ℂ] EuclideanVector n) :=
  (euclideanOperator (n := n)).toAlgEquiv.toLinearEquiv.toLinearMap.mkContinuous 1 fun A ↦ by
    rw [one_mul]
    exact le_rfl

/-- The norm on matrices selected in this project is definitionally the induced Euclidean
operator norm. -/
theorem matrix_norm_eq_euclidean_operator_norm {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) : ‖A‖ = ‖euclideanOperator A‖ :=
  rfl

@[simp]
theorem euclideanOperatorCLM_apply {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) : euclideanOperatorCLM A = euclideanOperator A :=
  rfl

/-- Evaluation of the numerical-range quadratic form is a continuous linear functional of the
matrix argument. -/
def euclideanQuadraticFormCLM {n : Type*} [Fintype n] [DecidableEq n]
    (x : EuclideanVector n) : SquareMatrix n →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ (EuclideanVector n) x).comp
    euclideanOperatorCLM)

@[simp]
theorem euclideanQuadraticFormCLM_apply {n : Type*} [Fintype n] [DecidableEq n]
    (x : EuclideanVector n) (A : SquareMatrix n) :
    euclideanQuadraticFormCLM x A = ⟪x, euclideanOperator A x⟫_ℂ := by
  simp [euclideanQuadraticFormCLM]

/-- Mathlib's complex inner product is conjugate-linear in the first variable.  Consequently
`\langle x,Ax\rangle` is exactly the coordinate expression `x^* A x` used in the manuscript. -/
theorem inner_euclideanOperator_eq_star_dotProduct {n : Type*} [Fintype n]
    [DecidableEq n] (A : SquareMatrix n) (x : EuclideanVector n) :
    ⟪x, euclideanOperator A x⟫_ℂ = star (ofLp x) ⬝ᵥ (A *ᵥ ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (A *ᵥ ofLp x) ⬝ᵥ star (ofLp x) = star (ofLp x) ⬝ᵥ (A *ᵥ ofLp x)
  exact dotProduct_comm _ _

/-- Conjugate transpose of matrices is transported to the Hilbert-space adjoint. -/
theorem euclideanOperator_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    (A : SquareMatrix n) :
    euclideanOperator Aᴴ = ContinuousLinearMap.adjoint (euclideanOperator A) := by
  exact map_star (euclideanOperator (n := n)) A

end CrouzeixConjecture
