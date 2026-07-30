module

public import CrouzeixConjecture.Spectrum

@[expose] public section

noncomputable section

open scoped Matrix

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by a unit, regarded as an algebra automorphism.  This is the
matrix change-of-basis map used in the manuscript. -/
def innerConjugation (u : (SquareMatrix n)ˣ) :
    SquareMatrix n ≃ₐ[ℂ] SquareMatrix n where
  toFun A := u.val * A * u.inv
  invFun A := u.inv * A * u.val
  left_inv A := by
    simp only [mul_assoc]
    rw [u.inv_val, mul_one, ← mul_assoc, u.inv_val, one_mul]
  right_inv A := by
    simp only [mul_assoc]
    rw [u.val_inv, mul_one, ← mul_assoc, u.val_inv, one_mul]
  map_add' A B := by rw [mul_add, add_mul]
  map_mul' A B := by
    simp only [mul_assoc]
    rw [← mul_assoc u.inv u.val (B * u.inv), u.inv_val, one_mul]
  commutes' z := by
    rw [← Algebra.commutes z (u : SquareMatrix n), mul_assoc, u.val_inv, mul_one]

/-- Explicit simple-spectrum diagonalization data: the matrix is similar to a
diagonal matrix whose diagonal entries are pairwise distinct. -/
structure SimpleDiagonalization (B : SquareMatrix n) where
  eigenvalues : n → ℂ
  changeBasis : (SquareMatrix n)ˣ
  eq_conjugate : B = innerConjugation changeBasis (Matrix.diagonal eigenvalues)
  eigenvalues_injective : Function.Injective eigenvalues

/-- Polynomial evaluation on a diagonal matrix is entrywise scalar evaluation. -/
theorem polynomialEval_diagonal (p : Polynomial ℂ) (nodes : n → ℂ) :
    polynomialEval p (Matrix.diagonal nodes) =
      Matrix.diagonal (fun i ↦ Polynomial.eval (nodes i) p) := by
  calc
    polynomialEval p (Matrix.diagonal nodes) =
        Matrix.diagonal (Polynomial.aeval nodes p) := by
      exact Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℂ) nodes p
    _ = Matrix.diagonal (fun i ↦ Polynomial.eval (nodes i) p) := by
      congr 1
      funext i
      rw [Polynomial.aeval_pi_apply₂]
      exact Polynomial.coe_aeval_eq_eval (nodes i) ▸ rfl

/-- Polynomial functional calculus preserves the eigenbasis supplied by a simple
diagonalization.  No separation hypothesis is imposed on the resulting diagonal entries. -/
theorem SimpleDiagonalization.polynomialEval_eq_innerConjugation_diagonal
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ) :
    polynomialEval p B =
      innerConjugation hB.changeBasis
        (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) p) := by
  calc
    polynomialEval p B =
        polynomialEval p
          (innerConjugation hB.changeBasis (Matrix.diagonal hB.eigenvalues)) := by
      exact congrArg (polynomialEval p) hB.eq_conjugate
    _ = innerConjugation hB.changeBasis
          (polynomialEval p (Matrix.diagonal hB.eigenvalues)) := by
      exact Polynomial.aeval_algHom_apply
        (innerConjugation hB.changeBasis) (Matrix.diagonal hB.eigenvalues) p
    _ = innerConjugation hB.changeBasis
          (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) p) := by
      exact congrArg (innerConjugation hB.changeBasis)
        (polynomialEval_diagonal p hB.eigenvalues)

end CrouzeixConjecture
