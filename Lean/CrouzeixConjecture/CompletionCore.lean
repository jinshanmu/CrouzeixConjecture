module

public import CrouzeixConjecture.CompletionEigenvector
public import Mathlib.Analysis.CStarAlgebra.Basic

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
/-- Unitary similarity preserves the induced Euclidean matrix norm. -/
theorem norm_unitary_conjugation (U : unitary (SquareMatrix n)) (C : SquareMatrix n) :
    ‖(U : SquareMatrix n) * C * (U : SquareMatrix n)ᴴ‖ = ‖C‖ := by
  rw [← Matrix.star_eq_conjTranspose]
  calc
    ‖(U : SquareMatrix n) * C * star (U : SquareMatrix n)‖ =
        ‖(U : SquareMatrix n) * C‖ :=
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop)
    _ = ‖C‖ := CStarRing.norm_coe_unitary_mul U C

/-- The completed second half of the positive-real completion argument: once the sampled kernel
has produced the Gramian anticommutator inequality and polar decomposition has identified `T`
with a unitary conjugate of `C`, the exact bound `‖T‖ ≤ 2` follows. -/
theorem norm_le_two_of_unitary_gramian_model {M : ℝ} (hM : 0 ≤ M)
    (T C : SquareMatrix n) (U : unitary (SquareMatrix n))
    (hTC : T = (U : SquareMatrix n) * C * (U : SquareMatrix n)ᴴ)
    (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M)
    (hineq : ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
      (gramian 2 C - gramian 4 C) * gramian 4 C -
      gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef) :
    ‖T‖ ≤ 2 := by
  rw [hTC, norm_unitary_conjugation]
  exact norm_le_two_of_gramian_inequality hM C hbound hineq

end CrouzeixConjecture
