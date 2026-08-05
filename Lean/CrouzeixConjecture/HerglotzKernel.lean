module

public import CrouzeixConjecture.Definitions
public import Mathlib.Analysis.Complex.Order

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace CrouzeixConjecture

/-- The open unit disk used in the manuscript. -/
def openUnitDisk : Set ℂ := Metric.ball 0 1

/-- The unit circle supporting a Herglotz representing measure. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- The block matrix obtained by sampling a matrix-valued kernel at finitely many points. -/
def sampledKernelMatrix {n : Type*} {m : ℕ}
    (L : ℂ → ℂ → SquareMatrix n) (z : Fin m → ℂ) :
    Matrix (Fin m × n) (Fin m × n) ℂ :=
  fun i j ↦ L (z i.1) (z j.1) i.2 j.2

/-- Positivity of every finite sampling whose points lie in a prescribed set. -/
def IsPositiveMatrixKernelOn {n : Type*} (s : Set ℂ)
    (L : ℂ → ℂ → SquareMatrix n) : Prop :=
  ∀ (m : ℕ) (z : Fin m → ℂ),
    (∀ i, z i ∈ s) → (sampledKernelMatrix L z).PosSemidef

/-- The matrix-valued Herglotz kernel from `eq:herglotz-kernel`. -/
def matrixHerglotzKernel {n : Type*} (K : ℂ → SquareMatrix n) (z w : ℂ) :
    SquareMatrix n :=
  (1 - z * starRingEnd ℂ w)⁻¹ • (K z + (K w)ᴴ)

/-- The block-matrix definition of kernel positivity implies exactly the finite quadratic-form
inequality in `eq:positive-kernel-definition`. -/
theorem finite_sampling_quadratic_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {s : Set ℂ} {L : ℂ → ℂ → SquareMatrix n} (hL : IsPositiveMatrixKernelOn s L)
    {m : ℕ} (z : Fin m → ℂ) (hz : ∀ i, z i ∈ s) (ξ : Fin m → n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j) := by
  let x : Fin m × n → ℂ := fun ia ↦ ξ ia.1 ia.2
  have hpair : 0 ≤ ∑ ia : Fin m × n, ∑ jb : Fin m × n,
      star (ξ ia.1 ia.2) * L (z ia.1) (z jb.1) ia.2 jb.2 * ξ jb.1 jb.2 := by
    have h := (hL m z hz).dotProduct_mulVec_nonneg x
    simpa [dotProduct, Matrix.mulVec, sampledKernelMatrix, x, Finset.mul_sum,
      mul_assoc] using h
  rw [show (∑ i, ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j)) =
      ∑ ia : Fin m × n, ∑ jb : Fin m × n,
        star (ξ ia.1 ia.2) * L (z ia.1) (z jb.1) ia.2 jb.2 * ξ jb.1 jb.2 by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    rfl
    ]
  exact hpair

end CrouzeixConjecture
