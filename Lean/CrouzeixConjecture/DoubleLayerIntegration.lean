module

public import CrouzeixConjecture.DoubleLayerGeometry
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

namespace CrouzeixConjecture

variable {i n : Type*} [MeasurableSpace i] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The positive-semidefinite cone is closed in the standard finite-product topology on
complex matrices.  This is the topology used by the Bochner integral on matrices. -/
theorem isClosed_setOf_posSemidef :
    IsClosed {A : SquareMatrix n | A.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · rw [show {A : SquareMatrix n | ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)} =
        ⋂ x, {A : SquareMatrix n | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} by
      ext A
      simp]
    exact isClosed_iInter fun x ↦
      isClosed_le continuous_const
        (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

/-- The Loewner upper cones are closed for the standard topology on complex matrices. -/
def squareMatrixClosedIciTopology : ClosedIciTopology (SquareMatrix n) :=
  ⟨by
    intro A
    rw [show Set.Ici A =
        (fun B : SquareMatrix n ↦ B - A) ⁻¹' {B : SquareMatrix n | B.PosSemidef} by
      ext B
      simp only [Set.mem_Ici, Set.mem_preimage, Matrix.le_iff]
      rfl]
    exact isClosed_setOf_posSemidef.preimage (continuous_id.sub continuous_const)⟩

/-- Bochner integration preserves positive semidefiniteness of a pointwise positive
matrix-valued density. -/
theorem integral_posSemidef {mu : Measure i} {f : i → SquareMatrix n}
    (hf : ∀ x, (f x).PosSemidef) :
    (∫ x, f x ∂mu).PosSemidef := by
  letI := squareMatrixClosedIciTopology (n := n)
  have hnonneg : ∀ x, (0 : SquareMatrix n) ≤ f x := fun x ↦ (hf x).nonneg
  exact Matrix.nonneg_iff_posSemidef.mp (MeasureTheory.integral_nonneg hnonneg)

/-- The same positivity conclusion from an almost-everywhere hypothesis. -/
theorem integral_posSemidef_of_ae {mu : Measure i} {f : i → SquareMatrix n}
    (hf : ∀ᵐ x ∂mu, (f x).PosSemidef) :
    (∫ x, f x ∂mu).PosSemidef := by
  letI := squareMatrixClosedIciTopology (n := n)
  have hnonneg : ∀ᵐ x ∂mu, (0 : SquareMatrix n) ≤ f x :=
    hf.mono fun x hx ↦ hx.nonneg
  exact Matrix.nonneg_iff_posSemidef.mp
    (MeasureTheory.integral_nonneg_of_ae hnonneg)

/-- Conjugate transpose as a real-linear map on complex matrices. -/
def matrixConjTransposeRealLinear :
    SquareMatrix n →ₗ[ℝ] SquareMatrix n where
  toFun A := Aᴴ
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' r A := by
    ext a b
    simp

/-- The preceding real-linear map is continuous because the matrix space is finite
dimensional. -/
def matrixConjTransposeCLM :
    SquareMatrix n →L[ℝ] SquareMatrix n :=
  matrixConjTransposeRealLinear.toContinuousLinearMap

/-- Conjugate transpose commutes with the Bochner integral of an integrable matrix-valued
function. -/
theorem conjTranspose_integral {mu : Measure i} {f : i → SquareMatrix n}
    (hf : Integrable f mu) :
    (∫ x, f x ∂mu)ᴴ = ∫ x, (f x)ᴴ ∂mu := by
  have h := (matrixConjTransposeCLM (n := n)).integral_comp_comm hf
  exact h.symm

/-- Pointwise positivity of the double-layer density makes its half-mass integral positive,
which is the positivity of the manuscript map `Φ` on a nonnegative scalar boundary input. -/
theorem doubleLayerIntegralAverage_posSemidef
    (mu : Measure i) (firstPart secondPart : i → SquareMatrix n)
    (hpositive : ∀ x, (firstPart x + secondPart x).PosSemidef) :
    (doubleLayerIntegralAverage mu firstPart secondPart).PosSemidef := by
  have hintegral :
      (∫ x, firstPart x + secondPart x ∂mu).PosSemidef :=
    integral_posSemidef hpositive
  change (((2 : ℂ)⁻¹) • ∫ x, firstPart x + secondPart x ∂mu).PosSemidef
  have hreal := hintegral.smul (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
  have heq :
      ((2 : ℂ)⁻¹) • (∫ x, firstPart x + secondPart x ∂mu) =
        ((2 : ℝ)⁻¹) • (∫ x, firstPart x + secondPart x ∂mu) := by
    ext a b
    norm_num [Complex.real_smul]
  rw [heq]
  exact hreal

end CrouzeixConjecture
