module

public import CrouzeixConjecture.CompletionDiagonalization

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The explicit diagonal correction from manuscript lines 87--92.  Multiplication by the
inverse Gram matrix turns the pulled-back generated-algebra term into its diagonal factor. -/
def completionAnalyticDiagonalCorrection {B : SquareMatrix n}
    (hB : SimpleDiagonalization B) (X : ℂ → SquareMatrix n) (z : ℂ) :
    SquareMatrix n :=
  (hB.changeBasis.valᴴ * X z * hB.changeBasis.val) *
    (completionGramMatrix hB.changeBasis.val)⁻¹

/-- The explicit correction is analytic whenever the original generated-algebra term is
analytic.  This supplies the analyticity assertion in manuscript lines 87--92 without making
a pointwise choice of polynomial coordinates. -/
theorem completionAnalyticDiagonalCorrection_analyticOnNhd
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    {X : ℂ → SquareMatrix n} {s : Set ℂ}
    (hX : AnalyticOnNhd ℂ X s) :
    AnalyticOnNhd ℂ (completionAnalyticDiagonalCorrection hB X) s := by
  intro z hz
  simpa only [completionAnalyticDiagonalCorrection] using
    (((analyticAt_const.mul (hX z hz)).mul analyticAt_const).mul analyticAt_const)

/-- Normalization of the original term at zero gives the manuscript normalization `D(0)=0`. -/
theorem completionAnalyticDiagonalCorrection_zero
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    {X : ℂ → SquareMatrix n} (hX0 : X 0 = 0) :
    completionAnalyticDiagonalCorrection hB X 0 = 0 := by
  simp [completionAnalyticDiagonalCorrection, hX0]

/-- On the disk, generated-algebra membership forces the explicit analytic correction to be a
diagonal matrix. -/
theorem completionAnalyticDiagonalCorrection_eq_diagonal
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    {X : ℂ → SquareMatrix n}
    (hX : ∀ z ∈ unitDisk, X z ∈ generatedAlgebra Bᴴ)
    {z : ℂ} (hz : z ∈ unitDisk) :
    ∃ d : n → ℂ,
      completionAnalyticDiagonalCorrection hB X z = Matrix.diagonal d := by
  obtain ⟨d, hd⟩ :=
    exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose hB (hX z hz)
  refine ⟨d, ?_⟩
  have hGunit : IsUnit (completionGramMatrix hB.changeBasis.val) :=
    completionGramMatrix_isUnit hB.changeBasis.val hB.changeBasis.isUnit
  have hGdet : IsUnit (completionGramMatrix hB.changeBasis.val).det :=
    (completionGramMatrix hB.changeBasis.val).isUnit_iff_isUnit_det.mp hGunit
  rw [completionAnalyticDiagonalCorrection, hd, Matrix.mul_assoc,
    (completionGramMatrix hB.changeBasis.val).mul_nonsing_inv hGdet, Matrix.mul_one]

/-- Multiplying the explicit diagonal correction by the Gram matrix reconstructs the pulled-back
term exactly, as claimed in manuscript lines 87--92. -/
theorem completionAnalyticDiagonalCorrection_mul_completionGramMatrix
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (X : ℂ → SquareMatrix n) (z : ℂ) :
    hB.changeBasis.valᴴ * X z * hB.changeBasis.val =
      completionAnalyticDiagonalCorrection hB X z *
        completionGramMatrix hB.changeBasis.val := by
  have hGunit : IsUnit (completionGramMatrix hB.changeBasis.val) :=
    completionGramMatrix_isUnit hB.changeBasis.val hB.changeBasis.isUnit
  have hGdet : IsUnit (completionGramMatrix hB.changeBasis.val).det :=
    (completionGramMatrix hB.changeBasis.val).isUnit_iff_isUnit_det.mp hGunit
  symm
  rw [completionAnalyticDiagonalCorrection, Matrix.mul_assoc,
    (completionGramMatrix hB.changeBasis.val).nonsing_inv_mul hGdet, Matrix.mul_one]

/-- Manuscript lines 87--92, with all quantifiers explicit: an analytic term taking values in
`alg(Bᴴ)` has an analytic matrix-valued diagonal coordinate `D`, normalized at zero, whose
product with the Gram matrix is the pulled-back term. -/
theorem exists_analytic_completionDiagonalCorrection
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    {X : ℂ → SquareMatrix n}
    (hXanalytic : AnalyticOnNhd ℂ X unitDisk)
    (hX0 : X 0 = 0)
    (hXgenerated : ∀ z ∈ unitDisk, X z ∈ generatedAlgebra Bᴴ) :
    ∃ D : ℂ → SquareMatrix n,
      AnalyticOnNhd ℂ D unitDisk ∧
        D 0 = 0 ∧
        (∀ z ∈ unitDisk, ∃ d : n → ℂ, D z = Matrix.diagonal d) ∧
        ∀ z ∈ unitDisk,
          hB.changeBasis.valᴴ * X z * hB.changeBasis.val =
            D z * completionGramMatrix hB.changeBasis.val := by
  refine ⟨completionAnalyticDiagonalCorrection hB X,
    completionAnalyticDiagonalCorrection_analyticOnNhd hB hXanalytic,
    completionAnalyticDiagonalCorrection_zero hB hX0, ?_, ?_⟩
  · intro z hz
    exact completionAnalyticDiagonalCorrection_eq_diagonal hB hXgenerated hz
  · intro z _hz
    exact completionAnalyticDiagonalCorrection_mul_completionGramMatrix hB X z

end CrouzeixConjecture
