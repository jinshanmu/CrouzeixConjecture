module

public import CrouzeixConjecture.PositiveRealCompletion
public import CrouzeixConjecture.SimpleSpectrumBridge
public import CrouzeixConjecture.GeneratedAlgebra
public import CrouzeixConjecture.MatrixHerglotz

@[expose] public section

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An explicit simple diagonalization is the manuscript matrix `SΛS⁻¹` using the same
nonsingular inverse as the rest of the project. -/
theorem SimpleDiagonalization.eq_completionDiagonalizableMatrix
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) :
    B = completionDiagonalizableMatrix hB.changeBasis.val hB.eigenvalues := by
  simpa [completionDiagonalizableMatrix, completionEigenvalueDiagonal,
    innerConjugation] using hB.eq_conjugate

/-- Every diagonal entry in an explicit diagonalization belongs to the matrix spectrum. -/
theorem SimpleDiagonalization.eigenvalue_mem_matrixSpectrum
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (i : n) :
    hB.eigenvalues i ∈ matrixSpectrum B := by
  let D := Matrix.diagonal hB.eigenvalues
  have hchar : B.charpoly = D.charpoly := by
    calc
      B.charpoly = (innerConjugation hB.changeBasis D).charpoly :=
        congrArg Matrix.charpoly hB.eq_conjugate
      _ = D.charpoly := by
        change (hB.changeBasis.val * D * hB.changeBasis.inv).charpoly = D.charpoly
        simpa only [Units.inv_eq_val_inv] using
          Matrix.charpoly_units_conj hB.changeBasis D
  apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
  rw [hchar, Matrix.charpoly_diagonal]
  exact (Polynomial.isRoot_prod Finset.univ
    (fun j ↦ Polynomial.X - Polynomial.C (hB.eigenvalues j))
    (hB.eigenvalues i)).mpr ⟨i, Finset.mem_univ i, by simp⟩

/-- A spectral closed-disk hypothesis gives the entrywise disk bound needed by the completion
sampling and Gramian series. -/
theorem SimpleDiagonalization.eigenvalues_norm_le_one
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (hspectrum : matrixSpectrum B ⊆ closedUnitDisk) :
    ∀ i, ‖hB.eigenvalues i‖ ≤ 1 := by
  intro i
  have hi := hspectrum (hB.eigenvalue_mem_matrixSpectrum i)
  simpa [closedUnitDisk, Metric.mem_closedBall, dist_eq_norm] using hi

omit [Fintype n] [DecidableEq n] in
/-- The scalar denominators in the diagonalized resolvent do not vanish in the open disk,
even when an eigenvalue lies on the boundary of the closed disk. -/
theorem completion_resolvent_denominator_ne_zero
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    {z : ℂ} (hz : z ∈ unitDisk) (i : n) :
    1 - z * lambda i ≠ 0 := by
  have hzNorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hproduct : ‖z * lambda i‖ < 1 := by
    rw [norm_mul]
    calc
      ‖z‖ * ‖lambda i‖ ≤ ‖z‖ * 1 :=
        mul_le_mul_of_nonneg_left (hlambda i) (norm_nonneg z)
      _ < 1 := by simpa using hzNorm
  apply sub_ne_zero.mpr
  intro hone
  have : ‖z * lambda i‖ = 1 := by rw [← hone]; norm_num
  linarith

/-- Factoring the resolvent through an invertible diagonalization. -/
theorem one_sub_smul_completionDiagonalizableMatrix
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ) (z : ℂ) :
    1 - z • completionDiagonalizableMatrix S lambda =
      S * (1 - z • completionEigenvalueDiagonal lambda) * S⁻¹ := by
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  rw [completionDiagonalizableMatrix]
  calc
    1 - z • (S * completionEigenvalueDiagonal lambda * S⁻¹) =
        S * S⁻¹ - z • (S * completionEigenvalueDiagonal lambda * S⁻¹) := by
      rw [S.mul_nonsing_inv hSdet]
    _ = S * (1 - z • completionEigenvalueDiagonal lambda) * S⁻¹ := by
      simp only [mul_sub, sub_mul, mul_one, mul_smul_comm, smul_mul_assoc]

/-- The inverse resolvent of a diagonalizable matrix is the similarity of the entrywise
diagonal inverse.  The proof constructs and verifies a left inverse explicitly. -/
theorem completionDiagonalizableMatrix_resolvent_inv
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) {z : ℂ} (hz : z ∈ unitDisk) :
    (1 - z • completionDiagonalizableMatrix S lambda)⁻¹ =
      S * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) * S⁻¹ := by
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  have hSinvS : S⁻¹ * S = 1 := S.nonsing_inv_mul hSdet
  have hSSinv : S * S⁻¹ = 1 := S.mul_nonsing_inv hSdet
  have hdiagonal :
      1 - z • completionEigenvalueDiagonal lambda =
        Matrix.diagonal (fun i ↦ 1 - z * lambda i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [completionEigenvalueDiagonal]
    · simp [completionEigenvalueDiagonal, hij]
  have hdiagonalLeftInverse :
      Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) *
          (1 - z • completionEigenvalueDiagonal lambda) = 1 := by
    rw [hdiagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [completion_resolvent_denominator_ne_zero lambda hlambda hz i]
    · simp [hij]
  apply Matrix.inv_eq_left_inv
  rw [one_sub_smul_completionDiagonalizableMatrix S hS lambda z]
  calc
    (S * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) * S⁻¹) *
          (S * (1 - z • completionEigenvalueDiagonal lambda) * S⁻¹) =
        S * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) *
          (S⁻¹ * S) * (1 - z • completionEigenvalueDiagonal lambda) * S⁻¹ := by
      noncomm_ring
    _ = S *
          (Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) *
            (1 - z • completionEigenvalueDiagonal lambda)) * S⁻¹ := by
      rw [hSinvS]
      simp only [mul_one]
      noncomm_ring
    _ = 1 := by rw [hdiagonalLeftInverse, mul_one, hSSinv]

/-- Pulling the resolvent back by `Sᴴ` and `S` gives exactly the manuscript's known kernel
term `G (I-zΛ)⁻¹`. -/
theorem completion_resolvent_pullback
    (S : SquareMatrix n) (hS : IsUnit S) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) {z : ℂ} (hz : z ∈ unitDisk) :
    Sᴴ * (1 - z • completionDiagonalizableMatrix S lambda)⁻¹ * S =
      completionResolventModel (completionGramMatrix S) lambda z := by
  rw [completionDiagonalizableMatrix_resolvent_inv S hS lambda hlambda hz]
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  have hSinvS : S⁻¹ * S = 1 := S.nonsing_inv_mul hSdet
  rw [completionResolventModel, completionGramMatrix]
  calc
    Sᴴ *
          (S * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) * S⁻¹) * S =
        (Sᴴ * S) * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) *
          (S⁻¹ * S) := by
      noncomm_ring
    _ = (Sᴴ * S) * Matrix.diagonal (fun i ↦ (1 - z * lambda i)⁻¹) := by
      rw [hSinvS, mul_one]

/-- The positive-real function pulled back through the diagonalizing basis. -/
def completionPullbackFunction (S : SquareMatrix n)
    (H : ℂ → SquareMatrix n) (z : ℂ) : SquareMatrix n :=
  Sᴴ * H z * S

/-- Constant left and right matrix multiplication preserve analyticity. -/
theorem completionPullbackFunction_analyticOnNhd
    (S : SquareMatrix n) {H : ℂ → SquareMatrix n} {s : Set ℂ}
    (hH : AnalyticOnNhd ℂ H s) :
    AnalyticOnNhd ℂ (completionPullbackFunction S H) s := by
  intro z hz
  exact (analyticAt_const.mul (hH z hz)).mul analyticAt_const

omit [DecidableEq n] in
/-- Real part commutes with the pullback congruence `A ↦ SᴴAS`. -/
theorem rePart_completionPullbackFunction
    (S : SquareMatrix n) (H : ℂ → SquareMatrix n) (z : ℂ) :
    rePart (completionPullbackFunction S H z) =
      Sᴴ * rePart (H z) * S := by
  simp only [completionPullbackFunction, rePart, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    mul_add, add_mul]
  noncomm_ring

omit [DecidableEq n] in
/-- Positive real part is preserved by the diagonalizing pullback. -/
theorem completionPullbackFunction_rePart_posSemidef
    (S : SquareMatrix n) {H : ℂ → SquareMatrix n} {z : ℂ}
    (hH : IsPositiveMatrix (rePart (H z))) :
    IsPositiveMatrix (rePart (completionPullbackFunction S H z)) := by
  rw [rePart_completionPullbackFunction]
  exact posSemidef_congruence hH S

/-- A function normalized by `H(0)=I` pulls back to the Gram matrix at the origin. -/
theorem completionPullbackFunction_zero
    (S : SquareMatrix n) {H : ℂ → SquareMatrix n} (hH0 : H 0 = 1) :
    completionPullbackFunction S H 0 = completionGramMatrix S := by
  simp [completionPullbackFunction, completionGramMatrix, hH0]

/-- Conjugate transpose of a diagonal similarity is a diagonal similarity by the starred
inverse unit. -/
theorem innerConjugation_conjTranspose_diagonal
    (u : (SquareMatrix n)ˣ) (lambda : n → ℂ) :
    (innerConjugation u (Matrix.diagonal lambda))ᴴ =
      innerConjugation (star u⁻¹)
        (Matrix.diagonal fun i ↦ conj (lambda i)) := by
  ext i j
  simp [innerConjugation, Matrix.mul_apply, Matrix.diagonal, mul_comm, mul_left_comm]

/-- Polynomial evaluation in `Bᴴ`, pulled back by `Sᴴ` and `S`, is a diagonal matrix times
the Gram matrix.  This is the algebraic isomorphism behind `eq:adjoint-algebra-diagonal`. -/
theorem polynomialEval_conjTranspose_diagonalization
    (u : (SquareMatrix n)ˣ) (lambda : n → ℂ) (p : Polynomial ℂ) :
    u.valᴴ *
        polynomialEval p (innerConjugation u (Matrix.diagonal lambda))ᴴ *
        u.val =
      Matrix.diagonal (fun i ↦ Polynomial.eval (conj (lambda i)) p) *
        completionGramMatrix u.val := by
  rw [innerConjugation_conjTranspose_diagonal]
  let v : (SquareMatrix n)ˣ := star u⁻¹
  have hpoly :
      polynomialEval p
          (innerConjugation v (Matrix.diagonal fun i ↦ conj (lambda i))) =
        innerConjugation v
          (polynomialEval p (Matrix.diagonal fun i ↦ conj (lambda i))) := by
    exact Polynomial.aeval_algHom_apply (innerConjugation v)
      (Matrix.diagonal fun i ↦ conj (lambda i)) p
  rw [hpoly, polynomialEval_diagonal]
  change u.valᴴ *
      (v.val * Matrix.diagonal (fun i ↦ Polynomial.eval (conj (lambda i)) p) * v.inv) *
      u.val = _
  change u.valᴴ *
      ((u.inv)ᴴ * Matrix.diagonal (fun i ↦ Polynomial.eval (conj (lambda i)) p) *
        u.valᴴ) * u.val = _
  rw [completionGramMatrix]
  have hleft : u.valᴴ * (u.inv)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, u.inv_val, Matrix.conjTranspose_one]
  simp only [← Matrix.mul_assoc]
  rw [hleft, Matrix.one_mul]

/-- Every element of `alg(Bᴴ)` has exactly the diagonal-times-Gram form used in
`eq:adjoint-algebra-diagonal`. -/
theorem exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose
    {B X : SquareMatrix n} (hB : SimpleDiagonalization B)
    (hX : X ∈ generatedAlgebra Bᴴ) :
    ∃ d : n → ℂ,
      hB.changeBasis.valᴴ * X * hB.changeBasis.val =
        Matrix.diagonal d * completionGramMatrix hB.changeBasis.val := by
  obtain ⟨p, hp⟩ :=
    (generatedAlgebra_mem_iff_exists_polynomial Bᴴ X).mp hX
  refine ⟨fun i ↦ Polynomial.eval (conj (hB.eigenvalues i)) p, ?_⟩
  have hpolyEq :
      polynomialEval p Bᴴ =
        polynomialEval p
          (innerConjugation hB.changeBasis
            (Matrix.diagonal hB.eigenvalues))ᴴ := by
    exact congrArg (polynomialEval p) (congrArg Matrix.conjTranspose hB.eq_conjugate)
  calc
    hB.changeBasis.valᴴ * X * hB.changeBasis.val =
        hB.changeBasis.valᴴ * polynomialEval p Bᴴ * hB.changeBasis.val := by rw [hp]
    _ = hB.changeBasis.valᴴ *
          polynomialEval p
            (innerConjugation hB.changeBasis
              (Matrix.diagonal hB.eigenvalues))ᴴ *
          hB.changeBasis.val := by rw [hpolyEq]
    _ = _ := polynomialEval_conjTranspose_diagonalization
      hB.changeBasis hB.eigenvalues p

/-- Pointwise generated-algebra membership gives one correction function, chosen to vanish at
the origin.  No analyticity of this chosen coordinate function is needed later: analyticity of
the original transformed function supplies the Herglotz theorem directly. -/
theorem exists_completionDiagonalCorrection
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (X : ℂ → SquareMatrix n) (hX0 : X 0 = 0)
    (hX : ∀ z ∈ unitDisk, X z ∈ generatedAlgebra Bᴴ) :
    ∃ d : ℂ → n → ℂ, d 0 = 0 ∧
      ∀ z ∈ unitDisk,
        hB.changeBasis.valᴴ * X z * hB.changeBasis.val =
          completionDiagonalCorrection d z * completionGramMatrix hB.changeBasis.val := by
  classical
  have hexists (z : ℂ) (hz : z ∈ unitDisk) :
      ∃ a : n → ℂ,
        hB.changeBasis.valᴴ * X z * hB.changeBasis.val =
          Matrix.diagonal a * completionGramMatrix hB.changeBasis.val :=
    exists_diagonal_correction_of_mem_generatedAlgebra_conjTranspose hB (hX z hz)
  let d : ℂ → n → ℂ := fun z ↦
    if hz : z ∈ unitDisk then
      if hzero : z = 0 then 0 else Classical.choose (hexists z hz)
    else 0
  refine ⟨d, ?_, ?_⟩
  · simp [d, unitDisk]
  · intro z hz
    by_cases hzero : z = 0
    · subst z
      simp [d, unitDisk, hX0, completionDiagonalCorrection]
    · simpa [d, hz, hzero, completionDiagonalCorrection] using
        (Classical.choose_spec (hexists z hz))

/-- The auxiliary generated-algebra condition in a positive-real completion produces exactly
the model `G(I-zΛ)⁻¹ + D(z)G` after pulling back by the common diagonalizing basis.  The
diagonal entries of the target matrix need not be distinct. -/
theorem exists_completionKernelModel_of_isPositiveRealCompletion
    {B T : SquareMatrix n} (hB : SimpleDiagonalization B) (lambda : n → ℂ)
    (hT : T = innerConjugation hB.changeBasis (Matrix.diagonal lambda))
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    {H : ℂ → SquareMatrix n} (hcompletion : IsPositiveRealCompletion B T H) :
    ∃ d : ℂ → n → ℂ, d 0 = 0 ∧
      ∀ z ∈ unitDisk,
        completionPullbackFunction hB.changeBasis.val H z =
          completionKernelModel
            (completionGramMatrix hB.changeBasis.val) lambda d z := by
  rcases hcompletion with ⟨_, hH0, _, hgenerated⟩
  let X : ℂ → SquareMatrix n := fun z ↦ H z - (1 - z • T)⁻¹
  have hX0 : X 0 = 0 := by simp [X, hH0]
  have hX : ∀ z ∈ unitDisk, X z ∈ generatedAlgebra Bᴴ := by
    intro z hz
    exact hgenerated z hz
  obtain ⟨d, hd0, hd⟩ := exists_completionDiagonalCorrection hB X hX0 hX
  refine ⟨d, hd0, ?_⟩
  intro z hz
  have hS : IsUnit hB.changeBasis.val := hB.changeBasis.isUnit
  have hmatrix : T = completionDiagonalizableMatrix
      hB.changeBasis.val lambda := by
    simpa [completionDiagonalizableMatrix, completionEigenvalueDiagonal,
      innerConjugation] using hT
  have hresolvent :
      hB.changeBasis.valᴴ * (1 - z • T)⁻¹ * hB.changeBasis.val =
        completionResolventModel (completionGramMatrix hB.changeBasis.val)
          lambda z := by
    have harg :
        1 - z • T =
          1 - z • completionDiagonalizableMatrix
            hB.changeBasis.val lambda :=
      congrArg (fun A : SquareMatrix n ↦ 1 - z • A) hmatrix
    have hinv :
        (1 - z • T)⁻¹ =
          (1 - z • completionDiagonalizableMatrix
            hB.changeBasis.val lambda)⁻¹ := by
      exact congrArg (fun A : SquareMatrix n ↦ A⁻¹) harg
    rw [hinv]
    exact completion_resolvent_pullback hB.changeBasis.val hS
      lambda hlambda hz
  have hcorrection := hd z hz
  change hB.changeBasis.valᴴ * H z * hB.changeBasis.val = _
  calc
    hB.changeBasis.valᴴ * H z * hB.changeBasis.val =
        hB.changeBasis.valᴴ * (1 - z • T)⁻¹ * hB.changeBasis.val +
          hB.changeBasis.valᴴ * X z * hB.changeBasis.val := by
      dsimp [X]
      noncomm_ring
    _ = completionResolventModel (completionGramMatrix hB.changeBasis.val)
          lambda z +
        completionDiagonalCorrection d z *
          completionGramMatrix hB.changeBasis.val := by
      rw [hresolvent, hcorrection]
    _ = completionKernelModel (completionGramMatrix hB.changeBasis.val)
          lambda d z := by
      rfl

omit [Fintype n] [DecidableEq n] in
/-- Kernel positivity is unchanged when the underlying functions agree on the sampled set. -/
theorem matrixHerglotzKernel_positive_congr_on
    {K L : ℂ → SquareMatrix n} {s : Set ℂ}
    (hK : IsPositiveMatrixKernelOn s (matrixHerglotzKernel K))
    (hKL : ∀ z ∈ s, K z = L z) :
    IsPositiveMatrixKernelOn s (matrixHerglotzKernel L) := by
  intro m z hz
  have hsample := hK m z hz
  have heq :
      sampledKernelMatrix (matrixHerglotzKernel K) z =
        sampledKernelMatrix (matrixHerglotzKernel L) z := by
    ext p q
    simp only [sampledKernelMatrix, matrixHerglotzKernel]
    rw [hKL (z p.1) (hz p.1), hKL (z q.1) (hz q.1)]
  rwa [← heq]

/-- The auxiliary-basis positive-real completion theorem.  All kernel, Gramian, eigenvector,
direct first-term, square-root, and polar-decomposition inputs have been discharged by preceding
declarations, without any distinctness requirement on the target diagonal entries. -/
theorem positiveRealCompletionStatement [Nonempty n] :
    PositiveRealCompletionStatement (n := n) := by
  intro B T H hB lambda hT hlambda hcompletion
  have hS : IsUnit hB.changeBasis.val := hB.changeBasis.isUnit
  obtain ⟨d, hd0, hmodel⟩ :=
    exists_completionKernelModel_of_isPositiveRealCompletion
      hB lambda hT hlambda hcompletion
  have hpullbackAnalytic :
      AnalyticOnNhd ℂ (completionPullbackFunction hB.changeBasis.val H)
        openUnitDisk := by
    have h := completionPullbackFunction_analyticOnNhd hB.changeBasis.val
      hcompletion.1
    simpa only [unitDisk, openUnitDisk] using h
  have hpullbackPositive :
      ∀ z ∈ openUnitDisk,
        (rePart (completionPullbackFunction hB.changeBasis.val H z)).PosSemidef := by
    intro z hz
    apply completionPullbackFunction_rePart_posSemidef
    exact hcompletion.2.2.1 z (by simpa only [unitDisk, openUnitDisk] using hz)
  have hpullbackKernel :
      IsPositiveMatrixKernelOn openUnitDisk
        (matrixHerglotzKernel
          (completionPullbackFunction hB.changeBasis.val H)) :=
    matrixHerglotzKernel_isPositiveMatrixKernelOn
      hpullbackAnalytic hpullbackPositive
  have hmodelOn :
      ∀ z ∈ openUnitDisk,
        completionPullbackFunction hB.changeBasis.val H z =
          completionKernelModel (completionGramMatrix hB.changeBasis.val)
            lambda d z := by
    intro z hz
    exact hmodel z (by simpa only [unitDisk, openUnitDisk] using hz)
  have hmodelKernel :
      IsPositiveMatrixKernelOn openUnitDisk
        (matrixHerglotzKernel
          (completionKernelModel (completionGramMatrix hB.changeBasis.val)
            lambda d)) :=
    matrixHerglotzKernel_positive_congr_on hpullbackKernel hmodelOn
  have hbound :
      ‖completionDiagonalizableMatrix hB.changeBasis.val lambda‖ ≤ 2 :=
    norm_completionDiagonalizableMatrix_le_two_of_positiveKernelModel
      hB.changeBasis.val hS lambda hlambda d hd0 hmodelKernel
  have hmatrix : T = completionDiagonalizableMatrix hB.changeBasis.val lambda := by
    simpa [completionDiagonalizableMatrix, completionEigenvalueDiagonal,
      innerConjugation] using hT
  rw [hmatrix]
  exact hbound

end CrouzeixConjecture
