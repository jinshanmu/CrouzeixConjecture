module

public import CrouzeixConjecture.CompletionAlgebra
public import CrouzeixConjecture.CompletionSeries

@[expose] public section

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The algebraic square-root data used in manuscript lines 163–192.  For the manuscript's
positive definite Gram matrix `G = SᴴS`, take `H = G¹⁄²` and `Hinv = G⁻¹⁄²`.  The
four fields below are precisely the self-adjointness and two-sided inverse facts used by the
similarity and congruence calculations; no analytic property of a square root is hidden here. -/
structure CompletionSquareRootData (G H Hinv : SquareMatrix n) : Prop where
  hH_selfAdjoint : Hᴴ = H
  hHinv_selfAdjoint : Hinvᴴ = Hinv
  hH_mul_H : H * H = G
  hH_mul_Hinv : H * Hinv = 1
  hHinv_mul_H : Hinv * H = 1

/-- The diagonal matrix of the eigenvalues in the completion argument. -/
def completionEigenvalueDiagonal (lambda : n → ℂ) : SquareMatrix n :=
  Matrix.diagonal lambda

/-- The power-bounded matrix `C = G¹⁄² D G⁻¹⁄²` from manuscript line 182. -/
def completionSimilarity (H Hinv : SquareMatrix n) (lambda : n → ℂ) : SquareMatrix n :=
  H * completionEigenvalueDiagonal lambda * Hinv

@[simp]
theorem completionEigenvalueDiagonal_pow (lambda : n → ℂ) (k : ℕ) :
    completionEigenvalueDiagonal lambda ^ k = Matrix.diagonal (fun i ↦ lambda i ^ k) := by
  exact Matrix.diagonal_pow lambda k

/-- Powers telescope through the similarity because `Hinv` is a two-sided inverse of `H`. -/
theorem completionSimilarity_pow {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ) (k : ℕ) :
    completionSimilarity H Hinv lambda ^ k =
      H * completionEigenvalueDiagonal lambda ^ k * Hinv := by
  induction k with
  | zero =>
      simp only [pow_zero]
      simpa only [mul_one] using hsqrt.hH_mul_Hinv.symm
  | succ k ih =>
      rw [pow_succ, ih]
      simp only [completionSimilarity]
      calc
        (H * completionEigenvalueDiagonal lambda ^ k * Hinv) *
              (H * completionEigenvalueDiagonal lambda * Hinv) =
            H * completionEigenvalueDiagonal lambda ^ k * (Hinv * H) *
              completionEigenvalueDiagonal lambda * Hinv := by noncomm_ring
        _ = H * (completionEigenvalueDiagonal lambda ^ k *
              completionEigenvalueDiagonal lambda) * Hinv := by
          rw [hsqrt.hHinv_mul_H]
          simp only [mul_one, mul_assoc]

/-- Closed-unit-disk eigenvalues make every power of the diagonal matrix contractive. -/
theorem completionEigenvalueDiagonal_pow_norm_le_one (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (k : ℕ) :
    ‖completionEigenvalueDiagonal lambda ^ k‖ ≤ 1 := by
  rw [completionEigenvalueDiagonal_pow, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg
    (x := fun i : n ↦ lambda i ^ k) zero_le_one).2
  intro i
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hlambda i)

/-- The manuscript's similarity matrix has uniformly bounded powers. -/
theorem completionSimilarity_pow_norm_le {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (k : ℕ) :
    ‖completionSimilarity H Hinv lambda ^ k‖ ≤ ‖H‖ * ‖Hinv‖ := by
  rw [completionSimilarity_pow hsqrt lambda k]
  calc
    ‖H * completionEigenvalueDiagonal lambda ^ k * Hinv‖ ≤
        (‖H‖ * ‖completionEigenvalueDiagonal lambda ^ k‖) * ‖Hinv‖ :=
      le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (‖H‖ * 1) * ‖Hinv‖ := by
      gcongr
      exact completionEigenvalueDiagonal_pow_norm_le_one lambda hlambda k
    _ = ‖H‖ * ‖Hinv‖ := by ring

/-- Hence both weighted Gramian series used in the manuscript are norm convergent. -/
theorem summable_gramianTerm_completionSimilarity {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) {q : ℝ} (hq : 1 < q) :
    Summable (gramianTerm q (completionSimilarity H Hinv lambda)) := by
  exact summable_gramianTerm hq (mul_nonneg (norm_nonneg H) (norm_nonneg Hinv))
    (completionSimilarity H Hinv lambda)
    (completionSimilarity_pow_norm_le hsqrt lambda hlambda)

/-- The diagonal-basis form of one weighted Gramian summand. -/
def completionDiagonalGramianTerm (q : ℝ) (G : SquareMatrix n) (lambda : n → ℂ)
    (k : ℕ) : SquareMatrix n :=
  (q⁻¹ ^ k) •
    ((completionEigenvalueDiagonal lambda ^ k)ᴴ * G *
      completionEigenvalueDiagonal lambda ^ k)

/-- Termwise congruence between the manuscript's diagonal geometric series and the abstract
Gramian series. -/
theorem gramianTerm_completionSimilarity_eq {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ)
    (q : ℝ) (k : ℕ) :
    gramianTerm q (completionSimilarity H Hinv lambda) k =
      Hinv * completionDiagonalGramianTerm q G lambda k * Hinv := by
  rw [gramianTerm, completionDiagonalGramianTerm,
    completionSimilarity_pow hsqrt lambda k]
  simp only [Matrix.conjTranspose_mul, hsqrt.hH_selfAdjoint,
    hsqrt.hHinv_selfAdjoint]
  rw [← hsqrt.hH_mul_H]
  simp only [mul_smul_comm, smul_mul_assoc]
  congr 1
  noncomm_ring

/-- The reverse termwise congruence, obtained by multiplying by the square root on both sides. -/
theorem completionDiagonalGramianTerm_eq {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ)
    (q : ℝ) (k : ℕ) :
    completionDiagonalGramianTerm q G lambda k =
      H * gramianTerm q (completionSimilarity H Hinv lambda) k * H := by
  rw [gramianTerm_completionSimilarity_eq hsqrt lambda q k]
  calc
    completionDiagonalGramianTerm q G lambda k =
        (H * Hinv) * completionDiagonalGramianTerm q G lambda k * (Hinv * H) := by
      rw [hsqrt.hH_mul_Hinv, hsqrt.hHinv_mul_H]
      simp only [one_mul, mul_one]
    _ = H * (Hinv * completionDiagonalGramianTerm q G lambda k * Hinv) * H := by
      noncomm_ring

/-- Norm convergence of the diagonal-basis series follows from the already established
power bound and the reverse congruence. -/
theorem summable_completionDiagonalGramianTerm {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) {q : ℝ} (hq : 1 < q) :
    Summable (completionDiagonalGramianTerm q G lambda) := by
  have hs : Summable (gramianTerm q (completionSimilarity H Hinv lambda)) :=
    summable_gramianTerm_completionSimilarity hsqrt lambda hlambda hq
  exact ((hs.mul_left H).mul_right H).congr fun k ↦
    (completionDiagonalGramianTerm_eq hsqrt lambda q k).symm

/-- Entrywise geometric form of the denominator-`4` diagonal summand. -/
theorem completionDiagonalGramianTerm_four_apply (G : SquareMatrix n) (lambda : n → ℂ)
    (k : ℕ) (i j : n) :
  completionDiagonalGramianTerm 4 G lambda k i j =
      (conj (lambda i) * lambda j / 4) ^ k * G i j := by
  simp only [completionDiagonalGramianTerm, completionEigenvalueDiagonal_pow]
  simp
  rw [← inv_pow]
  ring

/-- Entrywise geometric form of the denominator-`2` diagonal summand. -/
theorem completionDiagonalGramianTerm_two_apply (G : SquareMatrix n) (lambda : n → ℂ)
    (k : ℕ) (i j : n) :
  completionDiagonalGramianTerm 2 G lambda k i j =
      (conj (lambda i) * lambda j / 2) ^ k * G i j := by
  simp only [completionDiagonalGramianTerm, completionEigenvalueDiagonal_pow]
  simp
  rw [← inv_pow]
  ring

omit [Fintype n] [DecidableEq n] in
/-- The product of two closed-unit-disk eigenvalues remains in the closed unit disk. -/
theorem completionEigenvalueProduct_norm_le_one (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    ‖conj (lambda i) * lambda j‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  calc
    ‖lambda i‖ * ‖lambda j‖ ≤ 1 * 1 :=
      mul_le_mul (hlambda i) (hlambda j) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

omit [Fintype n] [DecidableEq n] in
/-- The denominator-`4` ratio is strictly contractive. -/
theorem completionRatioFour_norm_lt_one (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    ‖conj (lambda i) * lambda j / 4‖ < 1 := by
  rw [norm_div]
  have hden : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [hden]
  calc
    ‖conj (lambda i) * lambda j‖ / 4 ≤ 1 / 4 := by
      gcongr
      exact completionEigenvalueProduct_norm_le_one lambda hlambda i j
    _ < 1 := by norm_num

omit [Fintype n] [DecidableEq n] in
/-- The denominator-`2` ratio is strictly contractive. -/
theorem completionRatioTwo_norm_lt_one (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    ‖conj (lambda i) * lambda j / 2‖ < 1 := by
  rw [norm_div]
  have hden : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hden]
  calc
    ‖conj (lambda i) * lambda j‖ / 2 ≤ 1 / 2 := by
      gcongr
      exact completionEigenvalueProduct_norm_le_one lambda hlambda i j
    _ < 1 := by norm_num

/-- Summing the denominator-`4` diagonal series gives exactly the manuscript's matrix `P`. -/
theorem tsum_completionDiagonalGramianTerm_four_eq_completionP
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    (∑' k : ℕ, completionDiagonalGramianTerm 4 G lambda k) =
      completionP G lambda := by
  have hs : Summable (completionDiagonalGramianTerm 4 G lambda) :=
    summable_completionDiagonalGramianTerm hsqrt lambda hlambda (by norm_num)
  ext i j
  rw [tsum_apply hs, tsum_apply (Pi.summable.1 hs i)]
  calc
    ∑' k : ℕ, completionDiagonalGramianTerm 4 G lambda k i j =
        ∑' k : ℕ, (conj (lambda i) * lambda j / 4) ^ k * G i j := by
      exact tsum_congr fun k ↦ completionDiagonalGramianTerm_four_apply G lambda k i j
    _ = (1 - conj (lambda i) * lambda j / 4)⁻¹ * G i j :=
      ((hasSum_geometric_of_norm_lt_one
        (completionRatioFour_norm_lt_one lambda hlambda i j)).mul_right (G i j)).tsum_eq
    _ = completionP G lambda i j := by
      simp only [completionP, div_eq_mul_inv]
      ring

/-- Summing the denominator-`2` diagonal series gives exactly the manuscript's matrix `R`. -/
theorem tsum_completionDiagonalGramianTerm_two_eq_completionR
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    (∑' k : ℕ, completionDiagonalGramianTerm 2 G lambda k) =
      completionR G lambda := by
  have hs : Summable (completionDiagonalGramianTerm 2 G lambda) :=
    summable_completionDiagonalGramianTerm hsqrt lambda hlambda (by norm_num)
  ext i j
  rw [tsum_apply hs, tsum_apply (Pi.summable.1 hs i)]
  calc
    ∑' k : ℕ, completionDiagonalGramianTerm 2 G lambda k i j =
        ∑' k : ℕ, (conj (lambda i) * lambda j / 2) ^ k * G i j := by
      exact tsum_congr fun k ↦ completionDiagonalGramianTerm_two_apply G lambda k i j
    _ = (1 - conj (lambda i) * lambda j / 2)⁻¹ * G i j :=
      ((hasSum_geometric_of_norm_lt_one
        (completionRatioTwo_norm_lt_one lambda hlambda i j)).mul_right (G i j)).tsum_eq
    _ = completionR G lambda i j := by
      simp only [completionR, div_eq_mul_inv]
      ring

/-- Exact congruence identifying the manuscript's `P` with `gramian 4 C`. -/
theorem completionP_congruence_eq_gramian_four
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    Hinv * completionP G lambda * Hinv =
      gramian 4 (completionSimilarity H Hinv lambda) := by
  have hs : Summable (completionDiagonalGramianTerm 4 G lambda) :=
    summable_completionDiagonalGramianTerm hsqrt lambda hlambda (by norm_num)
  rw [← tsum_completionDiagonalGramianTerm_four_eq_completionP hsqrt lambda hlambda]
  calc
    Hinv * (∑' k : ℕ, completionDiagonalGramianTerm 4 G lambda k) * Hinv =
        ∑' k : ℕ, Hinv * completionDiagonalGramianTerm 4 G lambda k * Hinv := by
      rw [← hs.tsum_mul_left Hinv, ← (hs.mul_left Hinv).tsum_mul_right Hinv]
    _ = ∑' k : ℕ, gramianTerm 4 (completionSimilarity H Hinv lambda) k := by
      exact tsum_congr fun k ↦
        (gramianTerm_completionSimilarity_eq hsqrt lambda 4 k).symm
    _ = gramian 4 (completionSimilarity H Hinv lambda) := rfl

/-- Exact congruence identifying the manuscript's `R` with `gramian 2 C`. -/
theorem completionR_congruence_eq_gramian_two
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    Hinv * completionR G lambda * Hinv =
      gramian 2 (completionSimilarity H Hinv lambda) := by
  have hs : Summable (completionDiagonalGramianTerm 2 G lambda) :=
    summable_completionDiagonalGramianTerm hsqrt lambda hlambda (by norm_num)
  rw [← tsum_completionDiagonalGramianTerm_two_eq_completionR hsqrt lambda hlambda]
  calc
    Hinv * (∑' k : ℕ, completionDiagonalGramianTerm 2 G lambda k) * Hinv =
        ∑' k : ℕ, Hinv * completionDiagonalGramianTerm 2 G lambda k * Hinv := by
      rw [← hs.tsum_mul_left Hinv, ← (hs.mul_left Hinv).tsum_mul_right Hinv]
    _ = ∑' k : ℕ, gramianTerm 2 (completionSimilarity H Hinv lambda) k := by
      exact tsum_congr fun k ↦
        (gramianTerm_completionSimilarity_eq hsqrt lambda 2 k).symm
    _ = gramian 2 (completionSimilarity H Hinv lambda) := rfl

/-- Subtracting the preceding congruences gives the manuscript's identity for `X = R - P`. -/
theorem completionX_congruence_eq_gramian_difference
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    Hinv * completionX G lambda * Hinv =
      gramian 2 (completionSimilarity H Hinv lambda) -
        gramian 4 (completionSimilarity H Hinv lambda) := by
  rw [completionX, mul_sub, sub_mul,
    completionR_congruence_eq_gramian_two hsqrt lambda hlambda,
    completionP_congruence_eq_gramian_four hsqrt lambda hlambda]

/-- The square of `Hinv` is a left inverse of `G = H²`. -/
theorem completionSquareRoot_inverse_mul {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) :
    (Hinv * Hinv) * G = 1 := by
  rw [← hsqrt.hH_mul_H]
  calc
    (Hinv * Hinv) * (H * H) = Hinv * (Hinv * H) * H := by noncomm_ring
    _ = 1 := by
      rw [hsqrt.hHinv_mul_H]
      simp only [mul_one]
      exact hsqrt.hHinv_mul_H

/-- The square of `Hinv` is a right inverse of `G = H²`. -/
theorem completionSquareRoot_mul_inverse {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) :
    G * (Hinv * Hinv) = 1 := by
  rw [← hsqrt.hH_mul_H]
  calc
    (H * H) * (Hinv * Hinv) = H * (H * Hinv) * Hinv := by noncomm_ring
    _ = 1 := by
      rw [hsqrt.hH_mul_Hinv]
      simp only [mul_one]
      exact hsqrt.hH_mul_Hinv

/-- Thus the manuscript's matrix inverse `G⁻¹` is exactly `Hinv²`. -/
theorem completionGram_inverse_eq {G H Hinv : SquareMatrix n}
    (hsqrt : CompletionSquareRootData G H Hinv) :
    G⁻¹ = Hinv * Hinv :=
  Matrix.inv_eq_left_inv (completionSquareRoot_inverse_mul hsqrt)

/-- The purely algebraic identity behind congruencing manuscript equation (7) by `G⁻¹⁄²`. -/
theorem completion_congruence_identity (Hinv Ginv P X : SquareMatrix n)
    (hGinv : Ginv = Hinv * Hinv) :
    Hinv * (4 * X - X * Ginv * P - P * Ginv * X) * Hinv =
      4 * (Hinv * X * Hinv) -
        (Hinv * X * Hinv) * (Hinv * P * Hinv) -
          (Hinv * P * Hinv) * (Hinv * X * Hinv) := by
  rw [hGinv]
  noncomm_ring

/-- Exact Gramian form of the congruenced matrix in manuscript equation (10). -/
theorem completion_PRX_congruence_eq_gramian_expression
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    Hinv *
          (4 * completionX G lambda -
              completionX G lambda * G⁻¹ * completionP G lambda -
            completionP G lambda * G⁻¹ * completionX G lambda) *
        Hinv =
      4 * (gramian 2 (completionSimilarity H Hinv lambda) -
          gramian 4 (completionSimilarity H Hinv lambda)) -
        (gramian 2 (completionSimilarity H Hinv lambda) -
            gramian 4 (completionSimilarity H Hinv lambda)) *
          gramian 4 (completionSimilarity H Hinv lambda) -
        gramian 4 (completionSimilarity H Hinv lambda) *
          (gramian 2 (completionSimilarity H Hinv lambda) -
            gramian 4 (completionSimilarity H Hinv lambda)) := by
  rw [completion_congruence_identity Hinv G⁻¹ (completionP G lambda)
    (completionX G lambda) (completionGram_inverse_eq hsqrt)]
  rw [completionX_congruence_eq_gramian_difference hsqrt lambda hlambda,
    completionP_congruence_eq_gramian_four hsqrt lambda hlambda]

/-- The congruenced `X` is positive semidefinite, as asserted in manuscript equation (9). -/
theorem completionX_congruence_posSemidef [Nonempty n]
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    (Hinv * completionX G lambda * Hinv).PosSemidef := by
  rw [completionX_congruence_eq_gramian_difference hsqrt lambda hlambda]
  exact gramian_two_sub_gramian_four_posSemidef
    (mul_nonneg (norm_nonneg H) (norm_nonneg Hinv))
    (completionSimilarity H Hinv lambda)
    (completionSimilarity_pow_norm_le hsqrt lambda hlambda)

/-- Exact `k = 1, 2, ...` form of manuscript equation (9); the reindexing uses that the
`k = 0` difference summand vanishes. -/
theorem completionX_congruence_eq_tsum_succ
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1) :
    Hinv * completionX G lambda * Hinv =
      ∑' k : ℕ, gramianDifferenceTerm (completionSimilarity H Hinv lambda) (k + 1) := by
  let C := completionSimilarity H Hinv lambda
  let M := ‖H‖ * ‖Hinv‖
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg H) (norm_nonneg Hinv)
  have hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M :=
    completionSimilarity_pow_norm_le hsqrt lambda hlambda
  have hs : Summable (gramianDifferenceTerm C) :=
    (summable_gramianTerm (q := 2) (by norm_num) hM C hbound).sub
      (summable_gramianTerm (q := 4) (by norm_num) hM C hbound)
  rw [completionX_congruence_eq_gramian_difference hsqrt lambda hlambda]
  rw [gramian_two_sub_gramian_four_eq_tsum hM C hbound]
  calc
    ∑' k : ℕ, gramianDifferenceTerm C k =
        gramianDifferenceTerm C 0 + ∑' k : ℕ, gramianDifferenceTerm C (k + 1) :=
      hs.tsum_eq_zero_add
    _ = ∑' k : ℕ, gramianDifferenceTerm C (k + 1) := by
      rw [gramianDifferenceTerm_zero, zero_add]

/-- Positivity is preserved when manuscript equation (7) is congruenced by the self-adjoint
matrix `Hinv = G⁻¹⁄²`, yielding the Gramian form of equation (10). -/
theorem completion_gramian_expression_posSemidef_of_source
    {G H Hinv : SquareMatrix n} (hsqrt : CompletionSquareRootData G H Hinv)
    (lambda : n → ℂ) (hlambda : ∀ i, ‖lambda i‖ ≤ 1)
    (hsource :
      (4 * completionX G lambda -
          completionX G lambda * G⁻¹ * completionP G lambda -
        completionP G lambda * G⁻¹ * completionX G lambda).PosSemidef) :
    (4 * (gramian 2 (completionSimilarity H Hinv lambda) -
          gramian 4 (completionSimilarity H Hinv lambda)) -
        (gramian 2 (completionSimilarity H Hinv lambda) -
            gramian 4 (completionSimilarity H Hinv lambda)) *
          gramian 4 (completionSimilarity H Hinv lambda) -
        gramian 4 (completionSimilarity H Hinv lambda) *
          (gramian 2 (completionSimilarity H Hinv lambda) -
            gramian 4 (completionSimilarity H Hinv lambda))).PosSemidef := by
  have hcongr := hsource.conjTranspose_mul_mul_same Hinv
  rw [hsqrt.hHinv_selfAdjoint] at hcongr
  rw [completion_PRX_congruence_eq_gramian_expression hsqrt lambda hlambda] at hcongr
  exact hcongr

end CrouzeixConjecture
