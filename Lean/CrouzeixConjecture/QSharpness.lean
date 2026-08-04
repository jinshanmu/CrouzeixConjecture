module

public import CrouzeixConjecture.QRangeDisks
public import CrouzeixConjecture.QScaledRational

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- The `2 × 2` square-zero Jordan block used in the sharpness example. -/
def jordanNilpotentTwo : SquareMatrix (Fin 2) :=
  !![0, 1; 0, 0]

@[simp]
theorem jordanNilpotentTwo_apply (x : EuclideanVector (Fin 2)) :
    euclideanOperator jordanNilpotentTwo x =
      WithLp.toLp 2 ![x 1, 0] := by
  ext i
  fin_cases i
  · simp [euclideanOperator, jordanNilpotentTwo]
    rfl
  · simp [euclideanOperator, jordanNilpotentTwo]

theorem euclideanVector_finTwo_norm_sq (x : EuclideanVector (Fin 2)) :
    ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.norm_sq_eq x

theorem norm_jordanNilpotentTwo_apply (x : EuclideanVector (Fin 2)) :
    ‖euclideanOperator jordanNilpotentTwo x‖ = ‖x 1‖ := by
  rw [jordanNilpotentTwo_apply, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two, Real.sqrt_sq (norm_nonneg (x 1))]

theorem inner_jordanNilpotentTwo (x : EuclideanVector (Fin 2)) :
    ⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ = conj (x 0) * x 1 := by
  rw [jordanNilpotentTwo_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

theorem qResidual_jordanNilpotentTwo {x : EuclideanVector (Fin 2)}
    (hx : ‖x‖ = 1) :
    qResidual jordanNilpotentTwo x = ‖x 1‖ ^ 2 := by
  have hcoords : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    rw [← euclideanVector_finTwo_norm_sq, hx]
    norm_num
  have hsq : qResidualSq jordanNilpotentTwo x = (‖x 1‖ ^ 2) ^ 2 := by
    rw [qResidualSq, norm_jordanNilpotentTwo_apply,
      inner_jordanNilpotentTwo, norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg ‖x 0‖, sq_nonneg ‖x 1‖]
  rw [qResidual, hsq, Real.sqrt_sq (sq_nonneg ‖x 1‖)]

theorem norm_jordanNilpotentTwo : ‖jordanNilpotentTwo‖ = 1 := by
  rw [matrix_norm_eq_euclidean_operator_norm]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [one_mul, norm_jordanNilpotentTwo_apply]
    exact PiLp.norm_apply_le x 1
  · let e1 : EuclideanVector (Fin 2) := EuclideanSpace.single 1 1
    have he1 : ‖e1‖ = 1 := by simp [e1]
    have hJe1 : ‖euclideanOperator jordanNilpotentTwo e1‖ = 1 := by
      rw [norm_jordanNilpotentTwo_apply]
      simp [e1]
    calc
      1 = ‖euclideanOperator jordanNilpotentTwo e1‖ := hJe1.symm
      _ ≤ ‖euclideanOperator jordanNilpotentTwo‖ * ‖e1‖ :=
        (euclideanOperator jordanNilpotentTwo).le_opNorm e1
      _ = ‖euclideanOperator jordanNilpotentTwo‖ := by rw [he1, mul_one]

/-- The disk-radius coefficient in terms of the similarity parameter. -/
theorem qTau_div_eq_qKappa_expression {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    qTau r / r = (qKappa r ^ 2 - 1) / (2 * qKappa r) := by
  have htauSq := qTau_sq hr1 hr0.le
  have hrne : r ≠ 0 := ne_of_gt hr0
  have htone : 1 + qTau r ≠ 0 := by
    linarith [qTau_nonneg r]
  rw [qKappa]
  field_simp [hrne, htone]
  nlinarith [qTau_nonneg r]

/-- Each Tsing disk for the Jordan block lies in the closed disk of radius `κ(r) / 2`. -/
theorem jordanNilpotentTwo_center_add_radius_le
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {x : EuclideanVector (Fin 2)} (hx : ‖x‖ = 1) :
    ‖⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ +
        (qTau r / r) * qResidual jordanNilpotentTwo x ≤
      qKappa r / 2 := by
  let u : ℝ := ‖x 0‖
  let v : ℝ := ‖x 1‖
  let k : ℝ := qKappa r
  have huv : u ^ 2 + v ^ 2 = 1 := by
    simpa only [u, v] using (show ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 by
      rw [← euclideanVector_finTwo_norm_sq, hx]
      norm_num)
  have hcenter : ‖⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ = u * v := by
    rw [inner_jordanNilpotentTwo, norm_mul, Complex.norm_conj]
  have hresidual : qResidual jordanNilpotentTwo x = v ^ 2 := by
    simpa only [v] using qResidual_jordanNilpotentTwo hx
  have hcoefficient : qTau r / r = (k ^ 2 - 1) / (2 * k) := by
    simpa only [k] using qTau_div_eq_qKappa_expression hr0 hr1
  have hk0 : 0 < k := by simpa only [k] using qKappa_pos hr0
  have halgebra :
      k / 2 - (u * v + ((k ^ 2 - 1) / (2 * k)) * v ^ 2) =
        (k * u - v) ^ 2 / (2 * k) := by
    field_simp [ne_of_gt hk0]
    nlinarith
  have hnonneg : 0 ≤ (k * u - v) ^ 2 / (2 * k) := by positivity
  rw [hcenter, hresidual, hcoefficient]
  linarith

/-- Every point of the scaled `q`-range of the Jordan block has modulus at most `κ(r) / 2`. -/
theorem norm_le_qKappa_half_of_mem_scaledQNumericalRange_jordanNilpotentTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {z : ℂ}
    (hz : z ∈ scaledQNumericalRange (r : ℂ) jordanNilpotentTwo) :
    ‖z‖ ≤ qKappa r / 2 := by
  rw [scaledQNumericalRange_eq_qDiskUnion hr0 hr1 jordanNilpotentTwo] at hz
  obtain ⟨x, hx, hzDisk⟩ := hz
  calc
    ‖z‖ = ‖(z - ⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ) +
        ⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ := by simp
    _ ≤ ‖z - ⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ +
        ‖⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ := norm_add_le _ _
    _ ≤ (qTau r / r) * qResidual jordanNilpotentTwo x +
        ‖⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ :=
      add_le_add hzDisk le_rfl
    _ = ‖⟪x, euclideanOperator jordanNilpotentTwo x⟫_ℂ‖ +
        (qTau r / r) * qResidual jordanNilpotentTwo x := add_comm _ _
    _ ≤ qKappa r / 2 :=
      jordanNilpotentTwo_center_add_radius_le hr0 hr1 hx

/-- Normalizing denominator for the unit vector at which the Jordan disk bound is sharp. -/
def jordanMaximizingDenominator (r : ℝ) : ℝ :=
  √(qKappa r ^ 2 + 1)

/-- A unit vector whose coordinate-norm ratio is `κ(r)`. -/
def jordanMaximizingUnitVector (r : ℝ) : EuclideanVector (Fin 2) :=
  WithLp.toLp 2
    ![((jordanMaximizingDenominator r)⁻¹ : ℂ),
      ((qKappa r / jordanMaximizingDenominator r : ℝ) : ℂ)]

theorem jordanMaximizingDenominator_pos (r : ℝ) :
    0 < jordanMaximizingDenominator r := by
  rw [jordanMaximizingDenominator]
  exact Real.sqrt_pos.2 (by positivity)

theorem jordanMaximizingDenominator_sq (r : ℝ) :
    jordanMaximizingDenominator r ^ 2 = qKappa r ^ 2 + 1 := by
  rw [jordanMaximizingDenominator, Real.sq_sqrt]
  positivity

theorem norm_jordanMaximizingUnitVector {r : ℝ} (hr0 : 0 < r) :
    ‖jordanMaximizingUnitVector r‖ = 1 := by
  let d : ℝ := jordanMaximizingDenominator r
  let k : ℝ := qKappa r
  have hd0 : 0 < d := by simpa only [d] using jordanMaximizingDenominator_pos r
  have hk0 : 0 < k := by simpa only [k] using qKappa_pos hr0
  have hdsq : d ^ 2 = k ^ 2 + 1 := by
    simpa only [d, k] using jordanMaximizingDenominator_sq r
  have hnormSq : ‖jordanMaximizingUnitVector r‖ ^ 2 = 1 := by
    rw [euclideanVector_finTwo_norm_sq]
    change ‖((d : ℂ))⁻¹‖ ^ 2 + ‖((k / d : ℝ) : ℂ)‖ ^ 2 = 1
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hd0, abs_of_pos (div_pos hk0 hd0)]
    field_simp [ne_of_gt hd0]
    nlinarith
  nlinarith [norm_nonneg (jordanMaximizingUnitVector r)]

theorem inner_jordanMaximizingUnitVector (r : ℝ) :
    ⟪jordanMaximizingUnitVector r,
        euclideanOperator jordanNilpotentTwo (jordanMaximizingUnitVector r)⟫_ℂ =
      ((qKappa r / jordanMaximizingDenominator r ^ 2 : ℝ) : ℂ) := by
  let d : ℝ := jordanMaximizingDenominator r
  let k : ℝ := qKappa r
  have hd0 : d ≠ 0 := by
    exact ne_of_gt (by simpa only [d] using jordanMaximizingDenominator_pos r)
  rw [inner_jordanNilpotentTwo]
  simp only [jordanMaximizingUnitVector, Matrix.cons_val_zero, Matrix.cons_val_one]
  change conj (((jordanMaximizingDenominator r : ℝ) : ℂ)⁻¹) *
      (((qKappa r / jordanMaximizingDenominator r : ℝ) : ℂ)) =
    (((qKappa r / jordanMaximizingDenominator r ^ 2 : ℝ) : ℂ))
  rw [map_inv₀, Complex.conj_ofReal]
  norm_cast
  field_simp

theorem residual_jordanMaximizingUnitVector {r : ℝ} (hr0 : 0 < r) :
    qResidual jordanNilpotentTwo (jordanMaximizingUnitVector r) =
      (qKappa r / jordanMaximizingDenominator r) ^ 2 := by
  let d : ℝ := jordanMaximizingDenominator r
  let k : ℝ := qKappa r
  have hd0 : 0 < d := by simpa only [d] using jordanMaximizingDenominator_pos r
  have hk0 : 0 < k := by simpa only [k] using qKappa_pos hr0
  rw [qResidual_jordanNilpotentTwo (norm_jordanMaximizingUnitVector hr0)]
  change ‖((k / d : ℝ) : ℂ)‖ ^ 2 = (k / d) ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hk0 hd0)]

/-- The positive real boundary point `κ(r) / 2` belongs to the scaled range of the
Jordan block. -/
theorem qKappa_half_mem_scaledQNumericalRange_jordanNilpotentTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((qKappa r / 2 : ℝ) : ℂ) ∈
      scaledQNumericalRange (r : ℂ) jordanNilpotentTwo := by
  let d : ℝ := jordanMaximizingDenominator r
  let k : ℝ := qKappa r
  have hd0 : 0 < d := by simpa only [d] using jordanMaximizingDenominator_pos r
  have hk0 : 0 < k := by simpa only [k] using qKappa_pos hr0
  have hk1 : 1 ≤ k := by simpa only [k] using one_le_qKappa hr0 hr1
  have hdsq : d ^ 2 = k ^ 2 + 1 := by
    simpa only [d, k] using jordanMaximizingDenominator_sq r
  have hinner :
      ⟪jordanMaximizingUnitVector r,
          euclideanOperator jordanNilpotentTwo (jordanMaximizingUnitVector r)⟫_ℂ =
        ((k / d ^ 2 : ℝ) : ℂ) := by
    simpa only [k, d] using inner_jordanMaximizingUnitVector r
  have hresidual :
      qResidual jordanNilpotentTwo (jordanMaximizingUnitVector r) =
        (k / d) ^ 2 := by
    simpa only [k, d] using residual_jordanMaximizingUnitVector hr0
  have hcoefficient : qTau r / r = (k ^ 2 - 1) / (2 * k) := by
    simpa only [k] using qTau_div_eq_qKappa_expression hr0 hr1
  have hleft0 : 0 ≤ k / 2 - k / d ^ 2 := by
    have hleftform :
        k / 2 - k / d ^ 2 = k * (k ^ 2 - 1) / (2 * d ^ 2) := by
      field_simp [ne_of_gt hd0]
      nlinarith
    rw [hleftform]
    exact div_nonneg
      (mul_nonneg hk0.le (by nlinarith [sq_nonneg k])) (by positivity)
  have halgebra :
      k / 2 - k / d ^ 2 =
        ((k ^ 2 - 1) / (2 * k)) * (k / d) ^ 2 := by
    field_simp [ne_of_gt hd0, ne_of_gt hk0]
    nlinarith
  apply qDisk_boundary_mem_scaledQNumericalRange hr0 hr1 jordanNilpotentTwo
    (norm_jordanMaximizingUnitVector hr0)
  rw [hinner, hresidual, hcoefficient]
  calc
    ‖((k / 2 : ℝ) : ℂ) - ((k / d ^ 2 : ℝ) : ℂ)‖ =
        |k / 2 - k / d ^ 2| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = k / 2 - k / d ^ 2 := abs_of_nonneg hleft0
    _ = ((k ^ 2 - 1) / (2 * k)) * (k / d) ^ 2 := halgebra

/-- Exact maximum modulus of the identity polynomial on the scaled range of the Jordan block. -/
theorem maxPolynomialModulusOnScaledQNumericalRange_X_jordanNilpotentTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    maxPolynomialModulusOnScaledQNumericalRange (r : ℂ)
        jordanNilpotentTwo Polynomial.X = qKappa r / 2 := by
  have hrNorm : ‖(r : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hne :
      (scaledQNumericalRange (r : ℂ) jordanNilpotentTwo).Nonempty :=
    scaledQNumericalRange_nonempty hrNorm jordanNilpotentTwo
  obtain ⟨z, hz, hmax⟩ :=
    exists_maxPolynomialModulusOnScaledQNumericalRange
      (r : ℂ) jordanNilpotentTwo Polynomial.X hne
  apply le_antisymm
  · rw [← hmax]
    simpa using
      norm_le_qKappa_half_of_mem_scaledQNumericalRange_jordanNilpotentTwo
        hr0 hr1 hz
  · have hpoint :=
      norm_polynomial_eval_le_maxOnScaledQNumericalRange
        (r : ℂ) jordanNilpotentTwo Polynomial.X hne
        (qKappa_half_mem_scaledQNumericalRange_jordanNilpotentTwo hr0 hr1)
    rw [Polynomial.eval_X, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (qKappa_pos hr0) (by norm_num))] at hpoint
    exact hpoint

/-- The same exact maximum after regarding `X` as a rational function. -/
theorem maxRationalModulusOnScaledQNumericalRange_X_jordanNilpotentTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    maxRationalModulusOnScaledQNumericalRange (r : ℂ) jordanNilpotentTwo
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) =
      qKappa r / 2 := by
  rw [maxRationalModulusOnScaledQNumericalRange_algebraMap_polynomial,
    maxPolynomialModulusOnScaledQNumericalRange_X_jordanNilpotentTwo hr0 hr1]

/-- The identity polynomial evaluates to the Jordan block and hence has matrix norm one. -/
theorem norm_polynomialEval_X_jordanNilpotentTwo :
    ‖polynomialEval Polynomial.X jordanNilpotentTwo‖ = 1 := by
  simpa [polynomialEval] using norm_jordanNilpotentTwo

/-- The rational image of `X` likewise has matrix norm one. -/
theorem norm_rationalMatrixEval_X_jordanNilpotentTwo :
    ‖rationalMatrixEval
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
        jordanNilpotentTwo‖ = 1 := by
  rw [rationalMatrixEval_algebraMap_polynomial,
    norm_polynomialEval_X_jordanNilpotentTwo]

/-- A constant polynomial has maximum modulus one on every nonempty scaled range. -/
theorem maxPolynomialModulusOnScaledQNumericalRange_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℂ) (A : SquareMatrix n)
    (hne : (scaledQNumericalRange q A).Nonempty) :
    maxPolynomialModulusOnScaledQNumericalRange q A (1 : Polynomial ℂ) = 1 := by
  obtain ⟨z, hz, hmax⟩ :=
    exists_maxPolynomialModulusOnScaledQNumericalRange
      q A (1 : Polynomial ℂ) hne
  simpa using hmax.symm

/-- Rationalizing the constant polynomial preserves the exact maximum one. -/
theorem maxRationalModulusOnScaledQNumericalRange_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℂ) (A : SquareMatrix n)
    (hne : (scaledQNumericalRange q A).Nonempty) :
    maxRationalModulusOnScaledQNumericalRange q A
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 : Polynomial ℂ)) = 1 := by
  rw [maxRationalModulusOnScaledQNumericalRange_algebraMap_polynomial,
    maxPolynomialModulusOnScaledQNumericalRange_one q A hne]

theorem norm_polynomialEval_one_jordanNilpotentTwo :
    ‖polynomialEval (1 : Polynomial ℂ) jordanNilpotentTwo‖ = 1 := by
  simp [polynomialEval]

theorem norm_rationalMatrixEval_one_jordanNilpotentTwo :
    ‖rationalMatrixEval
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 : Polynomial ℂ))
        jordanNilpotentTwo‖ = 1 := by
  rw [rationalMatrixEval_algebraMap_polynomial,
    norm_polynomialEval_one_jordanNilpotentTwo]

/-- A candidate constant required to control all polynomial tests on `2 × 2` matrices. -/
def PolynomialScaledQBoundOnFinTwo (r K : ℝ) : Prop :=
  ∀ (A : SquareMatrix (Fin 2)) (p : Polynomial ℂ),
    ‖polynomialEval p A‖ ≤
      K * maxPolynomialModulusOnScaledQNumericalRange (r : ℂ) A p

/-- A candidate rational spectral constant on all `2 × 2` matrices. -/
def RationalScaledQBoundOnFinTwo (r K : ℝ) : Prop :=
  ∀ (A : SquareMatrix (Fin 2)) (f : RatFunc ℂ),
    RationalPoleFreeOn f (scaledQNumericalRange (r : ℂ) A) →
      ‖rationalMatrixEval f A‖ ≤
        K * maxRationalModulusOnScaledQNumericalRange (r : ℂ) A f

/-- Every rational candidate supplies its polynomial specialization. -/
theorem polynomialScaledQBoundOnFinTwo_of_rational
    {r K : ℝ} (hK : RationalScaledQBoundOnFinTwo r K) :
    PolynomialScaledQBoundOnFinTwo r K := by
  intro A p
  have hbound :=
    hK A (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      (rationalPoleFreeOn_algebraMap_polynomial p
        (scaledQNumericalRange (r : ℂ) A))
  rw [rationalMatrixEval_algebraMap_polynomial,
    maxRationalModulusOnScaledQNumericalRange_algebraMap_polynomial] at hbound
  exact hbound

/-- Constant polynomials force the universal lower branch `1`. -/
theorem one_le_of_polynomialScaledQBoundOnFinTwo
    {r K : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hK : PolynomialScaledQBoundOnFinTwo r K) :
    1 ≤ K := by
  have hrNorm : ‖(r : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hne :
      (scaledQNumericalRange (r : ℂ) jordanNilpotentTwo).Nonempty :=
    scaledQNumericalRange_nonempty hrNorm jordanNilpotentTwo
  have hbound := hK jordanNilpotentTwo (1 : Polynomial ℂ)
  rw [norm_polynomialEval_one_jordanNilpotentTwo,
    maxPolynomialModulusOnScaledQNumericalRange_one
      (r : ℂ) jordanNilpotentTwo hne, mul_one] at hbound
  exact hbound

/-- The identity polynomial on the Jordan block forces the lower branch `2 / κ(r)`. -/
theorem two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo
    {r K : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hK : PolynomialScaledQBoundOnFinTwo r K) :
    2 / qKappa r ≤ K := by
  have hbound := hK jordanNilpotentTwo Polynomial.X
  rw [norm_polynomialEval_X_jordanNilpotentTwo,
    maxPolynomialModulusOnScaledQNumericalRange_X_jordanNilpotentTwo hr0 hr1]
    at hbound
  apply (div_le_iff₀ (qKappa_pos hr0)).2
  nlinarith

/-- Any polynomial constant valid even just in dimension two dominates both sharpness
branches. -/
theorem max_one_two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo
    {r K : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hK : PolynomialScaledQBoundOnFinTwo r K) :
    max 1 (2 / qKappa r) ≤ K := by
  exact max_le
    (one_le_of_polynomialScaledQBoundOnFinTwo hr0 hr1 hK)
    (two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo hr0 hr1 hK)

/-- Consequently, every rational spectral constant valid in dimension two dominates the
manuscript's two-branch candidate. -/
theorem max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo
    {r K : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hK : RationalScaledQBoundOnFinTwo r K) :
    max 1 (2 / qKappa r) ≤ K :=
  max_one_two_div_qKappa_le_of_polynomialScaledQBoundOnFinTwo
    hr0 hr1 (polynomialScaledQBoundOnFinTwo_of_rational hK)

/-- Set-theoretic form: the two-branch candidate is a lower bound for every admissible
dimension-two rational spectral constant. -/
theorem max_one_two_div_qKappa_isLowerBound_rationalScaledQBoundOnFinTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    max 1 (2 / qKappa r) ∈
      lowerBounds {K : ℝ | RationalScaledQBoundOnFinTwo r K} := by
  intro K hK
  exact max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo
    hr0 hr1 hK

end CrouzeixConjecture
