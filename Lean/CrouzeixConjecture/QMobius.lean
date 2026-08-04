module

public import CrouzeixConjecture.DoubleLayerCayley
public import CrouzeixConjecture.RationalFunctionalCalculus

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The denominator of the rotated real disk automorphism
`z ↦ (ω z - a) / (1 - a ω z)` evaluated at a matrix. -/
def rotatedRealMobiusDenominator
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) : SquareMatrix n :=
  1 - ((a : ℂ) * ω) • X

/-- The numerator of the rotated real disk automorphism
`z ↦ (ω z - a) / (1 - a ω z)` evaluated at a matrix. -/
def rotatedRealMobiusNumerator
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) : SquareMatrix n :=
  ω • X - (a : ℂ) • 1

/-- The matrix evaluation of the rotated real disk automorphism used in the
similarity-orbit extraction argument.  Only `‖ω‖ = 1` and `0 ≤ a < 1` are needed
in that argument. -/
def rotatedRealMobiusEval
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) : SquareMatrix n :=
  rotatedRealMobiusNumerator ω a X * (rotatedRealMobiusDenominator ω a X)⁻¹

/-- The scalar multiplying `X` in the Möbius denominator lies in the open
unit disk when `‖ω‖ = 1` and `0 ≤ a < 1`. -/
theorem mul_mem_unitDisk_of_norm_eq_one
    {ω : ℂ} {a : ℝ} (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (a : ℂ) * ω ∈ unitDisk := by
  rw [unitDisk, Metric.mem_ball, dist_zero_right, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, hω, mul_one]
  exact ha1

/-- A closed-unit-disk spectral hypothesis makes the denominator of every
rotated real disk automorphism invertible. -/
theorem isUnit_rotatedRealMobiusDenominator
    [Nonempty n] (X : SquareMatrix n) (hspectrum : matrixSpectrum X ⊆ closedUnitDisk)
    {ω : ℂ} {a : ℝ} (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    IsUnit (rotatedRealMobiusDenominator ω a X) := by
  exact isUnit_one_sub_smul_of_spectrum_subset_closedUnitDisk X hspectrum
    (mul_mem_unitDisk_of_norm_eq_one hω ha0 ha1)

/-- Multiplication by the Möbius denominator recovers its numerator. -/
theorem rotatedRealMobiusEval_mul_denominator
    (X : SquareMatrix n) {ω : ℂ} {a : ℝ}
    (hunit : IsUnit (rotatedRealMobiusDenominator ω a X)) :
    rotatedRealMobiusEval ω a X * rotatedRealMobiusDenominator ω a X =
      rotatedRealMobiusNumerator ω a X := by
  have hdet : IsUnit (rotatedRealMobiusDenominator ω a X).det :=
    (rotatedRealMobiusDenominator ω a X).isUnit_iff_isUnit_det.mp hunit
  exact (rotatedRealMobiusDenominator ω a X).nonsing_inv_mul_cancel_right
    (rotatedRealMobiusNumerator ω a X) hdet

/-- Operator form of the cancellation identity.  This is the exact interface
used in extraction: if `u = (I-aωX)x`, then the Möbius transform sends `u`
to `(ωX-aI)x`. -/
theorem euclideanOperator_rotatedRealMobiusEval_apply_denominator
    (X : SquareMatrix n) {ω : ℂ} {a : ℝ}
    (hunit : IsUnit (rotatedRealMobiusDenominator ω a X))
    (x : EuclideanVector n) :
    euclideanOperator (rotatedRealMobiusEval ω a X)
        (euclideanOperator (rotatedRealMobiusDenominator ω a X) x) =
      euclideanOperator (rotatedRealMobiusNumerator ω a X) x := by
  have hmatrix := rotatedRealMobiusEval_mul_denominator X hunit
  have happly := congrArg (fun T : SquareMatrix n ↦ euclideanOperator T x) hmatrix
  simpa only [map_mul, ContinuousLinearMap.mul_apply] using happly

/-- Polynomial numerator of the same scalar Möbius transformation. -/
def rotatedRealMobiusNumeratorPolynomial (ω : ℂ) (a : ℝ) : Polynomial ℂ :=
  Polynomial.C ω * Polynomial.X - Polynomial.C (a : ℂ)

/-- Polynomial denominator of the same scalar Möbius transformation. -/
def rotatedRealMobiusDenominatorPolynomial (ω : ℂ) (a : ℝ) : Polynomial ℂ :=
  1 - Polynomial.C ((a : ℂ) * ω) * Polynomial.X

/-- The rotated real disk automorphism as an actual reduced rational-function
value.  Its displayed numerator and denominator are kept separately above so
that scalar and matrix evaluation stay inside the rational functional calculus. -/
def rotatedRealMobiusRatFunc (ω : ℂ) (a : ℝ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (rotatedRealMobiusNumeratorPolynomial ω a) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (rotatedRealMobiusDenominatorPolynomial ω a)

@[simp]
theorem eval_rotatedRealMobiusNumeratorPolynomial (ω : ℂ) (a : ℝ) (z : ℂ) :
    Polynomial.eval z (rotatedRealMobiusNumeratorPolynomial ω a) = ω * z - a := by
  simp [rotatedRealMobiusNumeratorPolynomial]

@[simp]
theorem eval_rotatedRealMobiusDenominatorPolynomial (ω : ℂ) (a : ℝ) (z : ℂ) :
    Polynomial.eval z (rotatedRealMobiusDenominatorPolynomial ω a) =
      1 - ((a : ℂ) * ω) * z := by
  simp [rotatedRealMobiusDenominatorPolynomial]

theorem rotatedRealMobiusDenominatorPolynomial_ne_zero (ω : ℂ) (a : ℝ) :
    rotatedRealMobiusDenominatorPolynomial ω a ≠ 0 := by
  intro hzero
  have h := congrArg (Polynomial.eval (0 : ℂ)) hzero
  simp at h

/-- The displayed scalar denominator cannot vanish on the closed unit disk. -/
theorem eval_rotatedRealMobiusDenominatorPolynomial_ne_zero
    {z ω : ℂ} {a : ℝ} (hz : z ∈ closedUnitDisk)
    (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Polynomial.eval z (rotatedRealMobiusDenominatorPolynomial ω a) ≠ 0 := by
  rw [eval_rotatedRealMobiusDenominatorPolynomial]
  intro hzero
  have hproduct : ((a : ℂ) * ω) * z = 1 := (sub_eq_zero.mp hzero).symm
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using hz
  have hnorm : 1 = a * ‖z‖ := by
    calc
      1 = ‖(1 : ℂ)‖ := by simp
      _ = ‖((a : ℂ) * ω) * z‖ := by rw [hproduct]
      _ = ‖(a : ℂ)‖ * ‖ω‖ * ‖z‖ := by rw [norm_mul, norm_mul]
      _ = a * ‖z‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, hω, mul_one]
  have hamul : a * ‖z‖ ≤ a := by
    nlinarith [norm_nonneg z]
  linarith

/-- The rational Möbius function has no pole on the closed unit disk. -/
theorem rationalPoleFreeOn_rotatedRealMobiusRatFunc_closedUnitDisk
    {ω : ℂ} {a : ℝ} (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    RationalPoleFreeOn (rotatedRealMobiusRatFunc ω a) closedUnitDisk := by
  rw [rationalPoleFreeOn_iff]
  intro z hz hcanonical
  let p := rotatedRealMobiusNumeratorPolynomial ω a
  let d := rotatedRealMobiusDenominatorPolynomial ω a
  have hdvd : (rotatedRealMobiusRatFunc ω a).denom ∣ d := by
    dsimp only [rotatedRealMobiusRatFunc, p, d]
    exact RatFunc.denom_div_dvd _ _
  obtain ⟨g, hg⟩ := hdvd
  have hexplicit : Polynomial.eval z d ≠ 0 := by
    exact eval_rotatedRealMobiusDenominatorPolynomial_ne_zero hz hω ha0 ha1
  apply hexplicit
  rw [hg, Polynomial.eval_mul, hcanonical, zero_mul]

/-- Scalar evaluation of the rational-function presentation agrees with the
displayed Möbius quotient throughout the closed unit disk. -/
theorem rationalScalarEval_rotatedRealMobiusRatFunc
    {z ω : ℂ} {a : ℝ} (hz : z ∈ closedUnitDisk)
    (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    rationalScalarEval (rotatedRealMobiusRatFunc ω a) z =
      (ω * z - a) / (1 - ((a : ℂ) * ω) * z) := by
  let p := rotatedRealMobiusNumeratorPolynomial ω a
  let d := rotatedRealMobiusDenominatorPolynomial ω a
  let h := rotatedRealMobiusRatFunc ω a
  have hd : d ≠ 0 := rotatedRealMobiusDenominatorPolynomial_ne_zero ω a
  have hcanonical : Polynomial.eval z h.denom ≠ 0 :=
    (rationalPoleFreeOn_iff h closedUnitDisk).mp
      (rationalPoleFreeOn_rotatedRealMobiusRatFunc_closedUnitDisk hω ha0 ha1) z hz
  have hexplicit : Polynomial.eval z d ≠ 0 :=
    eval_rotatedRealMobiusDenominatorPolynomial_ne_zero hz hω ha0 ha1
  have hcrossPolynomial : h.num * d = p * h.denom := by
    apply (RatFunc.num_mul_eq_mul_denom_iff hd).mpr
    rfl
  have hcross := congrArg (Polynomial.eval z) hcrossPolynomial
  simp only [Polynomial.eval_mul] at hcross
  change Polynomial.eval z h.num / Polynomial.eval z h.denom = _
  rw [show ω * z - a = Polynomial.eval z p by
      simp [p],
    show 1 - ((a : ℂ) * ω) * z = Polynomial.eval z d by
      simp [d]]
  exact (div_eq_div_iff hcanonical hexplicit).mpr hcross

/-- A rotated real Möbius map sends the closed unit disk into itself. -/
theorem norm_rotatedRealMobius_le_one
    {z ω : ℂ} {a : ℝ} (hz : z ∈ closedUnitDisk)
    (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ‖(ω * z - a) / (1 - ((a : ℂ) * ω) * z)‖ ≤ 1 := by
  let w : ℂ := ω * z
  have hzNorm : ‖z‖ ≤ 1 := by
    simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using hz
  have hwNorm : ‖w‖ ≤ 1 := by
    dsimp only [w]
    rw [norm_mul, hω, one_mul]
    exact hzNorm
  have haSq : a ^ 2 ≤ 1 := by nlinarith
  have hwSq : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
  have hidentity :
      ‖w - (a : ℂ)‖ ^ 2 + (1 - a ^ 2) * (1 - ‖w‖ ^ 2) =
        ‖1 - (a : ℂ) * w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.one_re,
      Complex.mul_re, Complex.one_im, zero_sub, Complex.mul_im,
      zero_mul, add_zero]
    ring
  have hsquares : ‖w - (a : ℂ)‖ ^ 2 ≤ ‖1 - (a : ℂ) * w‖ ^ 2 := by
    nlinarith
  have hnorms : ‖w - (a : ℂ)‖ ≤ ‖1 - (a : ℂ) * w‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  have hden : 1 - ((a : ℂ) * ω) * z ≠ 0 := by
    simpa using eval_rotatedRealMobiusDenominatorPolynomial_ne_zero hz hω ha0 ha1
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hden)).mpr
  simpa only [w, one_mul, mul_assoc] using hnorms

theorem norm_rationalScalarEval_rotatedRealMobiusRatFunc_le_one
    {z ω : ℂ} {a : ℝ} (hz : z ∈ closedUnitDisk)
    (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ‖rationalScalarEval (rotatedRealMobiusRatFunc ω a) z‖ ≤ 1 := by
  rw [rationalScalarEval_rotatedRealMobiusRatFunc hz hω ha0 ha1]
  exact norm_rotatedRealMobius_le_one hz hω ha0 ha1

@[simp]
theorem polynomialEval_rotatedRealMobiusNumeratorPolynomial
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) :
    polynomialEval (rotatedRealMobiusNumeratorPolynomial ω a) X =
      rotatedRealMobiusNumerator ω a X := by
  simp [polynomialEval, rotatedRealMobiusNumeratorPolynomial,
    rotatedRealMobiusNumerator, Algebra.smul_def]

@[simp]
theorem polynomialEval_rotatedRealMobiusDenominatorPolynomial
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) :
    polynomialEval (rotatedRealMobiusDenominatorPolynomial ω a) X =
      rotatedRealMobiusDenominator ω a X := by
  simp [polynomialEval, rotatedRealMobiusDenominatorPolynomial,
    rotatedRealMobiusDenominator, Algebra.smul_def]

/-- The Möbius numerator and denominator commute because both are polynomial
expressions in the same matrix. -/
theorem rotatedRealMobiusDenominator_commutes_numerator
    (ω : ℂ) (a : ℝ) (X : SquareMatrix n) :
    rotatedRealMobiusDenominator ω a X * rotatedRealMobiusNumerator ω a X =
      rotatedRealMobiusNumerator ω a X * rotatedRealMobiusDenominator ω a X := by
  rw [← polynomialEval_rotatedRealMobiusDenominatorPolynomial,
    ← polynomialEval_rotatedRealMobiusNumeratorPolynomial]
  simp only [polynomialEval, ← map_mul]
  rw [mul_comm]

/-- The cancellation identity with the denominator on the left. -/
theorem denominator_mul_rotatedRealMobiusEval
    (X : SquareMatrix n) {ω : ℂ} {a : ℝ}
    (hunit : IsUnit (rotatedRealMobiusDenominator ω a X)) :
    rotatedRealMobiusDenominator ω a X * rotatedRealMobiusEval ω a X =
      rotatedRealMobiusNumerator ω a X := by
  have hdet : IsUnit (rotatedRealMobiusDenominator ω a X).det :=
    (rotatedRealMobiusDenominator ω a X).isUnit_iff_isUnit_det.mp hunit
  rw [rotatedRealMobiusEval, ← Matrix.mul_assoc,
    rotatedRealMobiusDenominator_commutes_numerator]
  exact (rotatedRealMobiusDenominator ω a X).mul_nonsing_inv_cancel_right
    (rotatedRealMobiusNumerator ω a X) hdet

/-- Pole-freeness on any set containing the matrix spectrum makes the reduced
rational denominator invertible at the matrix. -/
theorem polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
    [Nonempty n] (f : RatFunc ℂ) (X : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum X ⊆ s) (hfree : RationalPoleFreeOn f s) :
    IsUnit (polynomialEval f.denom X) := by
  rw [← spectrum.zero_notMem_iff ℂ]
  rw [polynomialEval, spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hzero⟩
  exact (rationalPoleFreeOn_iff f s).mp hfree z (hspectrum hz) hzero

/-- The reduced rational matrix evaluation of the Möbius function agrees
with the explicit numerator-times-inverse-denominator formula. -/
theorem rationalMatrixEval_rotatedRealMobiusRatFunc
    [Nonempty n] (X : SquareMatrix n) (hspectrum : matrixSpectrum X ⊆ closedUnitDisk)
    {ω : ℂ} {a : ℝ} (hω : ‖ω‖ = 1) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    rationalMatrixEval (rotatedRealMobiusRatFunc ω a) X =
      rotatedRealMobiusEval ω a X := by
  let p := rotatedRealMobiusNumeratorPolynomial ω a
  let d := rotatedRealMobiusDenominatorPolynomial ω a
  let h := rotatedRealMobiusRatFunc ω a
  let D := rotatedRealMobiusDenominator ω a X
  let P := rotatedRealMobiusNumerator ω a X
  let HD := polynomialEval h.denom X
  let HN := polynomialEval h.num X
  have hd : d ≠ 0 := rotatedRealMobiusDenominatorPolynomial_ne_zero ω a
  have hcrossPolynomial : h.num * d = p * h.denom := by
    apply (RatFunc.num_mul_eq_mul_denom_iff hd).mpr
    rfl
  have hcross : HN * D = P * HD := by
    have hmapped := congrArg (fun q : Polynomial ℂ ↦ polynomialEval q X) hcrossPolynomial
    simp only [polynomialEval, map_mul] at hmapped
    dsimp only [HN, HD, P, D]
    rw [← polynomialEval_rotatedRealMobiusDenominatorPolynomial,
      ← polynomialEval_rotatedRealMobiusNumeratorPolynomial]
    simpa only [p, d, polynomialEval] using hmapped
  have hDunit : IsUnit D := by
    exact isUnit_rotatedRealMobiusDenominator X hspectrum hω ha0 ha1
  have hHDunit : IsUnit HD := by
    exact polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
      h X closedUnitDisk hspectrum
        (rationalPoleFreeOn_rotatedRealMobiusRatFunc_closedUnitDisk hω ha0 ha1)
  have hDdet : IsUnit D.det := D.isUnit_iff_isUnit_det.mp hDunit
  have hHDdet : IsUnit HD.det := HD.isUnit_iff_isUnit_det.mp hHDunit
  have hcomm : D * HD = HD * D := by
    dsimp only [D, HD]
    rw [← polynomialEval_rotatedRealMobiusDenominatorPolynomial]
    simp only [polynomialEval, ← map_mul]
    rw [mul_comm]
  have hcommInv : HD * D⁻¹ = D⁻¹ * HD := by
    calc
      HD * D⁻¹ = (D⁻¹ * D) * (HD * D⁻¹) := by
        rw [D.nonsing_inv_mul hDdet, Matrix.one_mul]
      _ = D⁻¹ * (D * HD) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (HD * D) * D⁻¹ := by rw [hcomm]
      _ = (D⁻¹ * HD) * (D * D⁻¹) := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * HD := by rw [D.mul_nonsing_inv hDdet, Matrix.mul_one]
  have hsolve : HN * HD⁻¹ = P * D⁻¹ := by
    have hfirst : HN = P * HD * D⁻¹ := by
      calc
        HN = HN * D * D⁻¹ :=
          (D.mul_nonsing_inv_cancel_right HN hDdet).symm
        _ = (P * HD) * D⁻¹ := by rw [hcross]
    calc
      HN * HD⁻¹ = (P * HD * D⁻¹) * HD⁻¹ := by rw [hfirst]
      _ = P * (HD * D⁻¹) * HD⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * (D⁻¹ * HD) * HD⁻¹ := by rw [hcommInv]
      _ = P * D⁻¹ * (HD * HD⁻¹) := by simp only [Matrix.mul_assoc]
      _ = P * D⁻¹ := by rw [HD.mul_nonsing_inv hHDdet, Matrix.mul_one]
  exact hsolve

end CrouzeixConjecture
