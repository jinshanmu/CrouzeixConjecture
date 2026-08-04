module

public import CrouzeixConjecture.QMobius
public import CrouzeixConjecture.SimpleSpectrum

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial functional calculus is covariant under an invertible matrix
similarity. -/
theorem polynomialEval_similarity
    (p : Polynomial ℂ) (A S : SquareMatrix n) (hS : IsUnit S) :
    polynomialEval p (S * A * S⁻¹) = S * polynomialEval p A * S⁻¹ := by
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  let u : (SquareMatrix n)ˣ := S.nonsingInvUnit hSdet
  change polynomialEval p (innerConjugation u A) = innerConjugation u (polynomialEval p A)
  exact Polynomial.aeval_algHom_apply (innerConjugation u) A p

/-- The nonsingular inverse of a product of two invertible matrices is the
reverse product of their nonsingular inverses. -/
theorem nonsing_inv_mul_of_isUnit
    (A B : SquareMatrix n) (hA : IsUnit A) (hB : IsUnit B) :
    (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  have hAdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  have hBdet : IsUnit B.det := B.isUnit_iff_isUnit_det.mp hB
  apply Matrix.inv_eq_right_inv
  calc
    (A * B) * (B⁻¹ * A⁻¹) = A * (B * B⁻¹) * A⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = A * 1 * A⁻¹ := by rw [B.mul_nonsing_inv hBdet]
    _ = 1 := by rw [Matrix.mul_one, A.mul_nonsing_inv hAdet]

/-- Nonsingular inversion is covariant under an invertible similarity. -/
theorem nonsing_inv_similarity
    (S A : SquareMatrix n) (hS : IsUnit S) (hA : IsUnit A) :
    (S * A * S⁻¹)⁻¹ = S * A⁻¹ * S⁻¹ := by
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  have hAdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA
  apply Matrix.inv_eq_right_inv
  calc
    (S * A * S⁻¹) * (S * A⁻¹ * S⁻¹) =
        S * A * (S⁻¹ * S) * A⁻¹ * S⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = S * A * 1 * A⁻¹ * S⁻¹ := by rw [S.nonsing_inv_mul hSdet]
    _ = S * (A * A⁻¹) * S⁻¹ := by simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = S * 1 * S⁻¹ := by rw [A.mul_nonsing_inv hAdet]
    _ = 1 := by rw [Matrix.mul_one, S.mul_nonsing_inv hSdet]

/-- Rational functional calculus is covariant under similarity whenever the
reduced denominator is invertible at the original matrix. -/
theorem rationalMatrixEval_similarity
    (f : RatFunc ℂ) (A S : SquareMatrix n) (hS : IsUnit S)
    (hden : IsUnit (polynomialEval f.denom A)) :
    rationalMatrixEval f (S * A * S⁻¹) =
      S * rationalMatrixEval f A * S⁻¹ := by
  rw [rationalMatrixEval, rationalMatrixEval,
    polynomialEval_similarity f.num A S hS,
    polynomialEval_similarity f.denom A S hS,
    nonsing_inv_similarity S (polynomialEval f.denom A) hS hden]
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hS
  calc
    (S * polynomialEval f.num A * S⁻¹) *
        (S * (polynomialEval f.denom A)⁻¹ * S⁻¹) =
      S * polynomialEval f.num A * (S⁻¹ * S) *
        (polynomialEval f.denom A)⁻¹ * S⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = S * polynomialEval f.num A * 1 *
        (polynomialEval f.denom A)⁻¹ * S⁻¹ := by
          rw [S.nonsing_inv_mul hSdet]
    _ = S * (polynomialEval f.num A * (polynomialEval f.denom A)⁻¹) * S⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_one]

/-- Pole-freeness on a set containing the spectrum supplies the denominator
hypothesis in `rationalMatrixEval_similarity`. -/
theorem rationalMatrixEval_similarity_of_rationalPoleFreeOn
    [Nonempty n] (f : RatFunc ℂ) (A S : SquareMatrix n) (s : Set ℂ)
    (hS : IsUnit S) (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s) :
    rationalMatrixEval f (S * A * S⁻¹) =
      S * rationalMatrixEval f A * S⁻¹ := by
  apply rationalMatrixEval_similarity f A S hS
  exact polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
    f A s hspectrum hfree

/-- Displayed numerator polynomial for the rational composition
`z ↦ (c f(z) - a) / (1 - a c f(z))`. -/
def mobiusComposeNumeratorPolynomial
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) : Polynomial ℂ :=
  Polynomial.C c * f.num - Polynomial.C (a : ℂ) * f.denom

/-- Displayed denominator polynomial for the rational composition
`z ↦ (c f(z) - a) / (1 - a c f(z))`. -/
def mobiusComposeDenominatorPolynomial
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) : Polynomial ℂ :=
  f.denom - Polynomial.C ((a : ℂ) * c) * f.num

/-- The explicit rational function representing
`z ↦ (c f(z) - a) / (1 - a c f(z))`. -/
def mobiusComposeRatFunc (f : RatFunc ℂ) (c : ℂ) (a : ℝ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (mobiusComposeNumeratorPolynomial f c a) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (mobiusComposeDenominatorPolynomial f c a)

/-- Algebraic identification of the explicit numerator/denominator
presentation with `(c f - a) / (1 - a c f)` in the rational-function field. -/
theorem mobiusComposeRatFunc_eq (f : RatFunc ℂ) (c : ℂ) (a : ℝ) :
    mobiusComposeRatFunc f c a =
      (RatFunc.C c * f - RatFunc.C (a : ℂ)) /
        (1 - RatFunc.C ((a : ℂ) * c) * f) := by
  let N : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) f.num
  let D : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) f.denom
  have hf : f = N / D := by
    exact (RatFunc.num_div_denom f).symm
  have hD : D ≠ 0 := by
    dsimp only [D]
    simpa using (RatFunc.algebraMap_injective ℂ).ne
      (RatFunc.denom_ne_zero f)
  simp only [mobiusComposeRatFunc, mobiusComposeNumeratorPolynomial,
    mobiusComposeDenominatorPolynomial, map_sub, map_mul,
    RatFunc.algebraMap_C]
  change (RatFunc.C c * N - RatFunc.C (a : ℂ) * D) /
      (D - RatFunc.C (a : ℂ) * RatFunc.C c * N) =
        (RatFunc.C c * f - RatFunc.C (a : ℂ)) /
          (1 - RatFunc.C (a : ℂ) * RatFunc.C c * f)
  rw [hf]
  by_cases hnew : D - RatFunc.C (a : ℂ) * RatFunc.C c * N = 0
  · have hdenzero :
        1 - RatFunc.C (a : ℂ) * RatFunc.C c * (N / D) = 0 := by
      field_simp [hD]
      simpa using hnew
    rw [hnew, div_zero, hdenzero, div_zero]
  · field_simp [hD, hnew]

@[simp]
theorem eval_mobiusComposeNumeratorPolynomial
    (f : RatFunc ℂ) (c z : ℂ) (a : ℝ) :
    Polynomial.eval z (mobiusComposeNumeratorPolynomial f c a) =
      c * Polynomial.eval z f.num - a * Polynomial.eval z f.denom := by
  simp [mobiusComposeNumeratorPolynomial]

@[simp]
theorem eval_mobiusComposeDenominatorPolynomial
    (f : RatFunc ℂ) (c z : ℂ) (a : ℝ) :
    Polynomial.eval z (mobiusComposeDenominatorPolynomial f c a) =
      Polynomial.eval z f.denom - ((a : ℂ) * c) * Polynomial.eval z f.num := by
  simp [mobiusComposeDenominatorPolynomial]

/-- Scalar evaluation of the displayed numerator factors through the reduced
denominator of `f`. -/
theorem eval_mobiusComposeNumeratorPolynomial_eq
    (f : RatFunc ℂ) (c z : ℂ) (a : ℝ)
    (hfden : Polynomial.eval z f.denom ≠ 0) :
    Polynomial.eval z (mobiusComposeNumeratorPolynomial f c a) =
      (c * rationalScalarEval f z - a) * Polynomial.eval z f.denom := by
  rw [eval_mobiusComposeNumeratorPolynomial]
  simp only [rationalScalarEval]
  field_simp

/-- Scalar evaluation of the displayed denominator factors through the
reduced denominator of `f`. -/
theorem eval_mobiusComposeDenominatorPolynomial_eq
    (f : RatFunc ℂ) (c z : ℂ) (a : ℝ)
    (hfden : Polynomial.eval z f.denom ≠ 0) :
    Polynomial.eval z (mobiusComposeDenominatorPolynomial f c a) =
      (1 - ((a : ℂ) * c) * rationalScalarEval f z) *
        Polynomial.eval z f.denom := by
  rw [eval_mobiusComposeDenominatorPolynomial]
  simp only [rationalScalarEval]
  field_simp

/-- A rational function presented by a displayed polynomial fraction is
pole-free wherever that displayed denominator does not vanish.  This bridges
Mathlib's canonical reduced denominator with the presentation used in the
manuscript. -/
theorem rationalPoleFreeOn_fraction_of_denominator_ne_zero
    (p d : Polynomial ℂ) (s : Set ℂ)
    (hd : ∀ z ∈ s, Polynomial.eval z d ≠ 0) :
    RationalPoleFreeOn
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) d) s := by
  rw [rationalPoleFreeOn_iff]
  intro z hz hcanonical
  have hdvd :
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) d).denom ∣ d :=
    RatFunc.denom_div_dvd p d
  obtain ⟨g, hg⟩ := hdvd
  apply hd z hz
  rw [hg, Polynomial.eval_mul, hcanonical, zero_mul]

/-- Scalar evaluation of a displayed rational fraction agrees with the
displayed quotient when both the reduced and displayed denominators are
nonzero. -/
theorem rationalScalarEval_fraction
    (r : RatFunc ℂ) (p d : Polynomial ℂ) (z : ℂ)
    (hr : r = algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) d)
    (hreduced : Polynomial.eval z r.denom ≠ 0)
    (hdisplayed : Polynomial.eval z d ≠ 0) :
    rationalScalarEval r z = Polynomial.eval z p / Polynomial.eval z d := by
  have hd : d ≠ 0 := by
    intro hzero
    apply hdisplayed
    rw [hzero, Polynomial.eval_zero]
  have hcrossPolynomial : r.num * d = p * r.denom := by
    apply (RatFunc.num_mul_eq_mul_denom_iff hd).mpr
    exact hr
  have hcross := congrArg (Polynomial.eval z) hcrossPolynomial
  simp only [Polynomial.eval_mul] at hcross
  exact (div_eq_div_iff hreduced hdisplayed).mpr hcross

/-- The explicit Möbius composition is pole-free on a set if `f` is pole-free
there and the new scalar denominator has no zero there. -/
theorem rationalPoleFreeOn_mobiusComposeRatFunc
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) (s : Set ℂ)
    (hfree : RationalPoleFreeOn f s)
    (hmobius : ∀ z ∈ s, 1 - ((a : ℂ) * c) * rationalScalarEval f z ≠ 0) :
    RationalPoleFreeOn (mobiusComposeRatFunc f c a) s := by
  apply rationalPoleFreeOn_fraction_of_denominator_ne_zero
  intro z hz
  have hfden : Polynomial.eval z f.denom ≠ 0 :=
    (rationalPoleFreeOn_iff f s).mp hfree z hz
  rw [eval_mobiusComposeDenominatorPolynomial_eq f c z a hfden]
  exact mul_ne_zero (hmobius z hz) hfden

/-- Pointwise scalar evaluation of the explicit Möbius composition. -/
theorem rationalScalarEval_mobiusComposeRatFunc
    (f : RatFunc ℂ) (c z : ℂ) (a : ℝ)
    (hfden : Polynomial.eval z f.denom ≠ 0)
    (hmobius : 1 - ((a : ℂ) * c) * rationalScalarEval f z ≠ 0) :
    rationalScalarEval (mobiusComposeRatFunc f c a) z =
      (c * rationalScalarEval f z - a) /
        (1 - ((a : ℂ) * c) * rationalScalarEval f z) := by
  let p := mobiusComposeNumeratorPolynomial f c a
  let d := mobiusComposeDenominatorPolynomial f c a
  let h := mobiusComposeRatFunc f c a
  have hdisplayed : Polynomial.eval z d ≠ 0 := by
    rw [eval_mobiusComposeDenominatorPolynomial_eq f c z a hfden]
    exact mul_ne_zero hmobius hfden
  have hfree : RationalPoleFreeOn h ({z} : Set ℂ) := by
    apply rationalPoleFreeOn_fraction_of_denominator_ne_zero
    intro w hw
    have hwz : w = z := Set.mem_singleton_iff.mp hw
    subst w
    exact hdisplayed
  have hreduced : Polynomial.eval z h.denom ≠ 0 :=
    (rationalPoleFreeOn_iff h {z}).mp hfree z (Set.mem_singleton z)
  calc
    rationalScalarEval h z = Polynomial.eval z p / Polynomial.eval z d := by
      apply rationalScalarEval_fraction h p d z
      · rfl
      · exact hreduced
      · exact hdisplayed
    _ = (c * rationalScalarEval f z - a) /
        (1 - ((a : ℂ) * c) * rationalScalarEval f z) := by
      rw [eval_mobiusComposeNumeratorPolynomial_eq f c z a hfden,
        eval_mobiusComposeDenominatorPolynomial_eq f c z a hfden,
        mul_div_mul_right]
      exact hfden

/-- Matrix evaluation of a displayed rational fraction agrees with the
displayed numerator-times-inverse-denominator whenever both denominators are
invertible. -/
theorem rationalMatrixEval_fraction
    [Nonempty n] (r : RatFunc ℂ) (p d : Polynomial ℂ) (A : SquareMatrix n)
    (hr : r = algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) d)
    (hreduced : IsUnit (polynomialEval r.denom A))
    (hdisplayed : IsUnit (polynomialEval d A)) :
    rationalMatrixEval r A = polynomialEval p A * (polynomialEval d A)⁻¹ := by
  have hd : d ≠ 0 := by
    intro hzero
    subst d
    simp only [map_zero, polynomialEval] at hdisplayed
    exact not_isUnit_zero hdisplayed
  have hcrossPolynomial : r.num * d = p * r.denom := by
    apply (RatFunc.num_mul_eq_mul_denom_iff hd).mpr
    exact hr
  let D := polynomialEval d A
  let P := polynomialEval p A
  let HD := polynomialEval r.denom A
  let HN := polynomialEval r.num A
  have hcross : HN * D = P * HD := by
    have hmapped := congrArg (fun q : Polynomial ℂ ↦ polynomialEval q A) hcrossPolynomial
    simp only [polynomialEval, map_mul] at hmapped
    simpa only [HN, HD, P, D, polynomialEval] using hmapped
  have hDdet : IsUnit D.det := D.isUnit_iff_isUnit_det.mp hdisplayed
  have hHDdet : IsUnit HD.det := HD.isUnit_iff_isUnit_det.mp hreduced
  have hcomm : D * HD = HD * D := by
    dsimp only [D, HD]
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

/-- Matrix evaluation of the displayed composition numerator factors through
the reduced denominator matrix of `f`. -/
theorem polynomialEval_mobiusComposeNumeratorPolynomial_eq
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) (A : SquareMatrix n)
    (hfden : IsUnit (polynomialEval f.denom A)) :
    polynomialEval (mobiusComposeNumeratorPolynomial f c a) A =
      (c • rationalMatrixEval f A - (a : ℂ) • 1) *
        polynomialEval f.denom A := by
  have hfdenDet : IsUnit (polynomialEval f.denom A).det :=
    (polynomialEval f.denom A).isUnit_iff_isUnit_det.mp hfden
  have hcancel :
      rationalMatrixEval f A * polynomialEval f.denom A = polynomialEval f.num A := by
    exact (polynomialEval f.denom A).nonsing_inv_mul_cancel_right
      (polynomialEval f.num A) hfdenDet
  calc
    polynomialEval (mobiusComposeNumeratorPolynomial f c a) A =
        c • polynomialEval f.num A - (a : ℂ) • polynomialEval f.denom A := by
      simp [mobiusComposeNumeratorPolynomial, polynomialEval, Algebra.smul_def]
    _ = (c • rationalMatrixEval f A - (a : ℂ) • 1) *
        polynomialEval f.denom A := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hcancel]

/-- Matrix evaluation of the displayed composition denominator factors
through the reduced denominator matrix of `f`. -/
theorem polynomialEval_mobiusComposeDenominatorPolynomial_eq
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) (A : SquareMatrix n)
    (hfden : IsUnit (polynomialEval f.denom A)) :
    polynomialEval (mobiusComposeDenominatorPolynomial f c a) A =
      (1 - ((a : ℂ) * c) • rationalMatrixEval f A) *
        polynomialEval f.denom A := by
  have hfdenDet : IsUnit (polynomialEval f.denom A).det :=
    (polynomialEval f.denom A).isUnit_iff_isUnit_det.mp hfden
  have hcancel :
      rationalMatrixEval f A * polynomialEval f.denom A = polynomialEval f.num A := by
    exact (polynomialEval f.denom A).nonsing_inv_mul_cancel_right
      (polynomialEval f.num A) hfdenDet
  calc
    polynomialEval (mobiusComposeDenominatorPolynomial f c a) A =
        polynomialEval f.denom A - ((a : ℂ) * c) • polynomialEval f.num A := by
      simp [mobiusComposeDenominatorPolynomial, polynomialEval, Algebra.smul_def]
    _ = (1 - ((a : ℂ) * c) • rationalMatrixEval f A) *
        polynomialEval f.denom A := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hcancel]

/-- The explicit matrix expression for the Möbius composition with a rational
functional-calculus value. -/
def mobiusComposeMatrixEval
    (f : RatFunc ℂ) (c : ℂ) (a : ℝ) (A : SquareMatrix n) : SquareMatrix n :=
  (c • rationalMatrixEval f A - (a : ℂ) • 1) *
    (1 - ((a : ℂ) * c) • rationalMatrixEval f A)⁻¹

/-- Matrix evaluation of the explicit rational composition.  Pole-freeness of
`f` and of the new scalar denominator is stated on a set containing the
spectrum.  Invertibility of the new matrix denominator is kept explicit; in
the transfer proof it follows from the closed-unit-disk spectral hypothesis. -/
theorem rationalMatrixEval_mobiusComposeRatFunc
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (a : ℝ)
    (A : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s)
    (hscalarDenominator :
      ∀ z ∈ s, 1 - ((a : ℂ) * c) * rationalScalarEval f z ≠ 0)
    (hmatrixDenominator :
      IsUnit (1 - ((a : ℂ) * c) • rationalMatrixEval f A)) :
    rationalMatrixEval (mobiusComposeRatFunc f c a) A =
      mobiusComposeMatrixEval f c a A := by
  let p := mobiusComposeNumeratorPolynomial f c a
  let d := mobiusComposeDenominatorPolynomial f c a
  let h := mobiusComposeRatFunc f c a
  let FD := polynomialEval f.denom A
  let MN := c • rationalMatrixEval f A - (a : ℂ) • 1
  let MD := 1 - ((a : ℂ) * c) • rationalMatrixEval f A
  have hFDunit : IsUnit FD := by
    exact polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
      f A s hspectrum hfree
  have hComposeFree : RationalPoleFreeOn h s := by
    exact rationalPoleFreeOn_mobiusComposeRatFunc f c a s hfree hscalarDenominator
  have hReduced : IsUnit (polynomialEval h.denom A) := by
    exact polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
      h A s hspectrum hComposeFree
  have hPfactor : polynomialEval p A = MN * FD := by
    exact polynomialEval_mobiusComposeNumeratorPolynomial_eq f c a A hFDunit
  have hDfactor : polynomialEval d A = MD * FD := by
    exact polynomialEval_mobiusComposeDenominatorPolynomial_eq f c a A hFDunit
  have hDisplayed : IsUnit (polynomialEval d A) := by
    rw [hDfactor]
    exact hmatrixDenominator.mul hFDunit
  have hFraction :
      rationalMatrixEval h A = polynomialEval p A * (polynomialEval d A)⁻¹ := by
    apply rationalMatrixEval_fraction h p d A
    · rfl
    · exact hReduced
    · exact hDisplayed
  have hFDdet : IsUnit FD.det := FD.isUnit_iff_isUnit_det.mp hFDunit
  calc
    rationalMatrixEval h A = polynomialEval p A * (polynomialEval d A)⁻¹ := hFraction
    _ = (MN * FD) * (MD * FD)⁻¹ := by rw [hPfactor, hDfactor]
    _ = (MN * FD) * (FD⁻¹ * MD⁻¹) := by
      rw [nonsing_inv_mul_of_isUnit MD FD hmatrixDenominator hFDunit]
    _ = MN * MD⁻¹ := by
      calc
        (MN * FD) * (FD⁻¹ * MD⁻¹) = MN * (FD * FD⁻¹) * MD⁻¹ := by
          simp only [Matrix.mul_assoc]
        _ = MN * MD⁻¹ := by rw [FD.mul_nonsing_inv hFDdet, Matrix.mul_one]

/-- The scalar Möbius denominator is nonzero whenever its argument lies in
the open unit disk. -/
theorem one_sub_real_mul_ne_zero_of_norm_lt_one
    {w : ℂ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hw : ‖w‖ < 1) :
    1 - (a : ℂ) * w ≠ 0 := by
  have hwDisk : w ∈ closedUnitDisk := by
    simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using hw.le
  have h := eval_rotatedRealMobiusDenominatorPolynomial_ne_zero
    hwDisk (show ‖(1 : ℂ)‖ = 1 by simp) ha0 ha1
  simpa using h

/-- Closed-unit-disk spectrum of `c f(A)` makes the matrix denominator in the
Möbius composition invertible. -/
theorem isUnit_mobiusComposeMatrixDenominator_of_spectrum_subset_closedUnitDisk
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (a : ℝ) (A : SquareMatrix n)
    (hspectrum : matrixSpectrum (c • rationalMatrixEval f A) ⊆ closedUnitDisk)
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    IsUnit (1 - ((a : ℂ) * c) • rationalMatrixEval f A) := by
  have h := isUnit_rotatedRealMobiusDenominator
    (c • rationalMatrixEval f A) hspectrum
    (show ‖(1 : ℂ)‖ = 1 by simp) ha0 ha1
  simpa [rotatedRealMobiusDenominator, smul_smul] using h

/-- Transfer-ready form of matrix Möbius composition.  The scalar and matrix
disk hypotheses directly discharge both new-denominator conditions. -/
theorem rationalMatrixEval_mobiusComposeRatFunc_of_disk
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (a : ℝ)
    (A : SquareMatrix n) (s : Set ℂ)
    (hspectrumA : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s)
    (hscalarDisk : ∀ z ∈ s, ‖c * rationalScalarEval f z‖ < 1)
    (hmatrixDisk :
      matrixSpectrum (c • rationalMatrixEval f A) ⊆ closedUnitDisk)
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    rationalMatrixEval (mobiusComposeRatFunc f c a) A =
      mobiusComposeMatrixEval f c a A := by
  apply rationalMatrixEval_mobiusComposeRatFunc f c a A s hspectrumA hfree
  · intro z hz
    simpa only [mul_assoc] using
      one_sub_real_mul_ne_zero_of_norm_lt_one ha0 ha1 (hscalarDisk z hz)
  · exact isUnit_mobiusComposeMatrixDenominator_of_spectrum_subset_closedUnitDisk
      f c a A hmatrixDisk ha0 ha1

end CrouzeixConjecture
