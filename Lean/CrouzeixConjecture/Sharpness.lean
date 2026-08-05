module

public import CrouzeixConjecture.FinalTheorems

public import CrouzeixConjecture.QSharpness

@[expose] public section

noncomputable section

open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- For the nilpotent Jordan block, the identity polynomial has numerical-range
maximum `1 / 2`. This is the normalization used by the manuscript's sharpness example. -/
theorem maxPolynomialModulusOnNumericalRange_X_jordanNilpotentTwo :
    maxPolynomialModulusOnNumericalRange jordanNilpotentTwo Polynomial.X = 1 / 2 := by
  calc
    maxPolynomialModulusOnNumericalRange jordanNilpotentTwo Polynomial.X =
        maxPolynomialModulusOnScaledQNumericalRange 1
          jordanNilpotentTwo Polynomial.X := by
      simp only [maxPolynomialModulusOnNumericalRange,
        maxPolynomialModulusOnScaledQNumericalRange,
        scaledQNumericalRange_one]
    _ = qKappa 1 / 2 := by
      exact maxPolynomialModulusOnScaledQNumericalRange_X_jordanNilpotentTwo
        (r := 1) (by norm_num) (by norm_num)
    _ = 1 / 2 := by norm_num [qKappa, qTau]

/-- The Jordan block and the identity polynomial attain the factor `2`. -/
theorem jordanNilpotentTwo_attains_two :
    ‖polynomialEval Polynomial.X jordanNilpotentTwo‖ =
      2 * maxPolynomialModulusOnNumericalRange jordanNilpotentTwo Polynomial.X := by
  rw [norm_polynomialEval_X_jordanNilpotentTwo,
    maxPolynomialModulusOnNumericalRange_X_jordanNilpotentTwo]
  norm_num

/-- Candidate ordinary rational spectral constants, restricted to `2 × 2` matrices. -/
def RationalCrouzeixBoundOnFinTwo (K : ℝ) : Prop :=
  ∀ (A : SquareMatrix (Fin 2)) (f : RatFunc ℂ),
    RationalPoleFreeOn f (numericalRange A) →
      ‖rationalMatrixEval f A‖ ≤ K * maxRationalModulusOnNumericalRange A f

/-- The ordinary Crouzeix constant `2` is least even after restricting to
`2 × 2` matrices.  The lower bound is the `q = 1` Jordan-block example. -/
theorem crouzeixConstantTwo_isLeast_finTwo :
    IsLeast {K : ℝ | RationalCrouzeixBoundOnFinTwo K} 2 := by
  refine ⟨?_, ?_⟩
  · intro A f hfree
    exact crouzeixRationalBound A f hfree
  · intro K hK
    let x : RatFunc ℂ :=
      algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X
    have hbound :
        ‖rationalMatrixEval x jordanNilpotentTwo‖ ≤
          K * maxRationalModulusOnNumericalRange jordanNilpotentTwo x :=
      hK jordanNilpotentTwo x
        (rationalPoleFreeOn_algebraMap_polynomial Polynomial.X
          (numericalRange jordanNilpotentTwo))
    have hnorm : ‖rationalMatrixEval x jordanNilpotentTwo‖ = 1 := by
      simpa only [x] using norm_rationalMatrixEval_X_jordanNilpotentTwo
    have hmax :
        maxRationalModulusOnNumericalRange jordanNilpotentTwo x = 1 / 2 := by
      calc
        maxRationalModulusOnNumericalRange jordanNilpotentTwo x =
            maxRationalModulusOnScaledQNumericalRange 1 jordanNilpotentTwo x := by
              simp only [maxRationalModulusOnNumericalRange,
                maxRationalModulusOnScaledQNumericalRange,
                scaledQNumericalRange_one]
        _ = qKappa 1 / 2 := by
          simpa only [x] using
            maxRationalModulusOnScaledQNumericalRange_X_jordanNilpotentTwo
              (r := 1) (by norm_num) (by norm_num)
        _ = 1 / 2 := by norm_num [qKappa, qTau]
    rw [hnorm, hmax] at hbound
    nlinarith

end CrouzeixConjecture
