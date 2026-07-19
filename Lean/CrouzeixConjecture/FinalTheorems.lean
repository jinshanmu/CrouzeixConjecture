module

public import CrouzeixConjecture.RadialOuterReduction
public import CrouzeixConjecture.RationalApproximation

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The manuscript's final polynomial theorem, displayed without an intermediate statement
alias: for every finite positive-dimensional complex square matrix and complex polynomial, the
induced Euclidean operator norm is bounded by twice the maximum modulus on its numerical range. -/
theorem crouzeixConjecture (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤
      2 * maxPolynomialModulusOnNumericalRange A p :=
  crouzeixConjecture_mainTheorem A p

/-- The manuscript's rational spectral-set discussion, kept as a separate corollary.  Pole
freeness is required on exactly the numerical range, and the same constant `2` and induced
Euclidean matrix norm occur in the conclusion. -/
theorem crouzeixRationalSpectralSetCorollary :
    RationalSpectralSetCorollaryStatement (n := n) :=
  rationalSpectralSetCorollary_of_mainTheorem
    crouzeixConjecture_mainTheorem

/-- Pointwise form of the separate rational corollary. -/
theorem crouzeixRationalBound
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    ‖rationalMatrixEval r A‖ ≤
      2 * maxRationalModulusOnNumericalRange A r :=
  crouzeixRationalSpectralSetCorollary A r hfree

end CrouzeixConjecture
