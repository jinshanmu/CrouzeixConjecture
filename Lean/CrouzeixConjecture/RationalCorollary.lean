module

public import CrouzeixConjecture.Limiting
public import CrouzeixConjecture.NumericalRange
public import CrouzeixConjecture.RationalFunctionalCalculus

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The maximum modulus of a reduced rational function on the numerical range. -/
def maxRationalModulusOnNumericalRange
    (A : SquareMatrix n) (r : RatFunc ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖rationalScalarEval r z‖) '' numericalRange A)

/-- The separate rational constant-two conclusion corresponding to
`eq:spectral-set-definition`. -/
def RationalCrouzeixBound (A : SquareMatrix n) (r : RatFunc ℂ) : Prop :=
  RationalPoleFreeOn r (numericalRange A) →
    ‖rationalMatrixEval r A‖ ≤ 2 * maxRationalModulusOnNumericalRange A r

/-- Quantified rational spectral-set corollary, kept separate from the polynomial theorem. -/
def RationalSpectralSetCorollaryStatement : Prop :=
  ∀ (A : SquareMatrix n) (r : RatFunc ℂ), RationalCrouzeixBound A r

/-- For a pole-free rational function, the displayed maximum on the compact numerical range is
attained. -/
theorem exists_maxRationalModulusOnNumericalRange
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    ∃ z ∈ numericalRange A,
      ‖rationalScalarEval r z‖ = maxRationalModulusOnNumericalRange A r := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (numericalRange_nonempty A)
      ((continuousOn_rationalScalarEval r (numericalRange A) hfree).norm)
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖rationalScalarEval r w‖) '' numericalRange A)
        ‖rationalScalarEval r z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- The final limiting step of the manuscript's Runge argument.  It makes explicit the two
convergences that a polynomial-approximation theorem and the matrix functional calculus must
supply; neither convergence is hidden in this result. -/
theorem rationalCrouzeixBound_of_polynomial_approximation
    (hMain : MainTheoremStatement (n := n))
    (A : SquareMatrix n) (r : RatFunc ℂ) (q : ℕ → Polynomial ℂ)
    (hmatrix : Tendsto (fun k ↦ polynomialEval (q k) A) atTop
      (nhds (rationalMatrixEval r A)))
    (hmax : Tendsto
      (fun k ↦ maxPolynomialModulusOnNumericalRange A (q k)) atTop
      (nhds (maxRationalModulusOnNumericalRange A r))) :
    ‖rationalMatrixEval r A‖ ≤ 2 * maxRationalModulusOnNumericalRange A r := by
  apply le_of_tendsto_of_tendsto' hmatrix.norm (hmax.const_mul 2)
  intro k
  exact hMain A (q k)

end CrouzeixConjecture
