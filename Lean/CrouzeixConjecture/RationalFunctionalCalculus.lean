module

public import CrouzeixConjecture.NumericalRange
public import CrouzeixConjecture.Spectrum
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite poles of a rational function, expressed using Mathlib's canonical reduced
denominator.  Thus removable singularities from an unreduced presentation are not counted. -/
def rationalPoleSet (r : RatFunc ℂ) : Set ℂ :=
  {z | Polynomial.eval z r.denom = 0}

/-- The canonical reduced denominator has only finitely many complex zeros. -/
theorem rationalPoleSet_finite (r : RatFunc ℂ) :
    (rationalPoleSet r).Finite := by
  simpa [rationalPoleSet, Polynomial.IsRoot] using
    (Polynomial.finite_setOf_isRoot (RatFunc.denom_ne_zero r))

/-- A rational function is pole-free on a set when its canonical denominator has no zero there. -/
def RationalPoleFreeOn (r : RatFunc ℂ) (s : Set ℂ) : Prop :=
  Disjoint (rationalPoleSet r) s

/-- Scalar evaluation using the same canonical reduced fraction as `rationalMatrixEval`. -/
def rationalScalarEval (r : RatFunc ℂ) (z : ℂ) : ℂ :=
  Polynomial.eval z r.num / Polynomial.eval z r.denom

/-- The local scalar definition agrees with Mathlib's reduced rational-function evaluation. -/
theorem rationalScalarEval_eq_ratFuncEval (r : RatFunc ℂ) (z : ℂ) :
    rationalScalarEval r z = RatFunc.eval (RingHom.id ℂ) z r := by
  simp [rationalScalarEval, RatFunc.eval]

/-- Pointwise form of pole-freeness. -/
theorem rationalPoleFreeOn_iff (r : RatFunc ℂ) (s : Set ℂ) :
    RationalPoleFreeOn r s ↔
      ∀ z ∈ s, Polynomial.eval z r.denom ≠ 0 := by
  constructor
  · intro h z hzs hzero
    exact Set.disjoint_left.mp h (by simpa [rationalPoleSet] using hzero) hzs
  · intro h
    apply Set.disjoint_left.mpr
    intro z hzp hzs
    exact h z hzs (by simpa [rationalPoleSet] using hzp)

/-- A reduced rational function is continuous on every set on which it is pole-free. -/
theorem continuousOn_rationalScalarEval (r : RatFunc ℂ) (s : Set ℂ)
    (hfree : RationalPoleFreeOn r s) :
    ContinuousOn (rationalScalarEval r) s := by
  apply ContinuousOn.div
  · exact r.num.continuous.continuousOn
  · exact r.denom.continuous.continuousOn
  · intro z hzs
    exact (rationalPoleFreeOn_iff r s).mp hfree z hzs

/-- Evaluation of a rational function at a matrix using the canonical reduced numerator and
denominator.  When the function is pole-free on the spectrum, the denominator matrix is a unit. -/
def rationalMatrixEval (r : RatFunc ℂ) (A : SquareMatrix n) : SquareMatrix n :=
  polynomialEval r.num A * (polynomialEval r.denom A)⁻¹

/-- Pole-freeness on the numerical range makes the canonical denominator invertible at the
matrix.  This uses the proved inclusion `spectrum(A) ⊆ W(A)` and polynomial spectral mapping. -/
theorem polynomialEval_denom_isUnit_of_rationalPoleFreeOn_numericalRange
    [Nonempty n] (r : RatFunc ℂ) (A : SquareMatrix n)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    IsUnit (polynomialEval r.denom A) := by
  rw [← spectrum.zero_notMem_iff ℂ]
  rw [polynomialEval, spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hzero⟩
  have hzW : z ∈ numericalRange A :=
    matrixSpectrum_subset_numericalRange A hz
  exact (rationalPoleFreeOn_iff r (numericalRange A)).mp hfree z hzW hzero

end CrouzeixConjecture
