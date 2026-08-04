module

public import CrouzeixConjecture.FinalTheorems
public import CrouzeixConjecture.QNumericalRange

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Maximum rational modulus on the scaled `q`-numerical range. -/
def maxRationalModulusOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (r : RatFunc ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖rationalScalarEval r z‖) '' scaledQNumericalRange q A)

/-- A pole-free rational function attains its maximum modulus on every nonempty scaled
`q`-numerical range. -/
theorem exists_maxRationalModulusOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (r : RatFunc ℂ)
    (hne : (scaledQNumericalRange q A).Nonempty)
    (hfree : RationalPoleFreeOn r (scaledQNumericalRange q A)) :
    ∃ z ∈ scaledQNumericalRange q A,
      ‖rationalScalarEval r z‖ =
        maxRationalModulusOnScaledQNumericalRange q A r := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_scaledQNumericalRange q A).exists_isMaxOn hne
      ((continuousOn_rationalScalarEval r (scaledQNumericalRange q A) hfree).norm)
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest
        ((fun w : ℂ ↦ ‖rationalScalarEval r w‖) '' scaledQNumericalRange q A)
        ‖rationalScalarEval r z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- Every scalar value is bounded by the attained rational maximum on the scaled
`q`-numerical range. -/
theorem norm_rationalScalarEval_le_maxOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (r : RatFunc ℂ)
    (hne : (scaledQNumericalRange q A).Nonempty)
    (hfree : RationalPoleFreeOn r (scaledQNumericalRange q A))
    {z : ℂ} (hz : z ∈ scaledQNumericalRange q A) :
    ‖rationalScalarEval r z‖ ≤
      maxRationalModulusOnScaledQNumericalRange q A r := by
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_scaledQNumericalRange q A).exists_isMaxOn hne
      ((continuousOn_rationalScalarEval r (scaledQNumericalRange q A) hfree).norm)
  have hgreatest :
      IsGreatest
        ((fun y : ℂ ↦ ‖rationalScalarEval r y‖) '' scaledQNumericalRange q A)
        ‖rationalScalarEval r w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxRationalModulusOnScaledQNumericalRange, hgreatest.csSup_eq]
  exact hmax hz

/-- A dimension-independent rational numerical-range estimate with constant `K`. -/
def UniversalRationalNumericalRangeBound (K : ℝ) : Prop :=
  ∀ {m : Type u} [Fintype m] [DecidableEq m] [Nonempty m]
    (A : SquareMatrix m) (r : RatFunc ℂ),
    RationalPoleFreeOn r (numericalRange A) →
      ‖rationalMatrixEval r A‖ ≤
        K * maxRationalModulusOnNumericalRange A r

/-- The proved rational Crouzeix theorem supplies the universal constant `2`. -/
theorem universalRationalNumericalRangeBound_two :
    UniversalRationalNumericalRangeBound.{u} 2 := by
  intro m _ _ _ A r hfree
  exact crouzeixRationalBound A r hfree

/-- A polynomial, regarded as a rational function, has no finite poles. -/
theorem rationalPoleFreeOn_algebraMap_polynomial
    (p : Polynomial ℂ) (s : Set ℂ) :
    RationalPoleFreeOn
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) s := by
  rw [rationalPoleFreeOn_iff]
  intro z hz
  simp

/-- Scalar rational evaluation specializes to ordinary polynomial evaluation. -/
@[simp] theorem rationalScalarEval_algebraMap_polynomial
    (p : Polynomial ℂ) (z : ℂ) :
    rationalScalarEval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z =
      Polynomial.eval z p := by
  simp [rationalScalarEval]

/-- Matrix rational evaluation specializes to ordinary polynomial evaluation. -/
@[simp] theorem rationalMatrixEval_algebraMap_polynomial
    (p : Polynomial ℂ) (A : SquareMatrix n) :
    rationalMatrixEval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) A =
      polynomialEval p A := by
  simp [rationalMatrixEval, polynomialEval]

/-- The scaled-range rational maximum specializes to its polynomial counterpart. -/
@[simp] theorem maxRationalModulusOnScaledQNumericalRange_algebraMap_polynomial
    (q : ℂ) (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxRationalModulusOnScaledQNumericalRange q A
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      maxPolynomialModulusOnScaledQNumericalRange q A p := by
  simp [maxRationalModulusOnScaledQNumericalRange,
    maxPolynomialModulusOnScaledQNumericalRange]

/-- The numerical-range rational maximum also specializes to its polynomial counterpart. -/
@[simp] theorem maxRationalModulusOnNumericalRange_algebraMap_polynomial
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxRationalModulusOnNumericalRange A
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      maxPolynomialModulusOnNumericalRange A p := by
  simp [maxRationalModulusOnNumericalRange,
    maxPolynomialModulusOnNumericalRange]

/-- Every universal rational numerical-range bound contains its polynomial specialization. -/
theorem polynomialNumericalRangeBound_of_universalRationalNumericalRangeBound
    (K : ℝ) (hK : UniversalRationalNumericalRangeBound.{u} K)
    [Nonempty n] (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤ K * maxPolynomialModulusOnNumericalRange A p := by
  have hbound :=
    hK (m := n) A (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      (rationalPoleFreeOn_algebraMap_polynomial p (numericalRange A))
  rw [rationalMatrixEval_algebraMap_polynomial,
    maxRationalModulusOnNumericalRange_algebraMap_polynomial] at hbound
  exact hbound

end CrouzeixConjecture
