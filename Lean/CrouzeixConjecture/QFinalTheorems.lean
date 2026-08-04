module

public import CrouzeixConjecture.QTransfer
public import CrouzeixConjecture.QSharpness

@[expose] public section

noncomputable section

open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The sharp universal spectral constant from the scaled `q`-numerical-range
theorem, written in the form displayed in the manuscript. -/
def sharpScaledQNumericalRangeConstant (q : ℂ) : ℝ :=
  max 1 (2 * ‖q‖ / (1 + √(1 - ‖q‖ ^ 2)))

/-- The displayed sharp constant is the constant produced by the reusable
transfer theorem. -/
theorem sharpScaledQNumericalRangeConstant_eq_qTransferredConstant
    {q : ℂ} (hq0 : q ≠ 0) :
    sharpScaledQNumericalRangeConstant q = qTransferredConstant 2 q := by
  rw [sharpScaledQNumericalRangeConstant, qTransferredConstant,
    two_div_qKappa (norm_pos_iff.mpr hq0)]

/-- Rational spectral-set form of the sharp scaled `q`-numerical-range
theorem. -/
theorem sharpRationalScaledQNumericalRangeBound
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    (A : SquareMatrix n) (f : RatFunc ℂ)
    (hfree : RationalPoleFreeOn f (scaledQNumericalRange q A)) :
    ‖rationalMatrixEval f A‖ ≤
      sharpScaledQNumericalRangeConstant q *
        maxRationalModulusOnScaledQNumericalRange q A f := by
  rw [sharpScaledQNumericalRangeConstant_eq_qTransferredConstant hq0]
  exact rationalScaledQNumericalRangeBound_two hq0 hq1 A f hfree

/-- Polynomial specialization of the sharp scaled `q`-numerical-range
theorem. -/
theorem sharpPolynomialScaledQNumericalRangeBound
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤
      sharpScaledQNumericalRangeConstant q *
        maxPolynomialModulusOnScaledQNumericalRange q A p := by
  rw [sharpScaledQNumericalRangeConstant_eq_qTransferredConstant hq0]
  exact polynomialScaledQNumericalRangeBound_two hq0 hq1 A p

/-- For a positive real parameter, the displayed constant agrees with the
two-branch form used in the sharpness argument. -/
theorem sharpScaledQNumericalRangeConstant_ofReal
    {r : ℝ} (hr0 : 0 < r) :
    sharpScaledQNumericalRangeConstant (r : ℂ) =
      max 1 (2 / qKappa r) := by
  rw [sharpScaledQNumericalRangeConstant_eq_qTransferredConstant]
  · simp [qTransferredConstant, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
  · exact_mod_cast hr0.ne'

/-- The displayed constant gives the rational bound in dimension two. -/
theorem rationalScaledQBoundOnFinTwo_sharp
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    RationalScaledQBoundOnFinTwo r
      (sharpScaledQNumericalRangeConstant (r : ℂ)) := by
  intro A f hfree
  apply sharpRationalScaledQNumericalRangeBound (q := (r : ℂ))
  · exact_mod_cast hr0.ne'
  · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  · exact hfree

/-- Sharpness in an order-theoretic form: even after restricting to `2 × 2`
matrices, the displayed constant is the least rational spectral constant. -/
theorem sharpScaledQNumericalRangeConstant_isLeast_finTwo
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    IsLeast {K : ℝ | RationalScaledQBoundOnFinTwo r K}
      (sharpScaledQNumericalRangeConstant (r : ℂ)) := by
  refine ⟨rationalScaledQBoundOnFinTwo_sharp hr0 hr1, ?_⟩
  intro K hK
  rw [sharpScaledQNumericalRangeConstant_ofReal hr0]
  exact max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo
    hr0 hr1 hK

/-- Candidate rational spectral constants for a fixed complex parameter on
all `2 × 2` matrices. -/
def RationalScaledQBoundOnFinTwoAt (q : ℂ) (K : ℝ) : Prop :=
  ∀ (A : SquareMatrix (Fin 2)) (f : RatFunc ℂ),
    RationalPoleFreeOn f (scaledQNumericalRange q A) →
      ‖rationalMatrixEval f A‖ ≤
        K * maxRationalModulusOnScaledQNumericalRange q A f

/-- Phase reduction transports a candidate bound for complex `q` to its
positive real modulus. -/
theorem rationalScaledQBoundOnFinTwo_of_complex
    {q : ℂ} (hq0 : q ≠ 0) {K : ℝ}
    (hK : RationalScaledQBoundOnFinTwoAt q K) :
    RationalScaledQBoundOnFinTwo ‖q‖ K := by
  intro A f hfree
  have hfreeq : RationalPoleFreeOn f (scaledQNumericalRange q A) := by
    rw [scaledQNumericalRange_eq_norm hq0 A]
    exact hfree
  have hbound := hK A f hfreeq
  simpa [maxRationalModulusOnScaledQNumericalRange,
    scaledQNumericalRange_eq_norm hq0 A] using hbound

/-- The displayed constant gives the fixed-complex-parameter bound in
dimension two. -/
theorem rationalScaledQBoundOnFinTwoAt_sharp
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1) :
    RationalScaledQBoundOnFinTwoAt q
      (sharpScaledQNumericalRangeConstant q) := by
  intro A f hfree
  exact sharpRationalScaledQNumericalRangeBound hq0 hq1 A f hfree

/-- Complex-parameter sharpness: for every admissible nonzero `q`, the
displayed constant is least even after restricting to `2 × 2` matrices. -/
theorem sharpScaledQNumericalRangeConstant_isLeast_finTwo_complex
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1) :
    IsLeast {K : ℝ | RationalScaledQBoundOnFinTwoAt q K}
      (sharpScaledQNumericalRangeConstant q) := by
  refine ⟨rationalScaledQBoundOnFinTwoAt_sharp hq0 hq1, ?_⟩
  intro K hK
  have hr0 : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hlower :=
    max_one_two_div_qKappa_le_of_rationalScaledQBoundOnFinTwo
      hr0 hq1 (rationalScaledQBoundOnFinTwo_of_complex hq0 hK)
  rw [← sharpScaledQNumericalRangeConstant_ofReal hr0] at hlower
  simpa [sharpScaledQNumericalRangeConstant, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hlower

end CrouzeixConjecture
