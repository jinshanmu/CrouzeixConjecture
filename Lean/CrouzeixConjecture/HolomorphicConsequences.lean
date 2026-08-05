module

public import CrouzeixConjecture.HolomorphicOuterLimit
public import CrouzeixConjecture.RationalCorollary

@[expose] public section

noncomputable section

open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The holomorphic matrix calculus agrees with the canonical reduced rational calculus whenever
the rational function has no pole on the numerical range. -/
theorem holomorphicMatrixEval_rational
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    holomorphicMatrixEval A (rationalScalarEval r) = rationalMatrixEval r A := by
  let U := (rationalPoleSet r)ᶜ
  have hUopen : IsOpen U := isOpen_compl_rationalPoleSet r
  have hWU : numericalRange A ⊆ U :=
    (rationalPoleFreeOn_iff_subset_compl r (numericalRange A)).mp hfree
  have hfreeU : RationalPoleFreeOn r U :=
    rationalPoleFreeOn_compl_rationalPoleSet r
  have hdenNonzero : ∀ z ∈ U, Polynomial.eval z r.denom ≠ 0 :=
    (rationalPoleFreeOn_iff r U).mp hfreeU
  have hdenHolomorphic :
      DifferentiableOn ℂ (fun z ↦ Polynomial.eval z r.denom) U :=
    r.denom.differentiableOn
  have hinvHolomorphic :
      DifferentiableOn ℂ (fun z ↦ (Polynomial.eval z r.denom)⁻¹) U := by
    simpa only [Pi.inv_apply] using hdenHolomorphic.inv hdenNonzero
  have hdenInv := holomorphicMatrixEval_mul A hUopen hWU
    hdenHolomorphic hinvHolomorphic
  have hproductOne :
      holomorphicMatrixEval A
          (fun z ↦ Polynomial.eval z r.denom * (Polynomial.eval z r.denom)⁻¹) =
        holomorphicMatrixEval A (fun _ ↦ 1) := by
    apply holomorphicMatrixEval_congr_on_neighborhood A hUopen hWU
    intro z hz
    exact mul_inv_cancel₀ (hdenNonzero z hz)
  have hrightInverse :
      polynomialEval r.denom A *
          holomorphicMatrixEval A (fun z ↦ (Polynomial.eval z r.denom)⁻¹) = 1 := by
    calc
      polynomialEval r.denom A *
          holomorphicMatrixEval A (fun z ↦ (Polynomial.eval z r.denom)⁻¹) =
          holomorphicMatrixEval A (fun z ↦ Polynomial.eval z r.denom) *
            holomorphicMatrixEval A (fun z ↦ (Polynomial.eval z r.denom)⁻¹) := by
              rw [holomorphicMatrixEval_polynomial]
      _ = holomorphicMatrixEval A
          (fun z ↦ Polynomial.eval z r.denom * (Polynomial.eval z r.denom)⁻¹) :=
        hdenInv.symm
      _ = holomorphicMatrixEval A (fun _ ↦ 1) := hproductOne
      _ = polynomialEval (1 : Polynomial ℂ) A := by
        simpa only [Polynomial.eval_one] using
          holomorphicMatrixEval_polynomial A (1 : Polynomial ℂ)
      _ = 1 := by simp [polynomialEval]
  have hinverse :
      holomorphicMatrixEval A (fun z ↦ (Polynomial.eval z r.denom)⁻¹) =
        (polynomialEval r.denom A)⁻¹ :=
    (Matrix.inv_eq_right_inv hrightInverse).symm
  have hnumMul := holomorphicMatrixEval_mul A hUopen hWU
    r.num.differentiableOn hinvHolomorphic
  calc
    holomorphicMatrixEval A (rationalScalarEval r) =
        holomorphicMatrixEval A
          (fun z ↦ Polynomial.eval z r.num * (Polynomial.eval z r.denom)⁻¹) := by
      rfl
    _ = holomorphicMatrixEval A (fun z ↦ Polynomial.eval z r.num) *
        holomorphicMatrixEval A (fun z ↦ (Polynomial.eval z r.denom)⁻¹) := hnumMul
    _ = polynomialEval r.num A * (polynomialEval r.denom A)⁻¹ := by
      rw [holomorphicMatrixEval_polynomial, hinverse]
    _ = rationalMatrixEval r A := rfl

/-- The finite rational Crouzeix estimate is the immediate rational specialization of the
holomorphic theorem. -/
theorem holomorphicCrouzeixRationalBound
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    ‖rationalMatrixEval r A‖ ≤
      2 * maxRationalModulusOnNumericalRange A r := by
  let U := (rationalPoleSet r)ᶜ
  have hUopen : IsOpen U := isOpen_compl_rationalPoleSet r
  have hWU : numericalRange A ⊆ U :=
    (rationalPoleFreeOn_iff_subset_compl r (numericalRange A)).mp hfree
  have hbound := holomorphicCrouzeixBound A hUopen hWU
    (differentiableOn_rationalScalarEval r U
      (rationalPoleFreeOn_compl_rationalPoleSet r))
  rw [holomorphicMatrixEval_rational A r hfree] at hbound
  simpa only [maxRationalModulusOnNumericalRange, maxFunctionModulusOnSet] using hbound

/-- The manuscript's polynomial matrix-function error estimate, obtained by applying the
holomorphic bound to the difference. -/
theorem holomorphicCrouzeixPolynomialErrorBound
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (p : Polynomial ℂ) :
    ‖holomorphicMatrixEval A f - polynomialEval p A‖ ≤
      2 * maxFunctionModulusOnSet (numericalRange A)
        (fun z ↦ f z - Polynomial.eval z p) := by
  have hbound := holomorphicCrouzeixBound A hUopen hWU
    (hf.sub p.differentiableOn)
  change ‖holomorphicMatrixEval A (fun z ↦ f z - Polynomial.eval z p)‖ ≤
    2 * maxFunctionModulusOnSet (numericalRange A)
      (fun z ↦ f z - Polynomial.eval z p) at hbound
  rw [holomorphicMatrixEval_sub A hUopen hWU hf p.differentiableOn,
    holomorphicMatrixEval_polynomial] at hbound
  exact hbound

/-- The manuscript's rational matrix-function error estimate.  Pole-freeness only on the
numerical range is needed: intersecting the given neighborhood with the rational holomorphy
domain supplies the common neighborhood used by the functional calculus. -/
theorem holomorphicCrouzeixRationalErrorBound
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    ‖holomorphicMatrixEval A f - rationalMatrixEval r A‖ ≤
      2 * maxFunctionModulusOnSet (numericalRange A)
        (fun z ↦ f z - rationalScalarEval r z) := by
  let V := U ∩ (rationalPoleSet r)ᶜ
  have hVopen : IsOpen V := hUopen.inter (isOpen_compl_rationalPoleSet r)
  have hWV : numericalRange A ⊆ V := fun z hz ↦
    ⟨hWU hz, (rationalPoleFreeOn_iff_subset_compl r (numericalRange A)).mp hfree hz⟩
  have hfV : DifferentiableOn ℂ f V := hf.mono (inter_subset_left)
  have hfreeV : RationalPoleFreeOn r V :=
    (rationalPoleFreeOn_iff_subset_compl r V).mpr inter_subset_right
  have hrV : DifferentiableOn ℂ (rationalScalarEval r) V :=
    differentiableOn_rationalScalarEval r V hfreeV
  have hbound := holomorphicCrouzeixBound A hVopen hWV (hfV.sub hrV)
  change ‖holomorphicMatrixEval A (fun z ↦ f z - rationalScalarEval r z)‖ ≤
    2 * maxFunctionModulusOnSet (numericalRange A)
      (fun z ↦ f z - rationalScalarEval r z) at hbound
  rw [holomorphicMatrixEval_sub A hVopen hWV hfV hrV,
    holomorphicMatrixEval_rational A r hfree] at hbound
  exact hbound

/-- Definition-level finite spectral-set consequence: spectrum containment and the rational
constant-two estimate are recorded together. -/
theorem finiteRationalSpectralSetCorollary (A : SquareMatrix n) :
    IsCompact (numericalRange A) ∧
      matrixSpectrum A ⊆ numericalRange A ∧
      ∀ r : RatFunc ℂ, RationalPoleFreeOn r (numericalRange A) →
        ‖rationalMatrixEval r A‖ ≤
          2 * maxRationalModulusOnNumericalRange A r := by
  exact ⟨isCompact_numericalRange A, matrixSpectrum_subset_numericalRange A,
    fun r hfree ↦ holomorphicCrouzeixRationalBound A r hfree⟩

end CrouzeixConjecture
