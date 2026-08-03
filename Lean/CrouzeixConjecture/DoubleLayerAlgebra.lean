module

public import CrouzeixConjecture.GeneratedAlgebra
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator Pointwise

namespace CrouzeixConjecture

/-- The support-line matrix in `eq:supporting-half-plane`. -/
def doubleLayerSupportMatrix {n : Type*} [DecidableEq n]
    (B : SquareMatrix n) (sigma nu : ℂ) : SquareMatrix n :=
  nu • (star sigma • (1 : SquareMatrix n) - Bᴴ) +
    star nu • (sigma • (1 : SquareMatrix n) - B)

/-- The support-line matrix is twice the real part in `eq:supporting-half-plane`. -/
theorem doubleLayerSupportMatrix_eq_two_smul_rePart
    {n : Type*} [DecidableEq n] (B : SquareMatrix n) (sigma nu : ℂ) :
    doubleLayerSupportMatrix B sigma nu =
      (2 : ℂ) • rePart (star nu • (sigma • (1 : SquareMatrix n) - B)) := by
  simp only [doubleLayerSupportMatrix, rePart, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, star_star, smul_add, smul_smul]
  module

/-- The support-line matrix is Hermitian, independently of its geometric positivity. -/
theorem doubleLayerSupportMatrix_isHermitian
    {n : Type*} [DecidableEq n] (B : SquareMatrix n) (sigma nu : ℂ) :
    (doubleLayerSupportMatrix B sigma nu).IsHermitian := by
  simp [doubleLayerSupportMatrix, Matrix.IsHermitian, add_comm]

/-- The unnormalised double-layer density in `eq:double-layer-measure`. -/
def doubleLayerDensity {n : Type*} (R : SquareMatrix n) (nu : ℂ) : SquareMatrix n :=
  nu • R + star nu • Rᴴ

/-- The double-layer density is Hermitian. -/
theorem doubleLayerDensity_isHermitian
    {n : Type*} (R : SquareMatrix n) (nu : ℂ) :
    (doubleLayerDensity R nu).IsHermitian := by
  simp [doubleLayerDensity, Matrix.IsHermitian, add_comm]

/-- Taking conjugate transpose turns the right inverse resolvent identity into the
corresponding left inverse identity. -/
theorem resolvent_conjTranspose_leftInverse
    {n : Type*} [Fintype n] [DecidableEq n]
    (B R : SquareMatrix n) (sigma : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - B) * R = 1) :
    Rᴴ * (star sigma • (1 : SquareMatrix n) - Bᴴ) = 1 := by
  have h := congrArg Matrix.conjTranspose hR
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, starRingEnd_apply,
    star_star] using h

/-- Exact algebra connecting `eq:supporting-half-plane` and `eq:double-layer-measure`:
congruencing the support-line matrix by the resolvent produces the double-layer density. -/
theorem doubleLayer_congruence_density_identity
    {n : Type*} [Fintype n] [DecidableEq n]
    (B R : SquareMatrix n) (sigma nu : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - B) * R = 1) :
    Rᴴ * doubleLayerSupportMatrix B sigma nu * R = doubleLayerDensity R nu := by
  have hRstar := resolvent_conjTranspose_leftInverse B R sigma hR
  simp only [doubleLayerSupportMatrix, doubleLayerDensity, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, mul_assoc, hR, hRstar, one_mul, mul_one]

/-- Once convex support geometry supplies positivity of the support-line matrix,
the double-layer density is positive by congruence. -/
theorem doubleLayerDensity_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    (B R : SquareMatrix n) (sigma nu : ℂ)
    (hR : (sigma • (1 : SquareMatrix n) - B) * R = 1)
    (hSupport : (doubleLayerSupportMatrix B sigma nu).PosSemidef) :
    (doubleLayerDensity R nu).PosSemidef := by
  rw [← doubleLayer_congruence_density_identity B R sigma nu hR]
  exact hSupport.conjTranspose_mul_mul_same R

/-- Abstract integral form of the map in `eq:Phi-definition`.  The two functions stand for
the already normalised analytic and adjoint pieces of the density. -/
def doubleLayerIntegralAverage {i n : Type*} [MeasurableSpace i]
    [Fintype n] [DecidableEq n] (mu : Measure i)
    (firstPart secondPart : i → SquareMatrix n) : SquareMatrix n :=
  (2 : ℂ)⁻¹ • ∫ x, firstPart x + secondPart x ∂mu

/-- The factor `1/2` in the double-layer map cancels the total factor `2`. -/
theorem two_smul_doubleLayerIntegralAverage
    {i n : Type*} [MeasurableSpace i] [Fintype n] [DecidableEq n]
    (mu : Measure i) (firstPart secondPart : i → SquareMatrix n) :
    (2 : ℂ) • doubleLayerIntegralAverage mu firstPart secondPart =
      ∫ x, firstPart x + secondPart x ∂mu := by
  simp [doubleLayerIntegralAverage]

/-- Abstracted Cauchy-mass calculation behind `eq:first-layer-mass` and
`eq:double-layer-mass`.  The hypotheses state exactly the two contour-integral evaluations
left to boundary geometry. -/
theorem doubleLayerIntegral_mass_eq_two_one
    {i n : Type*} [MeasurableSpace i] [Fintype n] [DecidableEq n]
    (mu : Measure i) (firstPart secondPart : i → SquareMatrix n)
    (hfirst : Integrable firstPart mu) (hsecond : Integrable secondPart mu)
    (hCauchy : ∫ x, firstPart x ∂mu = 1)
    (hAdjoint : ∫ x, secondPart x ∂mu = (∫ x, firstPart x ∂mu)ᴴ) :
    (∫ x, firstPart x + secondPart x ∂mu) =
      (2 : ℂ) • (1 : SquareMatrix n) := by
  rw [integral_add hfirst hsecond, hCauchy, hAdjoint, hCauchy,
    Matrix.conjTranspose_one]
  module

/-- The mass hypotheses make the abstract double-layer integral map unital. -/
theorem doubleLayerIntegralAverage_eq_one_of_cauchy
    {i n : Type*} [MeasurableSpace i] [Fintype n] [DecidableEq n]
    (mu : Measure i) (firstPart secondPart : i → SquareMatrix n)
    (hfirst : Integrable firstPart mu) (hsecond : Integrable secondPart mu)
    (hCauchy : ∫ x, firstPart x ∂mu = 1)
    (hAdjoint : ∫ x, secondPart x ∂mu = (∫ x, firstPart x ∂mu)ᴴ) :
    doubleLayerIntegralAverage mu firstPart secondPart = 1 := by
  rw [doubleLayerIntegralAverage,
    doubleLayerIntegral_mass_eq_two_one mu firstPart secondPart hfirst hsecond
      hCauchy hAdjoint]
  module

/-- Abstracted companion-transform identity from `eq:double-layer-identity`.  Its two
hypotheses are the Cauchy evaluation and the adjoint companion evaluation. -/
theorem doubleLayer_companion_identity
    {i n : Type*} [MeasurableSpace i] [Fintype n] [DecidableEq n]
    (mu : Measure i) (firstPart secondPart : i → SquareMatrix n)
    (hfirst : Integrable firstPart mu) (hsecond : Integrable secondPart mu)
    (hB gB : SquareMatrix n)
    (hCauchy : ∫ x, firstPart x ∂mu = hB)
    (hCompanion : ∫ x, secondPart x ∂mu = gBᴴ) :
    (2 : ℂ) • doubleLayerIntegralAverage mu firstPart secondPart = hB + gBᴴ := by
  rw [two_smul_doubleLayerIntegralAverage,
    integral_add hfirst hsecond, hCauchy, hCompanion]

/-- Scalar Cayley transform used for the boundary functions in
`eq:cayley-boundary-function`. -/
def cayleyTransform (z w : ℂ) : ℂ := (1 + z * w) / (1 - z * w)

/-- Coefficients of `1 + 2 ∑_{m ≥ 1} z^m w^m`. -/
def cayleyCoefficient (z w : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => 2 * z ^ (m + 1) * w ^ (m + 1)

/-- Constant coefficient in the Cayley expansion. -/
@[simp]
theorem cayleyCoefficient_zero (z w : ℂ) : cayleyCoefficient z w 0 = 1 := rfl

/-- Positive-degree coefficients in the Cayley expansion. -/
@[simp]
theorem cayleyCoefficient_succ (z w : ℂ) (m : ℕ) :
    cayleyCoefficient z w (m + 1) = 2 * z ^ (m + 1) * w ^ (m + 1) := rfl

/-- The Cayley boundary function has nonnegative real part under the manuscript's
disk bounds. -/
theorem cayleyTransform_re_nonneg {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    0 ≤ (cayleyTransform z w).re := by
  have hzw : ‖z * w‖ < 1 := calc
    ‖z * w‖ = ‖z‖ * ‖w‖ := norm_mul z w
    _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg z)
    _ < 1 := by simpa using hz
  have hne : 1 - z * w ≠ 0 := by
    intro h
    have hzwone : z * w = 1 := (sub_eq_zero.mp h).symm
    rw [hzwone, norm_one] at hzw
    exact lt_irrefl 1 hzw
  have hden : 0 < Complex.normSq (1 - z * w) := Complex.normSq_pos.mpr hne
  rw [cayleyTransform, Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re,
    Complex.add_im, Complex.one_im, Complex.sub_im]
  rw [← add_div]
  apply div_nonneg
  · have hsq : ‖z * w‖ ^ 2 < 1 := by nlinarith [norm_nonneg (z * w)]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
    nlinarith
  · exact hden.le

/-- Norm-convergent expansion of the scalar Cayley transform. -/
theorem cayleyCoefficient_hasSum {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    HasSum (cayleyCoefficient z w) (cayleyTransform z w) := by
  have hzw : ‖z * w‖ < 1 := calc
    ‖z * w‖ = ‖z‖ * ‖w‖ := norm_mul z w
    _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg z)
    _ < 1 := by simpa using hz
  have hseries := (hasSum_geometric_of_norm_lt_one hzw).mul_left (2 : ℂ)
  have hone := hasSum_ite_eq 0 (1 : ℂ)
  have hsub := hseries.sub hone
  have hne : 1 - z * w ≠ 0 := by
    intro h
    have hzwone : z * w = 1 := (sub_eq_zero.mp h).symm
    rw [hzwone, norm_one] at hzw
    exact lt_irrefl 1 hzw
  convert hsub using 1
  · funext m
    rcases m with _ | m
    · norm_num [cayleyCoefficient]
    · simp [cayleyCoefficient, mul_pow, mul_assoc]
  · rw [cayleyTransform, div_eq_mul_inv]
    field_simp [hne]
    ring

/-- Conjugate transpose transports membership in `alg(T)` to membership in `alg(Tᴴ)`. -/
theorem conjTranspose_mem_generatedAlgebra_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n] {T X : SquareMatrix n}
    (hX : X ∈ generatedAlgebra T) : Xᴴ ∈ generatedAlgebra Tᴴ := by
  have hstar : star X ∈ star (generatedAlgebra T) :=
    (Subalgebra.star_mem_star_iff (generatedAlgebra T) X).2 hX
  rw [generatedAlgebra, Subalgebra.star_adjoin_comm] at hstar
  simpa only [Set.star_singleton, Matrix.star_eq_conjTranspose] using hstar

end CrouzeixConjecture
