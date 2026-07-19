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

/-- The support-line matrix in manuscript lines 268--271. -/
def doubleLayerSupportMatrix {n : Type*} [DecidableEq n]
    (B : SquareMatrix n) (sigma nu : ℂ) : SquareMatrix n :=
  nu • (star sigma • (1 : SquareMatrix n) - Bᴴ) +
    star nu • (sigma • (1 : SquareMatrix n) - B)

/-- The support-line matrix is twice the real part used in manuscript line 270. -/
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

/-- The unnormalised double-layer density in the parentheses of manuscript equation (261). -/
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

/-- Exact algebra behind manuscript lines 275--276: congruencing the support-line
matrix by the resolvent produces the double-layer density. -/
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

/-- Abstract integral form of the map in manuscript equation (292).  The two functions
stand for the already normalised analytic and adjoint pieces of the density. -/
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

/-- Abstracted Cauchy-mass calculation from manuscript lines 278--289.  The hypotheses
state exactly the two contour-integral evaluations left to boundary geometry. -/
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

/-- Abstracted companion-transform identity from manuscript equation (308).  Its two
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

/-- Scalar Cayley transform used for the boundary functions in manuscript line 314. -/
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

/-- Norm-convergent Cayley expansion from manuscript lines 325--330. -/
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

/-- Manuscript line 346: equality of the two generated algebras moves a companion
adjoint from `alg(B)` into `alg(Tᴴ)`. -/
theorem conjTranspose_mem_generatedAlgebra_conjTranspose_of_eq
    {n : Type*} [Fintype n] [DecidableEq n] {B T X : SquareMatrix n}
    (hAlg : generatedAlgebra T = generatedAlgebra B)
    (hX : X ∈ generatedAlgebra B) : Xᴴ ∈ generatedAlgebra Tᴴ := by
  apply conjTranspose_mem_generatedAlgebra_conjTranspose
  rw [hAlg]
  exact hX

/-- Coefficient in the norm-convergent expansion of `H` in manuscript equation (333). -/
def doubleLayerCompletionCoefficient
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : SquareMatrix n) (G : ℕ → SquareMatrix n) (m : ℕ) : SquareMatrix n :=
  T ^ m + (G m)ᴴ

/-- Positive-degree tail term of the expansion of `H`. -/
def doubleLayerCompletionTailTerm
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T : SquareMatrix n) (G : ℕ → SquareMatrix n) (m : ℕ) :
    SquareMatrix n :=
  z ^ (m + 1) • doubleLayerCompletionCoefficient T G (m + 1)

/-- A term of the full matrix geometric series for the resolvent. -/
def resolventSeriesTerm
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T : SquareMatrix n) (m : ℕ) : SquareMatrix n :=
  z ^ m • T ^ m

/-- Positive-degree tail term of the matrix geometric series. -/
def resolventTailTerm
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T : SquareMatrix n) (m : ℕ) : SquareMatrix n :=
  z ^ (m + 1) • T ^ (m + 1)

/-- Positive-degree companion term in manuscript equation (340). -/
def companionTailTerm {n : Type*} (z : ℂ)
    (G : ℕ → SquareMatrix n) (m : ℕ) : SquareMatrix n :=
  z ^ (m + 1) • (G (m + 1))ᴴ

/-- Coefficientwise cancellation of the resolvent terms leaves precisely the companion
term. -/
theorem doubleLayerCompletionTailTerm_sub_resolventTailTerm
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T : SquareMatrix n) (G : ℕ → SquareMatrix n) (m : ℕ) :
    doubleLayerCompletionTailTerm z T G m - resolventTailTerm z T m =
      companionTailTerm z G m := by
  simp [doubleLayerCompletionTailTerm, doubleLayerCompletionCoefficient,
    resolventTailTerm, companionTailTerm, smul_add]

/-- Removing the constant term from the full geometric resolvent series gives its
positive-degree tail. -/
theorem resolventTailTerm_hasSum_of_resolventSeries
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T : SquareMatrix n)
    (hResolvent : HasSum (resolventSeriesTerm z T)
      ((1 : SquareMatrix n) - z • T)⁻¹) :
    HasSum (resolventTailTerm z T)
      (((1 : SquareMatrix n) - z • T)⁻¹ - 1) := by
  have htail := (hasSum_nat_add_iff' 1).mpr hResolvent
  simpa [resolventSeriesTerm, resolventTailTerm, add_comm] using htail

/-- Subtracting the geometric resolvent series from the expansion of `H` proves
manuscript equation (340) as an equality of norm-convergent series. -/
theorem companionTailTerm_hasSum_completion_sub_resolvent
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (T H : SquareMatrix n) (G : ℕ → SquareMatrix n)
    (hH : HasSum (doubleLayerCompletionTailTerm z T G) (H - 1))
    (hResolvent : HasSum (resolventSeriesTerm z T)
      ((1 : SquareMatrix n) - z • T)⁻¹) :
    HasSum (companionTailTerm z G)
      (H - ((1 : SquareMatrix n) - z • T)⁻¹) := by
  have hR := resolventTailTerm_hasSum_of_resolventSeries z T hResolvent
  have hsub := hH.sub hR
  convert hsub using 1
  · funext m
    exact (doubleLayerCompletionTailTerm_sub_resolventTailTerm z T G m).symm
  · exact
      (sub_sub_sub_cancel_right H ((1 : SquareMatrix n) - z • T)⁻¹ 1).symm

/-- Each companion tail term lies in `alg(Tᴴ)` once the corresponding unstarred
companion value lies in the algebra shared by `B` and `T`. -/
theorem companionTailTerm_mem_generatedAlgebra_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) {B T : SquareMatrix n} (G : ℕ → SquareMatrix n)
    (hAlg : generatedAlgebra T = generatedAlgebra B)
    (hG : ∀ m : ℕ, G (m + 1) ∈ generatedAlgebra B) (m : ℕ) :
    companionTailTerm z G m ∈ generatedAlgebra Tᴴ := by
  apply (generatedAlgebra Tᴴ).smul_mem
  exact conjTranspose_mem_generatedAlgebra_conjTranspose_of_eq hAlg (hG m)

/-- Algebraic and topological conclusion of manuscript lines 343--352.  The geometric
resolvent and holomorphic-calculus work is isolated in the two `HasSum` hypotheses and
the exact generated-algebra membership hypothesis for positive degrees. -/
theorem completion_sub_resolvent_mem_generatedAlgebra_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : ℂ) (B T H : SquareMatrix n) (G : ℕ → SquareMatrix n)
    (hAlg : generatedAlgebra T = generatedAlgebra B)
    (hG : ∀ m : ℕ, G (m + 1) ∈ generatedAlgebra B)
    (hH : HasSum (doubleLayerCompletionTailTerm z T G) (H - 1))
    (hResolvent : HasSum (resolventSeriesTerm z T)
      ((1 : SquareMatrix n) - z • T)⁻¹) :
    H - ((1 : SquareMatrix n) - z • T)⁻¹ ∈ generatedAlgebra Tᴴ := by
  apply generatedAlgebra_hasSum_mem Tᴴ (companionTailTerm z G)
    (H - ((1 : SquareMatrix n) - z • T)⁻¹)
    (companionTailTerm_hasSum_completion_sub_resolvent z T H G hH hResolvent)
  exact companionTailTerm_mem_generatedAlgebra_conjTranspose z G hAlg hG

end CrouzeixConjecture
