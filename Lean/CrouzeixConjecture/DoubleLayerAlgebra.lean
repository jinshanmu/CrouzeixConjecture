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

/-- Scalar Cayley transform used for the boundary functions in
`eq:cayley-boundary-function`. -/
def cayleyTransform (z w : ℂ) : ℂ := (1 + z * w) / (1 - z * w)

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

/-- Conjugate transpose transports membership in `alg(T)` to membership in `alg(Tᴴ)`. -/
theorem conjTranspose_mem_generatedAlgebra_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n] {T X : SquareMatrix n}
    (hX : X ∈ generatedAlgebra T) : Xᴴ ∈ generatedAlgebra Tᴴ := by
  have hstar : star X ∈ star (generatedAlgebra T) :=
    (Subalgebra.star_mem_star_iff (generatedAlgebra T) X).2 hX
  rw [generatedAlgebra, Subalgebra.star_adjoin_comm] at hstar
  simpa only [Set.star_singleton, Matrix.star_eq_conjTranspose] using hstar

end CrouzeixConjecture
