module

public import CrouzeixConjecture.DoubleLayerAlgebra
public import CrouzeixConjecture.Positivity
public import CrouzeixConjecture.Spectrum
public import Mathlib.Topology.Closure

@[expose] public section

noncomputable section

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix
  Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact geometric information used from a smooth convex boundary point.  For the
manuscript, `Omega` is the bounded convex domain, `sigma ∈ ∂Omega`, and `nu` is its outward
unit normal.  Smooth convex geometry supplies `support_inequality`; all subsequent matrix
positivity is proved algebraically in this module. -/
structure OutwardBoundarySupport (Omega : Set ℂ) (sigma nu : ℂ) : Prop where
  isOpen_domain : IsOpen Omega
  boundary_point : sigma ∈ frontier Omega
  unit_normal : ‖nu‖ = 1
  support_inequality : ∀ z ∈ Omega, 0 ≤ RCLike.re (star nu * (sigma - z))

/-- A boundary point of an open domain is not in the domain. -/
theorem OutwardBoundarySupport.sigma_not_mem {Omega : Set ℂ} {sigma nu : ℂ}
    (hgeom : OutwardBoundarySupport Omega sigma nu) : sigma ∉ Omega := by
  intro hsigma
  have hmem : sigma ∈ Omega ∩ frontier Omega := ⟨hsigma, hgeom.boundary_point⟩
  rw [hgeom.isOpen_domain.inter_frontier_eq] at hmem
  exact hmem

/-- Strict containment of the numerical range in the domain puts every boundary point outside
the numerical range. -/
theorem OutwardBoundarySupport.sigma_not_mem_numericalRange
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    sigma ∉ numericalRange B := by
  exact fun hsigma ↦ hgeom.sigma_not_mem (hWB hsigma)

/-- A boundary point outside the numerical range lies in the resolvent set, using the already
proved inclusion `spectrum(B) ⊆ W(B)`. -/
theorem scalar_sub_matrix_isUnit_of_outwardBoundarySupport
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    IsUnit (sigma • (1 : SquareMatrix n) - B) := by
  have hsigmaNumerical := hgeom.sigma_not_mem_numericalRange B hWB
  have hsigmaSpectrum : sigma ∉ matrixSpectrum B := fun hsigma ↦
    hsigmaNumerical (matrixSpectrum_subset_numericalRange B hsigma)
  change sigma ∉ spectrum ℂ B at hsigmaSpectrum
  have hunit := spectrum.notMem_iff.mp hsigmaSpectrum
  simpa only [Algebra.algebraMap_eq_smul_one] using hunit

/-- A Hermitian matrix whose quadratic form is nonnegative on the Euclidean unit sphere is
positive semidefinite.  This is the finite-dimensional normalization step used below. -/
theorem posSemidef_of_reApplyInnerSelf_nonneg_on_unit
    (A : SquareMatrix n) (hA : A.IsHermitian)
    (hunit : ∀ x : EuclideanVector n, ‖x‖ = 1 →
      0 ≤ (euclideanOperator A).reApplyInnerSelf x) :
    A.PosSemidef := by
  change IsPositiveMatrix A
  rw [isPositiveMatrix_iff_euclideanOperator_isPositive]
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨?_, ?_⟩
  · change A.toEuclideanLin.IsSymmetric
    exact Matrix.isHermitian_iff_isSymmetric.mp hA
  · intro x
    by_cases hx : x = 0
    · subst x
      simp [ContinuousLinearMap.reApplyInnerSelf_apply]
    · let y : EuclideanVector n := (‖x‖ : ℂ)⁻¹ • x
      have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hynorm : ‖y‖ = 1 := by
        simp [y, norm_smul, hxnorm]
      have hxy : (‖x‖ : ℂ) • y = x := by
        simp [y, smul_smul, hxnorm]
      rw [← hxy, ContinuousLinearMap.reApplyInnerSelf_smul]
      exact mul_nonneg (sq_nonneg _) (hunit y hynorm)

/-- On a unit vector, the scalar support functional is the real quadratic form of the
unstarred support operator `conj(nu) (σI-B)`. -/
theorem supportOperator_reApplyInnerSelf_unit
    (B : SquareMatrix n) (sigma nu : ℂ) (x : EuclideanVector n) (hx : ‖x‖ = 1) :
    (euclideanOperator
      (star nu • (sigma • (1 : SquareMatrix n) - B))).reApplyInnerSelf x =
      RCLike.re (star nu * (sigma - ⟪x, euclideanOperator B x⟫_ℂ)) := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  simp only [map_smul, map_sub, map_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_smul_right,
    inner_sub_right, inner_self_eq_norm_sq_to_K, hx, one_pow]
  simp only [mul_one]

/-- The support-line matrix has twice the real quadratic form of the unstarred support
operator. -/
theorem doubleLayerSupportMatrix_reApplyInnerSelf_eq_two
    (B : SquareMatrix n) (sigma nu : ℂ) (x : EuclideanVector n) :
    (euclideanOperator (doubleLayerSupportMatrix B sigma nu)).reApplyInnerSelf x =
      2 * (euclideanOperator
        (star nu • (sigma • (1 : SquareMatrix n) - B))).reApplyInnerSelf x := by
  rw [doubleLayerSupportMatrix_eq_two_smul_rePart]
  have hmatrix :
      (2 : ℂ) • rePart (star nu • (sigma • (1 : SquareMatrix n) - B)) =
        star nu • (sigma • (1 : SquareMatrix n) - B) +
          (star nu • (sigma • (1 : SquareMatrix n) - B))ᴴ := by
    simp only [rePart, smul_smul]
    norm_num
  rw [hmatrix, map_add, euclideanOperator_conjTranspose]
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply,
    ContinuousLinearMap.add_apply, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, map_add]
  rw [inner_re_symm x
    (euclideanOperator (star nu • (sigma • (1 : SquareMatrix n) - B)) x)]
  ring

/-- The outward support inequality on a domain containing `W(B)` proves, rather than assumes,
positivity of the manuscript's support-line matrix. -/
theorem doubleLayerSupportMatrix_posSemidef_of_outwardBoundarySupport
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (doubleLayerSupportMatrix B sigma nu).PosSemidef := by
  apply posSemidef_of_reApplyInnerSelf_nonneg_on_unit
    (doubleLayerSupportMatrix B sigma nu)
    (doubleLayerSupportMatrix_isHermitian B sigma nu)
  intro x hx
  rw [doubleLayerSupportMatrix_reApplyInnerSelf_eq_two,
    supportOperator_reApplyInnerSelf_unit B sigma nu x hx]
  exact mul_nonneg (by norm_num)
    (hgeom.support_inequality ⟪x, euclideanOperator B x⟫_ℂ (hWB ⟨x, hx, rfl⟩))

/-- The manuscript's actual resolvent `R_σ = (σI-B)⁻¹`. -/
def doubleLayerResolvent (B : SquareMatrix n) (sigma : ℂ) : SquareMatrix n :=
  (sigma • (1 : SquareMatrix n) - B)⁻¹

/-- The actual resolvent is a right inverse at a supported boundary point. -/
theorem doubleLayerResolvent_rightInverse
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (sigma • (1 : SquareMatrix n) - B) * doubleLayerResolvent B sigma = 1 := by
  have hunit := scalar_sub_matrix_isUnit_of_outwardBoundarySupport hgeom B hWB
  have hdet : IsUnit (sigma • (1 : SquareMatrix n) - B).det :=
    (sigma • (1 : SquareMatrix n) - B).isUnit_iff_isUnit_det.mp hunit
  exact (sigma • (1 : SquareMatrix n) - B).mul_nonsing_inv hdet

/-- The actual resolvent is also a left inverse. -/
theorem doubleLayerResolvent_leftInverse
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    doubleLayerResolvent B sigma * (sigma • (1 : SquareMatrix n) - B) = 1 := by
  have hunit := scalar_sub_matrix_isUnit_of_outwardBoundarySupport hgeom B hWB
  have hdet : IsUnit (sigma • (1 : SquareMatrix n) - B).det :=
    (sigma • (1 : SquareMatrix n) - B).isUnit_iff_isUnit_det.mp hunit
  exact (sigma • (1 : SquareMatrix n) - B).nonsing_inv_mul hdet

/-- Exact instantiated form of manuscript lines 275–276 for the genuine resolvent. -/
theorem doubleLayerResolvent_congruence_density
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (doubleLayerResolvent B sigma)ᴴ * doubleLayerSupportMatrix B sigma nu *
        doubleLayerResolvent B sigma =
      doubleLayerDensity (doubleLayerResolvent B sigma) nu := by
  exact doubleLayer_congruence_density_identity B (doubleLayerResolvent B sigma) sigma nu
    (doubleLayerResolvent_rightInverse hgeom B hWB)

/-- Thus the double-layer density in manuscript equation (11) is positive semidefinite at
every supported boundary point. -/
theorem doubleLayerResolvent_density_posSemidef
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (doubleLayerDensity (doubleLayerResolvent B sigma) nu).PosSemidef := by
  exact doubleLayerDensity_posSemidef B (doubleLayerResolvent B sigma) sigma nu
    (doubleLayerResolvent_rightInverse hgeom B hWB)
    (doubleLayerSupportMatrix_posSemidef_of_outwardBoundarySupport hgeom B hWB)

/-- The positive scalar `1 / (2π)` appearing in the operator-valued measure preserves the
pointwise positivity of its matrix density. -/
theorem normalizedDoubleLayerResolvent_density_posSemidef
    {Omega : Set ℂ} {sigma nu : ℂ} (hgeom : OutwardBoundarySupport Omega sigma nu)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (((2 * Real.pi : ℝ)⁻¹) •
      doubleLayerDensity (doubleLayerResolvent B sigma) nu).PosSemidef := by
  exact (doubleLayerResolvent_density_posSemidef hgeom B hWB).smul
    (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le))

end CrouzeixConjecture
