module

public import CrouzeixConjecture.DoubleLayerCayley
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one orthogonal projection onto the span of `v`, when `v` is a unit vector. -/
def rankOneProjection (v : EuclideanVector n) : SquareMatrix n :=
  (euclideanOperator (n := n)).symm (InnerProductSpace.rankOne ℂ v v)

@[simp]
theorem euclideanOperator_rankOneProjection (v : EuclideanVector n) :
    euclideanOperator (rankOneProjection v) = InnerProductSpace.rankOne ℂ v v := by
  exact (euclideanOperator (n := n)).apply_symm_apply _

@[simp]
theorem euclideanOperator_rankOneProjection_apply
    (v x : EuclideanVector n) :
    euclideanOperator (rankOneProjection v) x = ⟪v, x⟫_ℂ • v := by
  simp

/-- A unit-vector rank-one operator is a self-adjoint idempotent. -/
theorem rankOneProjection_isStarProjection {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    IsStarProjection (rankOneProjection v) := by
  have hp : IsStarProjection (InnerProductSpace.rankOne ℂ v v) :=
    InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) hv
  exact
    ⟨hp.isIdempotentElem.map (euclideanOperator (n := n)).symm,
      hp.isSelfAdjoint.map (euclideanOperator (n := n)).symm⟩

/-- The positive stretch which multiplies the `v` direction by `kappa` and fixes its
orthogonal complement. -/
def stretchSimilarity (kappa : ℝ) (v : EuclideanVector n) : SquareMatrix n :=
  (kappa : ℂ) • rankOneProjection v + (1 - rankOneProjection v)

/-- The explicit inverse candidate for `stretchSimilarity`. -/
def stretchInverseCandidate (kappa : ℝ) (v : EuclideanVector n) : SquareMatrix n :=
  (kappa⁻¹ : ℂ) • rankOneProjection v + (1 - rankOneProjection v)

@[simp]
theorem euclideanOperator_stretchSimilarity_apply
    (kappa : ℝ) (v x : EuclideanVector n) :
    euclideanOperator (stretchSimilarity kappa v) x =
      (kappa : ℂ) • (⟪v, x⟫_ℂ • v) + (x - ⟪v, x⟫_ℂ • v) := by
  rw [stretchSimilarity, map_add, map_smul, map_sub, map_one]
  simp

@[simp]
theorem euclideanOperator_stretchInverseCandidate_apply
    (kappa : ℝ) (v x : EuclideanVector n) :
    euclideanOperator (stretchInverseCandidate kappa v) x =
      (kappa⁻¹ : ℂ) • (⟪v, x⟫_ℂ • v) + (x - ⟪v, x⟫_ℂ • v) := by
  rw [stretchInverseCandidate, map_add, map_smul, map_sub, map_one]
  simp

@[simp]
theorem inner_stretchSimilarity_apply
    (kappa : ℝ) {v : EuclideanVector n} (hv : ‖v‖ = 1) (x : EuclideanVector n) :
    ⟪v, euclideanOperator (stretchSimilarity kappa v) x⟫_ℂ =
      (kappa : ℂ) * ⟪v, x⟫_ℂ := by
  rw [euclideanOperator_stretchSimilarity_apply, inner_add_right, inner_smul_right,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
  simp

@[simp]
theorem inner_stretchInverseCandidate_apply
    (kappa : ℝ) {v : EuclideanVector n} (hv : ‖v‖ = 1) (x : EuclideanVector n) :
    ⟪v, euclideanOperator (stretchInverseCandidate kappa v) x⟫_ℂ =
      (kappa⁻¹ : ℂ) * ⟪v, x⟫_ℂ := by
  rw [euclideanOperator_stretchInverseCandidate_apply, inner_add_right, inner_smul_right,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
  simp

@[simp]
theorem stretchSimilarity_apply_self
    (kappa : ℝ) {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    euclideanOperator (stretchSimilarity kappa v) v = (kappa : ℂ) • v := by
  rw [euclideanOperator_stretchSimilarity_apply, inner_self_eq_norm_sq_to_K, hv]
  simp

theorem stretchInverseCandidate_apply_of_inner_eq_zero
    (kappa : ℝ) {v x : EuclideanVector n} (hvx : ⟪v, x⟫_ℂ = 0) :
    euclideanOperator (stretchInverseCandidate kappa v) x = x := by
  simp [euclideanOperator_stretchInverseCandidate_apply, hvx]

/-- The displayed inverse candidate is a right inverse of the stretch. -/
theorem stretchSimilarity_mul_inverseCandidate
    {kappa : ℝ} (hkappa : kappa ≠ 0)
  {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    stretchSimilarity kappa v * stretchInverseCandidate kappa v = 1 := by
  apply (euclideanOperator (n := n)).injective
  rw [map_mul, map_one]
  apply ContinuousLinearMap.ext
  intro x
  change euclideanOperator (stretchSimilarity kappa v)
      (euclideanOperator (stretchInverseCandidate kappa v) x) = x
  rw [euclideanOperator_stretchSimilarity_apply,
    inner_stretchInverseCandidate_apply kappa hv,
    euclideanOperator_stretchInverseCandidate_apply]
  simp [smul_smul, hkappa]

/-- The displayed inverse candidate is also a left inverse of the stretch. -/
theorem inverseCandidate_mul_stretchSimilarity
    {kappa : ℝ} (hkappa : kappa ≠ 0)
  {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    stretchInverseCandidate kappa v * stretchSimilarity kappa v = 1 := by
  apply (euclideanOperator (n := n)).injective
  rw [map_mul, map_one]
  apply ContinuousLinearMap.ext
  intro x
  change euclideanOperator (stretchInverseCandidate kappa v)
      (euclideanOperator (stretchSimilarity kappa v) x) = x
  rw [euclideanOperator_stretchInverseCandidate_apply,
    inner_stretchSimilarity_apply kappa hv,
    euclideanOperator_stretchSimilarity_apply]
  simp [smul_smul, hkappa]

/-- The nonsingular matrix inverse of a stretch is its displayed inverse candidate. -/
theorem stretchSimilarity_inv
    {kappa : ℝ} (hkappa : kappa ≠ 0)
    {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    (stretchSimilarity kappa v)⁻¹ = stretchInverseCandidate kappa v := by
  exact Matrix.inv_eq_left_inv (inverseCandidate_mul_stretchSimilarity hkappa hv)

/-- A stretch with nonnegative scale is positive semidefinite. -/
theorem stretchSimilarity_posSemidef
    {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    (stretchSimilarity kappa v).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  rw [stretchSimilarity]
  exact add_nonneg
    (smul_nonneg (by positivity)
      (rankOneProjection_isStarProjection hv).nonneg)
    (rankOneProjection_isStarProjection hv).one_sub_nonneg

/-- A stretch by a positive factor is positive definite. -/
theorem stretchSimilarity_posDef
    {kappa : ℝ} (hkappa : 0 < kappa)
    {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    (stretchSimilarity kappa v).PosDef := by
  have hpsd := stretchSimilarity_posSemidef hkappa.le hv
  apply hpsd.posDef_iff_isUnit.mpr
  exact IsUnit.of_mul_eq_one (stretchInverseCandidate kappa v)
    (stretchSimilarity_mul_inverseCandidate hkappa.ne' hv)

end CrouzeixConjecture
