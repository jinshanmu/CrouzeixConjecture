module

public import CrouzeixConjecture.Statements
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The numerical-range quadratic form is continuous. -/
theorem continuous_euclideanQuadraticForm (A : SquareMatrix n) :
    Continuous (fun x : EuclideanVector n ↦ ⟪x, euclideanOperator A x⟫_ℂ) :=
  continuous_id.inner (euclideanOperator A).continuous

/-- The defining unit-vector set is the Euclidean unit sphere. -/
theorem numericalRange_eq_image_sphere (A : SquareMatrix n) :
    numericalRange A =
      (fun x : EuclideanVector n ↦ ⟪x, euclideanOperator A x⟫_ℂ) '' Metric.sphere 0 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mp hx, rfl⟩

/-- The numerical range of a finite complex matrix is compact. -/
theorem isCompact_numericalRange (A : SquareMatrix n) : IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image_sphere]
  exact (isCompact_sphere (0 : EuclideanVector n) 1).image
    (continuous_euclideanQuadraticForm A)

/-- On a positive-dimensional matrix space, the manuscript's displayed maximum is attained. -/
theorem exists_maxPolynomialModulusOnNumericalRange [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ∃ z ∈ numericalRange A,
      ‖p.eval z‖ = maxPolynomialModulusOnNumericalRange A p := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (numericalRange_nonempty A)
      p.continuous.norm.continuousOn
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖p.eval w‖) '' numericalRange A) ‖p.eval z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- Every value on the numerical range is bounded by the attained manuscript maximum. -/
theorem norm_polynomial_eval_le_maxOnNumericalRange [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ numericalRange A) :
    ‖p.eval z‖ ≤ maxPolynomialModulusOnNumericalRange A p := by
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (numericalRange_nonempty A)
      p.continuous.norm.continuousOn
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖p.eval y‖) '' numericalRange A) ‖p.eval w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxPolynomialModulusOnNumericalRange, hgreatest.csSup_eq]
  exact hmax hz

/-- Quantitative continuity of numerical range under matrix perturbation, in the exact
Euclidean operator norm used by the manuscript. -/
theorem numericalRange_perturbation (A B : SquareMatrix n) {z : ℂ}
    (hz : z ∈ numericalRange B) :
    ∃ w ∈ numericalRange A, ‖z - w‖ ≤ ‖B - A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨⟪x, euclideanOperator A x⟫_ℂ, ⟨x, hx, rfl⟩, ?_⟩
  calc
    ‖⟪x, euclideanOperator B x⟫_ℂ - ⟪x, euclideanOperator A x⟫_ℂ‖ =
        ‖⟪x, euclideanOperator (B - A) x⟫_ℂ‖ := by
          rw [map_sub, ContinuousLinearMap.sub_apply, inner_sub_right]
    _ ≤ ‖x‖ * ‖euclideanOperator (B - A) x‖ :=
      norm_inner_le_norm x (euclideanOperator (B - A) x)
    _ ≤ ‖x‖ * (‖euclideanOperator (B - A)‖ * ‖x‖) := by
          gcongr
          exact (euclideanOperator (B - A)).le_opNorm x
    _ = ‖euclideanOperator (B - A)‖ := by rw [hx, one_mul, mul_one]
    _ = ‖B - A‖ := (matrix_norm_eq_euclidean_operator_norm (B - A)).symm

/-- Every point of the numerical range is bounded by the induced Euclidean operator norm. -/
theorem norm_le_of_mem_numericalRange (A : SquareMatrix n) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, euclideanOperator A x⟫_ℂ‖ ≤ ‖x‖ * ‖euclideanOperator A x‖ :=
      norm_inner_le_norm x (euclideanOperator A x)
    _ ≤ ‖x‖ * (‖euclideanOperator A‖ * ‖x‖) := by
      gcongr
      exact (euclideanOperator A).le_opNorm x
    _ = ‖euclideanOperator A‖ := by rw [hx, one_mul, mul_one]
    _ = ‖A‖ := (matrix_norm_eq_euclidean_operator_norm A).symm

end CrouzeixConjecture
