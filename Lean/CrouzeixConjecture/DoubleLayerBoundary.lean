module

public import CrouzeixConjecture.DoubleLayerCayley
public import CrouzeixConjecture.HolomorphicMatrixAlgebra
public import CrouzeixConjecture.MainPerturbationReduction
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexConjugate ComplexOrder Matrix
  Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {i n : Type*} [TopologicalSpace i] [CompactSpace i]
  [MeasurableSpace i] [OpensMeasurableSpace i]
  [Fintype n] [DecidableEq n] [Nonempty n]

/-- A compact parametrized boundary carrying exactly the geometric data used by the
double-layer construction.  The measure on the parameter space is ordinary parameter
measure; `speed` is the arclength Jacobian.  No Cauchy formula is included in this structure. -/
structure ParametricConvexBoundary (Omega : Set ℂ) where
  point : C(i, ℂ)
  normal : C(i, ℂ)
  speed : C(i, ℝ)
  speed_nonneg : ∀ x, 0 ≤ speed x
  supported : ∀ x, OutwardBoundarySupport Omega (point x) (normal x)

variable {Omega : Set ℂ}

/-- The continuous resolvent along a parametrized supported boundary. -/
def parametricBoundaryResolvent
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (x : i) : SquareMatrix n :=
  doubleLayerResolvent B (Gamma.point x)

omit [CompactSpace i] [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
/-- Resolvent inversion is continuous along the compact boundary because every boundary
point lies outside the numerical range, hence outside the spectrum. -/
theorem continuous_parametricBoundaryResolvent
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    Continuous (parametricBoundaryResolvent Gamma B) := by
  have hmatrix : Continuous
      (fun x : i ↦ Gamma.point x • (1 : SquareMatrix n) - B) := by
    fun_prop
  apply continuous_iff_continuousAt.2
  intro x
  have hunit := scalar_sub_matrix_isUnit_of_outwardBoundarySupport
    (Gamma.supported x) B hWB
  have hdet : IsUnit
      (Gamma.point x • (1 : SquareMatrix n) - B).det :=
    (Gamma.point x • (1 : SquareMatrix n) - B).isUnit_iff_isUnit_det.mp hunit
  have hinverse : ContinuousAt Ring.inverse
      (Gamma.point x • (1 : SquareMatrix n) - B).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet.ne_zero
  have hinverseMatrix : ContinuousAt (Inv.inv : SquareMatrix n → SquareMatrix n)
      (Gamma.point x • (1 : SquareMatrix n) - B) :=
    continuousAt_matrix_inv _ hinverse
  change ContinuousAt
    (fun y : i ↦ (Gamma.point y • (1 : SquareMatrix n) - B)⁻¹) x
  exact hinverseMatrix.comp'
    (f := fun y : i ↦ Gamma.point y • (1 : SquareMatrix n) - B)
    hmatrix.continuousAt

/-- The normalized analytic half of the pulled-back double-layer density.  The factor
`speed` converts parameter measure to arclength and `1/(2π)` is the manuscript's
normalization. -/
def parametricBoundaryFirstPart
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (x : i) : SquareMatrix n :=
  ((2 * Real.pi : ℝ)⁻¹ * Gamma.speed x) •
    (Gamma.normal x • parametricBoundaryResolvent Gamma B x)

/-- The pulled-back density is the analytic half plus its pointwise adjoint. -/
def parametricDoubleLayerDensity
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (x : i) : SquareMatrix n :=
  parametricBoundaryFirstPart Gamma B x +
    (parametricBoundaryFirstPart Gamma B x)ᴴ

omit [CompactSpace i] [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
theorem continuous_parametricBoundaryFirstPart
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    Continuous (parametricBoundaryFirstPart Gamma B) := by
  unfold parametricBoundaryFirstPart
  have hres := continuous_parametricBoundaryResolvent Gamma B hWB
  fun_prop

omit [CompactSpace i] [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
theorem continuous_parametricDoubleLayerDensity
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    Continuous (parametricDoubleLayerDensity Gamma B) := by
  unfold parametricDoubleLayerDensity
  exact (continuous_parametricBoundaryFirstPart Gamma B hWB).add
    (continuous_parametricBoundaryFirstPart Gamma B hWB).matrix_conjTranspose

omit [Nonempty n] in
/-- A continuous matrix-valued function on the compact parameter space is Bochner integrable
for every finite parameter measure. -/
theorem integrable_of_continuous_compact [IsFiniteMeasure (mu : Measure i)]
    {f : i → SquareMatrix n} (hf : Continuous f) : Integrable f mu := by
  let fb : i →ᵇ SquareMatrix n :=
    BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  apply Integrable.of_bound fb.continuous.aestronglyMeasurable ‖fb‖
  exact Filter.Eventually.of_forall fun x ↦ fb.norm_coe_le_norm x

omit [Nonempty n] in
theorem integrable_parametricBoundaryFirstPart
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    Integrable (parametricBoundaryFirstPart Gamma B) mu :=
  integrable_of_continuous_compact
    (continuous_parametricBoundaryFirstPart Gamma B hWB)

omit [Nonempty n] in
/-- Multiplication by a bounded continuous scalar boundary function preserves integrability of
the analytic half of the double-layer density. -/
theorem integrable_parametricBoundaryBCFFirstPart
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (h : i →ᵇ ℂ) :
    Integrable (fun x ↦ h x • parametricBoundaryFirstPart Gamma B x) mu := by
  apply integrable_of_continuous_compact
  exact h.continuous.smul (continuous_parametricBoundaryFirstPart Gamma B hWB)

/-- Integration against the analytic half of the boundary density, as a linear map on continuous
boundary functions. -/
def parametricBoundaryFirstPartIntegralLinear
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (i →ᵇ ℂ) →ₗ[ℂ] SquareMatrix n where
  toFun h := ∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu
  map_add' h g := by
    simp only [BoundedContinuousFunction.add_apply, add_smul,
      integral_add (integrable_parametricBoundaryBCFFirstPart Gamma B hWB h)
        (integrable_parametricBoundaryBCFFirstPart Gamma B hWB g)]
  map_smul' c h := by
    simp only [BoundedContinuousFunction.smul_apply]
    have hfun :
        (fun x ↦ (c • h x) • parametricBoundaryFirstPart Gamma B x) =
          fun x ↦ c • (h x • parametricBoundaryFirstPart Gamma B x) := by
      funext x
      simp [smul_smul]
    rw [hfun, integral_smul]
    rfl

omit [Nonempty n] in
theorem parametricBoundaryFirstPartIntegral_norm_le
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (h : i →ᵇ ℂ) :
    ‖∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu‖ ≤
      (∫ x, ‖parametricBoundaryFirstPart Gamma B x‖ ∂mu) * ‖h‖ := by
  have hpoint : ∀ x,
      ‖h x • parametricBoundaryFirstPart Gamma B x‖ ≤
        ‖h‖ * ‖parametricBoundaryFirstPart Gamma B x‖ := by
    intro x
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm x) (norm_nonneg _)
  calc
    ‖∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu‖ ≤
        ∫ x, ‖h x • parametricBoundaryFirstPart Gamma B x‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖h‖ * ‖parametricBoundaryFirstPart Gamma B x‖ ∂mu := by
      exact integral_mono_ae
        (integrable_parametricBoundaryBCFFirstPart Gamma B hWB h).norm
        ((integrable_parametricBoundaryFirstPart Gamma B hWB).norm.const_mul ‖h‖)
        (Filter.Eventually.of_forall hpoint)
    _ = (∫ x, ‖parametricBoundaryFirstPart Gamma B x‖ ∂mu) * ‖h‖ := by
      rw [integral_const_mul]
      ring

/-- The boundary integral is continuous in the uniform norm. -/
def parametricBoundaryFirstPartIntegralCLM
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    (i →ᵇ ℂ) →L[ℂ] SquareMatrix n :=
  (parametricBoundaryFirstPartIntegralLinear Gamma B hWB).mkContinuous
    (∫ x, ‖parametricBoundaryFirstPart Gamma B x‖ ∂mu)
    (parametricBoundaryFirstPartIntegral_norm_le Gamma B hWB)

omit [Nonempty n] in
@[simp]
theorem parametricBoundaryFirstPartIntegralCLM_apply
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (h : i →ᵇ ℂ) :
    parametricBoundaryFirstPartIntegralCLM (mu := mu) Gamma B hWB h =
      ∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu := rfl

omit [Nonempty n] in
theorem integrable_parametricDoubleLayerDensity
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) :
    Integrable (parametricDoubleLayerDensity Gamma B) mu :=
  integrable_of_continuous_compact
    (continuous_parametricDoubleLayerDensity Gamma B hWB)

omit [CompactSpace i] [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
/-- Pointwise positivity of the pulled-back density follows from the supporting-line
inequality and the nonnegative arclength speed. -/
theorem parametricDoubleLayerDensity_posSemidef
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) (x : i) :
    (parametricDoubleLayerDensity Gamma B x).PosSemidef := by
  have hbase := normalizedDoubleLayerResolvent_density_posSemidef
    (Gamma.supported x) B hWB
  have hscaled := hbase.smul (Gamma.speed_nonneg x)
  have heq :
      parametricDoubleLayerDensity Gamma B x =
        Gamma.speed x • (((2 * Real.pi : ℝ)⁻¹ •
          doubleLayerDensity
            (parametricBoundaryResolvent Gamma B x) (Gamma.normal x))) := by
    ext a b
    simp [parametricDoubleLayerDensity, parametricBoundaryFirstPart,
      parametricBoundaryResolvent, doubleLayerDensity, smul_add,
      Complex.real_smul]
    ring
  rw [heq]
  exact hscaled

/-- The exact remaining analytic statement for a fixed parametrized contour: polynomial
Cauchy evaluation for the normalized analytic half of the density.  Unlike the previous
provider interface, this proposition exposes the contour integral that still has to be proved
from the radial convex-boundary construction. -/
def HasParametricPolynomialCauchyFormula
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n) : Prop :=
  ∀ q : Polynomial ℂ,
    ∫ x, Polynomial.eval (Gamma.point x) q •
      parametricBoundaryFirstPart Gamma B x ∂mu = polynomialEval q B

/-- A polynomial restricted to the compact parametrized boundary, bundled as a bounded
continuous function. -/
def parametricPolynomialBoundaryFunction
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (q : Polynomial ℂ) : i →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ Polynomial.eval (Gamma.point x) q,
      q.continuous.comp Gamma.point.continuous⟩

omit [MeasurableSpace i] [OpensMeasurableSpace i] in
@[simp]
theorem parametricPolynomialBoundaryFunction_apply
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (q : Polynomial ℂ) (x : i) :
    parametricPolynomialBoundaryFunction Gamma q x =
      Polynomial.eval (Gamma.point x) q := rfl

/-- The manuscript's unit bound on the closed domain restricts to a contractive boundary
function because every parametrized point lies in the frontier, hence in the closure. -/
def parametricContractivePolynomialBoundaryFunction
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (q : Polynomial ℂ)
    (hq : ∀ z ∈ closure Omega, ‖Polynomial.eval z q‖ ≤ 1) :
    ContractiveBoundaryFunction i where
  function := parametricPolynomialBoundaryFunction Gamma q
  norm_le_one x := hq (Gamma.point x)
    (frontier_subset_closure (Gamma.supported x).boundary_point)

omit [Nonempty n] in
theorem integrable_parametricPolynomialFirstPart
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (q : Polynomial ℂ) :
    Integrable (fun x ↦ Polynomial.eval (Gamma.point x) q •
      parametricBoundaryFirstPart Gamma B x) mu := by
  apply integrable_of_continuous_compact
  exact (q.continuous.comp Gamma.point.continuous).smul
    (continuous_parametricBoundaryFirstPart Gamma B hWB)

/-- The positive boundary density obtained from the supported parametrization.  Its mass
identity is derived from the constant-polynomial instance of the Cauchy formula, rather than
stored as independent boundary data. -/
def parametricPositiveBoundaryDensity
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B) :
    PositiveBoundaryDensity (n := n) mu where
  density := parametricDoubleLayerDensity Gamma B
  integrable_density := integrable_parametricDoubleLayerDensity Gamma B hWB
  posSemidef_ae := Filter.Eventually.of_forall
    (parametricDoubleLayerDensity_posSemidef Gamma B hWB)
  mass_eq_two_one := by
    have hfirst := integrable_parametricBoundaryFirstPart
      (mu := mu) Gamma B hWB
    have hadjoint : Integrable
        (fun x ↦ (parametricBoundaryFirstPart Gamma B x)ᴴ) mu :=
      integrable_of_continuous_compact
        (continuous_parametricBoundaryFirstPart Gamma B hWB).matrix_conjTranspose
    have hfirstMass :
        ∫ x, parametricBoundaryFirstPart Gamma B x ∂mu =
          (1 : SquareMatrix n) := by
      simpa [polynomialEval] using hCauchy (1 : Polynomial ℂ)
    rw [show (fun x ↦ parametricDoubleLayerDensity Gamma B x) =
        fun x ↦ parametricBoundaryFirstPart Gamma B x +
          (parametricBoundaryFirstPart Gamma B x)ᴴ by
      rfl]
    rw [integral_add hfirst hadjoint, ← conjTranspose_integral hfirst,
      hfirstMass, Matrix.conjTranspose_one]
    module

/-- The companion transform for an arbitrary bounded continuous boundary function. -/
def parametricBoundaryCompanion
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n) (h : i →ᵇ ℂ) : SquareMatrix n :=
  ∫ x, star (h x) • parametricBoundaryFirstPart Gamma B x ∂mu

omit [Nonempty n] in
theorem integrable_parametricBoundaryCompanion
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) (h : i →ᵇ ℂ) :
    Integrable (fun x ↦ star (h x) • parametricBoundaryFirstPart Gamma B x) mu := by
  apply integrable_of_continuous_compact
  exact h.continuous.star.smul (continuous_parametricBoundaryFirstPart Gamma B hWB)

omit [Nonempty n] in
/-- The companion lies in the algebra generated by the auxiliary matrix. -/
theorem parametricBoundaryCompanion_mem_generatedAlgebra
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega) (h : i →ᵇ ℂ) :
    parametricBoundaryCompanion Gamma mu B h ∈ generatedAlgebra B := by
  apply generatedAlgebra_integral_mem B
    (integrable_parametricBoundaryCompanion Gamma B hWB h)
  exact Filter.Eventually.of_forall fun x ↦ by
    have hres : parametricBoundaryResolvent Gamma B x ∈ generatedAlgebra B := by
      apply resolvent_mem_generatedAlgebra_of_numericalRange_subset B hWB
      exact (Gamma.supported x).sigma_not_mem
    have hnormal := (generatedAlgebra B).smul_mem hres (Gamma.normal x)
    have hfirst : parametricBoundaryFirstPart Gamma B x ∈ generatedAlgebra B := by
      exact ((generatedAlgebra B).toSubmodule.restrictScalars ℝ).smul_mem
        ((2 * Real.pi : ℝ)⁻¹ * Gamma.speed x) hnormal
    exact (generatedAlgebra B).smul_mem hfirst (star (h x))

omit [Nonempty n] in
/-- Generic double-layer identity: the analytic half is supplied by a Cauchy evaluation and the
second half is the adjoint of the companion. -/
theorem two_smul_boundaryPhi_parametric_eq
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B)
    (h : i →ᵇ ℂ) (hB : SquareMatrix n)
    (hCauchyValue :
      ∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu = hB) :
    (2 : ℂ) • boundaryPhiCLM
        (parametricPositiveBoundaryDensity Gamma B hWB hCauchy) h =
      hB + (parametricBoundaryCompanion Gamma mu B h)ᴴ := by
  let first : i → SquareMatrix n := parametricBoundaryFirstPart Gamma B
  have hfirst : Integrable (fun x ↦ h x • first x) mu := by
    apply integrable_of_continuous_compact
    exact h.continuous.smul (continuous_parametricBoundaryFirstPart Gamma B hWB)
  have hcompanion : Integrable (fun x ↦ star (h x) • first x) mu :=
    integrable_parametricBoundaryCompanion Gamma B hWB h
  have hsecond : Integrable (fun x ↦ h x • (first x)ᴴ) mu := by
    apply integrable_of_continuous_compact
    exact h.continuous.smul
      (continuous_parametricBoundaryFirstPart Gamma B hWB).matrix_conjTranspose
  have hsecondIntegral :
      ∫ x, h x • (first x)ᴴ ∂mu =
        (parametricBoundaryCompanion Gamma mu B h)ᴴ := by
    rw [parametricBoundaryCompanion, conjTranspose_integral hcompanion]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [Matrix.conjTranspose_smul, star_star]
  rw [boundaryPhiCLM_apply, boundaryPhi]
  simp only [smul_smul]
  rw [show (2 : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, one_smul]
  change (∫ x, h x • (first x + (first x)ᴴ) ∂mu) = _
  rw [show (fun x ↦ h x • (first x + (first x)ᴴ)) =
      fun x ↦ h x • first x + h x • (first x)ᴴ by
    funext x
    exact smul_add _ _ _]
  rw [integral_add hfirst hsecond, hCauchyValue, hsecondIntegral]

/-- The polynomial Cauchy formula extends to the Cayley boundary function by uniform convergence. -/
theorem parametricBoundaryFirstPartIntegral_cayley_eq
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B)
    (q : Polynomial ℂ)
    (hq : ∀ w ∈ closure Omega, ‖Polynomial.eval w q‖ ≤ 1)
    (z : ℂ) (hz : z ∈ unitDisk) :
    (∫ x, cayleyBoundaryFunction z
          (by simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz)
          (parametricContractivePolynomialBoundaryFunction Gamma q hq) x •
        parametricBoundaryFirstPart Gamma B x ∂mu) =
      matrixCayleyTransform z (polynomialEval q B) := by
  let f := parametricContractivePolynomialBoundaryFunction Gamma q hq
  let L := parametricBoundaryFirstPartIntegralCLM (mu := mu) Gamma B hWB
  have hznorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hmapped := (cayleyBoundarySeriesTerm_hasSum z hznorm f).mapL L
  have hspectrumB : matrixSpectrum B ⊆ closure Omega := by
    intro w hw
    exact subset_closure (hWB (matrixSpectrum_subset_numericalRange B hw))
  have hspectrumT : matrixSpectrum (polynomialEval q B) ⊆ closedUnitDisk :=
    matrixSpectrum_polynomialEval_subset_closedUnitDisk B q (closure Omega) hspectrumB hq
  have hmatrix := matrixCayleySeriesTerm_hasSum (polynomialEval q B) hspectrumT hz
  have heq :
      (fun m ↦ L (cayleyBoundarySeriesTerm z f m)) =
        matrixCayleySeriesTerm z (polynomialEval q B) := by
    funext m
    cases m with
    | zero =>
        change (∫ x, (1 : ℂ) • parametricBoundaryFirstPart Gamma B x ∂mu) = 1
        simpa [polynomialEval] using hCauchy (1 : Polynomial ℂ)
    | succ m =>
        have hboundaryPower :
            f.function ^ (m + 1) =
              parametricPolynomialBoundaryFunction Gamma (q ^ (m + 1)) := by
          ext x
          simp [f, parametricContractivePolynomialBoundaryFunction,
            parametricPolynomialBoundaryFunction, Polynomial.eval_pow]
        change L ((2 * z ^ (m + 1)) • (f.function ^ (m + 1))) =
          (2 * z ^ (m + 1)) • polynomialEval q B ^ (m + 1)
        rw [map_smul, hboundaryPower]
        change (2 * z ^ (m + 1)) •
            (∫ x, Polynomial.eval (Gamma.point x) (q ^ (m + 1)) •
              parametricBoundaryFirstPart Gamma B x ∂mu) = _
        rw [hCauchy (q ^ (m + 1))]
        simp [polynomialEval]
  rw [heq] at hmapped
  exact hmapped.unique hmatrix

/-- The companion associated with the full Cayley boundary function. -/
noncomputable def parametricCayleyCompanion
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n)
    (q : Polynomial ℂ)
    (hq : ∀ w ∈ closure Omega, ‖Polynomial.eval w q‖ ≤ 1)
    (z : ℂ) : SquareMatrix n := by
  classical
  exact if hz : z ∈ unitDisk then
    parametricBoundaryCompanion Gamma mu B
      (cayleyBoundaryFunction z
        (by simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz)
        (parametricContractivePolynomialBoundaryFunction Gamma q hq))
  else 0

omit [Nonempty n] in
theorem parametricCayleyCompanion_mem_generatedAlgebra
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (q : Polynomial ℂ)
    (hq : ∀ w ∈ closure Omega, ‖Polynomial.eval w q‖ ≤ 1)
    (z : ℂ) (hz : z ∈ unitDisk) :
    parametricCayleyCompanion Gamma mu B q hq z ∈ generatedAlgebra B := by
  rw [parametricCayleyCompanion, dif_pos hz]
  exact parametricBoundaryCompanion_mem_generatedAlgebra Gamma B hWB _

/-- The full double-layer identity in direct Cayley form. -/
theorem parametric_direct_cayley_identity
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B)
    (q : Polynomial ℂ)
    (hq : ∀ w ∈ closure Omega, ‖Polynomial.eval w q‖ ≤ 1)
    (z : ℂ) (hz : z ∈ unitDisk) :
    (2 : ℂ) • doubleLayerCayleySeries
        (parametricPositiveBoundaryDensity Gamma B hWB hCauchy)
        (parametricContractivePolynomialBoundaryFunction Gamma q hq) z =
      matrixCayleyTransform z (polynomialEval q B) +
        (parametricCayleyCompanion Gamma mu B q hq z)ᴴ := by
  have hznorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  rw [doubleLayerCayleySeries_eq_value
    (parametricPositiveBoundaryDensity Gamma B hWB hCauchy)
    (parametricContractivePolynomialBoundaryFunction Gamma q hq) z hznorm]
  rw [parametricCayleyCompanion, dif_pos hz]
  exact two_smul_boundaryPhi_parametric_eq Gamma B hWB hCauchy _ _
    (parametricBoundaryFirstPartIntegral_cayley_eq Gamma B hWB hCauchy q hq z hz)

/-- A supported compact parametrization satisfying the explicit polynomial Cauchy integral
constructs the direct Cayley completion on the closed domain. -/
theorem hasDoubleLayerCompletionProvider_of_parametricBoundary
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B) :
    HasDoubleLayerCompletionProvider B (closure Omega) := by
  intro q hq
  let D : PositiveBoundaryDensity (n := n) mu :=
    parametricPositiveBoundaryDensity Gamma B hWB hCauchy
  let f : ContractiveBoundaryFunction i :=
    parametricContractivePolynomialBoundaryFunction Gamma q hq
  let g : ℂ → SquareMatrix n :=
    parametricCayleyCompanion Gamma mu B q hq
  refine ⟨doubleLayerCayleySeries D f, ?_⟩
  have hspectrumB : matrixSpectrum B ⊆ closure Omega := by
    intro z hz
    exact subset_closure (hWB (matrixSpectrum_subset_numericalRange B hz))
  apply isPositiveRealCompletion_of_direct_cayley_identity
    B (polynomialEval q B) (doubleLayerCayleySeries D f) g
  · exact matrixSpectrum_polynomialEval_subset_closedUnitDisk
      B q (closure Omega) hspectrumB hq
  · exact doubleLayerCayleySeries_analyticOnNhd D f
  · exact doubleLayerCayleySeries_zero D f
  · exact doubleLayerCayleySeries_rePart_posSemidef D f
  · intro z hz
    exact parametricCayleyCompanion_mem_generatedAlgebra Gamma B hWB q hq z hz
  · intro z hz
    exact parametric_direct_cayley_identity Gamma B hWB hCauchy q hq z hz

end CrouzeixConjecture
