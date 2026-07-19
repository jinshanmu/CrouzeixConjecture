module

public import CrouzeixConjecture.DoubleLayerProvider
public import CrouzeixConjecture.HolomorphicMatrixAlgebra
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

/-- The anti-analytic companion transform evaluated at `B`, written directly as the
pulled-back boundary integral from manuscript equation (304). -/
def parametricPolynomialCompanion
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n) (q : Polynomial ℂ) :
    SquareMatrix n :=
  ∫ x, star (Polynomial.eval (Gamma.point x) q) •
    parametricBoundaryFirstPart Gamma B x ∂mu

omit [Nonempty n] in
theorem integrable_parametricPolynomialCompanion
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (q : Polynomial ℂ) :
    Integrable (fun x ↦ star (Polynomial.eval (Gamma.point x) q) •
      parametricBoundaryFirstPart Gamma B x) mu := by
  apply integrable_of_continuous_compact
  exact (q.continuous.comp Gamma.point.continuous).star.smul
    (continuous_parametricBoundaryFirstPart Gamma B hWB)

omit [Nonempty n] in
/-- The companion integral belongs to the generated algebra because every resolvent does,
and finite-dimensional generated algebras are closed under Bochner integration. -/
theorem parametricPolynomialCompanion_mem_generatedAlgebra
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (q : Polynomial ℂ) :
    parametricPolynomialCompanion Gamma mu B q ∈ generatedAlgebra B := by
  apply generatedAlgebra_integral_mem B
    (integrable_parametricPolynomialCompanion Gamma B hWB q)
  exact Filter.Eventually.of_forall fun x ↦ by
    have hres : parametricBoundaryResolvent Gamma B x ∈ generatedAlgebra B := by
      apply resolvent_mem_generatedAlgebra_of_numericalRange_subset B hWB
      exact (Gamma.supported x).sigma_not_mem
    have hnormal := (generatedAlgebra B).smul_mem hres (Gamma.normal x)
    have hfirst : parametricBoundaryFirstPart Gamma B x ∈ generatedAlgebra B := by
      exact
        ((generatedAlgebra B).toSubmodule.restrictScalars ℝ).smul_mem
          ((2 * Real.pi : ℝ)⁻¹ * Gamma.speed x) hnormal
    exact (generatedAlgebra B).smul_mem hfirst
      (star (Polynomial.eval (Gamma.point x) q))

omit [Nonempty n] in
/-- Parametric form of manuscript equation (308).  Cauchy's formula evaluates the analytic
half, while the second half is exactly the adjoint of the explicitly defined companion
integral. -/
theorem two_smul_boundaryPhi_parametricPolynomial_eq
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B)
    (q : Polynomial ℂ) :
    (2 : ℂ) • boundaryPhiCLM
        (parametricPositiveBoundaryDensity Gamma B hWB hCauchy)
        (parametricPolynomialBoundaryFunction Gamma q) =
      polynomialEval q B + (parametricPolynomialCompanion Gamma mu B q)ᴴ := by
  let first : i → SquareMatrix n := parametricBoundaryFirstPart Gamma B
  have hfirst : Integrable
      (fun x ↦ Polynomial.eval (Gamma.point x) q • first x) mu :=
    integrable_parametricPolynomialFirstPart Gamma B hWB q
  have hcompanion : Integrable
      (fun x ↦ star (Polynomial.eval (Gamma.point x) q) • first x) mu :=
    integrable_parametricPolynomialCompanion Gamma B hWB q
  have hsecond : Integrable
      (fun x ↦ Polynomial.eval (Gamma.point x) q • (first x)ᴴ) mu := by
    apply integrable_of_continuous_compact
    exact (q.continuous.comp Gamma.point.continuous).smul
      (continuous_parametricBoundaryFirstPart Gamma B hWB).matrix_conjTranspose
  have hsecondIntegral :
      ∫ x, Polynomial.eval (Gamma.point x) q • (first x)ᴴ ∂mu =
        (parametricPolynomialCompanion Gamma mu B q)ᴴ := by
    rw [parametricPolynomialCompanion, conjTranspose_integral hcompanion]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      simp only [Matrix.conjTranspose_smul, star_star]
  rw [boundaryPhiCLM_apply, boundaryPhi]
  simp only [smul_smul]
  rw [show (2 : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, one_smul]
  change
    (∫ x, Polynomial.eval (Gamma.point x) q •
      (first x + (first x)ᴴ) ∂mu) = _
  rw [show (fun x ↦ Polynomial.eval (Gamma.point x) q •
      (first x + (first x)ᴴ)) =
      fun x ↦ Polynomial.eval (Gamma.point x) q • first x +
        Polynomial.eval (Gamma.point x) q • (first x)ᴴ by
    funext x
    exact smul_add _ _ _]
  rw [integral_add hfirst hsecond, hCauchy q, hsecondIntegral]

omit [Nonempty n] in
/-- Every positive Cayley coefficient has exactly the manuscript's polynomial-plus-companion
form.  This is the coefficient hypothesis previously exposed by `DoubleLayerProvider`; here it
is a theorem derived from the parametric Cauchy formula. -/
theorem parametricDoubleLayerCayleySeriesCoefficient_succ
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B)
    (q : Polynomial ℂ)
    (hq : ∀ z ∈ closure Omega, ‖Polynomial.eval z q‖ ≤ 1)
    (m : ℕ) :
    doubleLayerCayleySeriesCoefficient
        (parametricPositiveBoundaryDensity Gamma B hWB hCauchy)
        (parametricContractivePolynomialBoundaryFunction Gamma q hq)
        (m + 1) =
      polynomialEval q B ^ (m + 1) +
        (parametricPolynomialCompanion Gamma mu B (q ^ (m + 1)))ᴴ := by
  have hboundaryPower :
      (parametricContractivePolynomialBoundaryFunction Gamma q hq).function ^
          (m + 1) =
        parametricPolynomialBoundaryFunction Gamma (q ^ (m + 1)) := by
    ext x
    simp [parametricContractivePolynomialBoundaryFunction,
      parametricPolynomialBoundaryFunction, Polynomial.eval_pow]
  change
    (2 : ℂ) • boundaryPhiCLM
        (parametricPositiveBoundaryDensity Gamma B hWB hCauchy)
        ((parametricContractivePolynomialBoundaryFunction Gamma q hq).function ^
          (m + 1)) = _
  rw [hboundaryPower,
    two_smul_boundaryPhi_parametricPolynomial_eq Gamma B hWB hCauchy]
  simp [polynomialEval]

/-- A supported compact parametrization satisfying the explicit polynomial Cauchy integral
constructs the complete double-layer provider on the closed domain.  All positivity, mass,
boundedness, companion, coefficient, and generated-algebra obligations are discharged here. -/
theorem hasDoubleLayerCompletionProvider_of_parametricBoundary
    [IsFiniteMeasure (mu : Measure i)]
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hCauchy : HasParametricPolynomialCauchyFormula Gamma mu B) :
    HasDoubleLayerCompletionProvider B (closure Omega) := by
  have hspectrum : matrixSpectrum B ⊆ closure Omega := by
    intro z hz
    exact subset_closure (hWB (matrixSpectrum_subset_numericalRange B hz))
  let D : PositiveBoundaryDensity (n := n) mu :=
    parametricPositiveBoundaryDensity Gamma B hWB hCauchy
  let boundaryFunction : ∀ (q : Polynomial ℂ),
      (∀ z ∈ closure Omega, ‖Polynomial.eval z q‖ ≤ 1) →
        ContractiveBoundaryFunction i :=
    fun q hq ↦ parametricContractivePolynomialBoundaryFunction Gamma q hq
  let companion : ∀ (q : Polynomial ℂ)
      (_hq : ∀ z ∈ closure Omega, ‖Polynomial.eval z q‖ ≤ 1),
      ℕ → SquareMatrix n :=
    fun q _ m ↦ parametricPolynomialCompanion Gamma mu B (q ^ m)
  apply hasDoubleLayerCompletionProvider_of_boundary_data
    B (closure Omega) hspectrum D boundaryFunction companion
  · intro q hq m
    exact parametricPolynomialCompanion_mem_generatedAlgebra
      Gamma B hWB (q ^ (m + 1))
  · intro q hq m
    exact parametricDoubleLayerCayleySeriesCoefficient_succ
      Gamma B hWB hCauchy q hq m

end CrouzeixConjecture
