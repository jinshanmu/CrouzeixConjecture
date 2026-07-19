module

public import CrouzeixConjecture.DoubleLayerIntegration
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Bounded.Star

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] [Fintype n] [DecidableEq n]

/-- The exact measure-theoretic hypotheses on the positive operator-valued boundary
density.  Integrability is stated explicitly.  Positive semidefiniteness includes
Hermitian symmetry, so no separate (and redundant) Hermitian hypothesis is imposed.
The mass identity is the normalisation in manuscript equation (289). -/
structure PositiveBoundaryDensity (mu : Measure i) where
  density : i → SquareMatrix n
  integrable_density : Integrable density mu
  posSemidef_ae : ∀ᵐ x ∂mu, (density x).PosSemidef
  mass_eq_two_one : ∫ x, density x ∂mu = (2 : ℂ) • (1 : SquareMatrix n)

variable {mu : Measure i}

/-- Multiplication of an integrable density by a bounded continuous scalar function
is integrable.  This is the only integrability input needed to define `boundaryPhi`. -/
theorem PositiveBoundaryDensity.integrable_smul
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    Integrable (fun x ↦ h x • D.density x) mu := by
  simpa only [Pi.smul_apply] using
    D.integrable_density.bdd_smul (φ := fun x ↦ h x) ‖h‖
      h.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ h.norm_coe_le_norm x)

/-- The positive operator-valued boundary map from manuscript equation (292), on
the Banach algebra of bounded continuous complex boundary functions. -/
def boundaryPhi (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    SquareMatrix n :=
  (2 : ℂ)⁻¹ • ∫ x, h x • D.density x ∂mu

/-- Complex linearity of the boundary map. -/
def boundaryPhiLinear (D : PositiveBoundaryDensity (n := n) mu) :
    (i →ᵇ ℂ) →ₗ[ℂ] SquareMatrix n where
  toFun := boundaryPhi D
  map_add' h g := by
    simp only [boundaryPhi, BoundedContinuousFunction.add_apply, add_smul,
      integral_add (D.integrable_smul h) (D.integrable_smul g), smul_add]
  map_smul' c h := by
    simp only [boundaryPhi, BoundedContinuousFunction.smul_apply]
    have hfun :
        (fun x ↦ (c • h x) • D.density x) =
          fun x ↦ c • (h x • D.density x) := by
      funext x
      change (c * h x) • D.density x = c • (h x • D.density x)
      rw [smul_smul]
    rw [hfun, integral_smul]
    simp only [smul_smul, RingHom.id_apply]
    ring_nf

/-- A concrete continuity bound for `boundaryPhi`.  It records that the map uses
only the Bochner integrability of the density, rather than finite boundary measure. -/
theorem boundaryPhi_norm_le
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    ‖boundaryPhi D h‖ ≤
      ((2 : ℝ)⁻¹ * ∫ x, ‖D.density x‖ ∂mu) * ‖h‖ := by
  have hpoint : ∀ x, ‖h x • D.density x‖ ≤ ‖h‖ * ‖D.density x‖ := by
    intro x
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm x) (norm_nonneg _)
  calc
    ‖boundaryPhi D h‖ = (2 : ℝ)⁻¹ * ‖∫ x, h x • D.density x ∂mu‖ := by
      rw [boundaryPhi, norm_smul]
      norm_num
    _ ≤ (2 : ℝ)⁻¹ * ∫ x, ‖h x • D.density x‖ ∂mu := by
      exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
        (by positivity)
    _ ≤ (2 : ℝ)⁻¹ * ∫ x, ‖h‖ * ‖D.density x‖ ∂mu := by
      exact mul_le_mul_of_nonneg_left
        (integral_mono_ae (D.integrable_smul h).norm
          (D.integrable_density.norm.const_mul ‖h‖)
          (Filter.Eventually.of_forall hpoint))
        (by positivity)
    _ = ((2 : ℝ)⁻¹ * ∫ x, ‖D.density x‖ ∂mu) * ‖h‖ := by
      rw [integral_const_mul]
      ring

/-- The bundled continuous complex-linear boundary map. -/
def boundaryPhiCLM (D : PositiveBoundaryDensity (n := n) mu) :
    (i →ᵇ ℂ) →L[ℂ] SquareMatrix n :=
  (boundaryPhiLinear D).mkContinuous
    ((2 : ℝ)⁻¹ * ∫ x, ‖D.density x‖ ∂mu)
    (boundaryPhi_norm_le D)

@[simp]
theorem boundaryPhiCLM_apply
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    boundaryPhiCLM D h = boundaryPhi D h := rfl

/-- The mass identity makes the boundary map unital. -/
@[simp]
theorem boundaryPhi_one (D : PositiveBoundaryDensity (n := n) mu) :
    boundaryPhiCLM D (1 : i →ᵇ ℂ) = 1 := by
  rw [boundaryPhiCLM_apply, boundaryPhi]
  change (2 : ℂ)⁻¹ • ∫ x, (1 : ℂ) • D.density x ∂mu = 1
  simp only [one_smul, D.mass_eq_two_one]
  rw [smul_smul]
  norm_num

omit [TopologicalSpace i] [OpensMeasurableSpace i] in
/-- Positive-semidefinite densities are Hermitian almost everywhere. -/
theorem PositiveBoundaryDensity.isHermitian_ae
    (D : PositiveBoundaryDensity (n := n) mu) :
    ∀ᵐ x ∂mu, (D.density x).IsHermitian :=
  D.posSemidef_ae.mono fun _ hx ↦ hx.1

/-- The boundary map intertwines scalar conjugation with matrix conjugate transpose. -/
theorem boundaryPhi_star
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    boundaryPhiCLM D (star h) = (boundaryPhiCLM D h)ᴴ := by
  have hcongr : ∀ᵐ x ∂mu,
      (star h) x • D.density x = (h x • D.density x)ᴴ := by
    filter_upwards [D.isHermitian_ae] with x hx
    simp only [BoundedContinuousFunction.star_apply, Matrix.conjTranspose_smul, hx.eq]
  have hint := D.integrable_smul h
  rw [boundaryPhiCLM_apply, boundaryPhiCLM_apply, boundaryPhi,
    boundaryPhi, integral_congr_ae hcongr, ← conjTranspose_integral hint]
  simp only [Matrix.conjTranspose_smul]
  norm_num

/-- The real part of a bounded continuous scalar boundary function, still regarded
as a complex-valued boundary function. -/
def boundaryRealPart (h : i →ᵇ ℂ) : i →ᵇ ℂ :=
  (2 : ℂ)⁻¹ • (h + star h)

omit [MeasurableSpace i] [OpensMeasurableSpace i] in
@[simp]
theorem boundaryRealPart_apply (h : i →ᵇ ℂ) (x : i) :
    boundaryRealPart h x = ((h x).re : ℂ) := by
  apply Complex.ext
  · norm_num [boundaryRealPart]
    ring
  · norm_num [boundaryRealPart]

/-- Taking the matrix real part after `boundaryPhi` is the same as first taking the
pointwise scalar real part. -/
theorem rePart_boundaryPhi
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ) :
    rePart (boundaryPhiCLM D h) = boundaryPhiCLM D (boundaryRealPart h) := by
  rw [boundaryRealPart, map_smul, map_add, boundaryPhi_star]
  simp only [rePart]

/-- Positivity of `boundaryPhi` on pointwise nonnegative real scalar functions. -/
theorem boundaryPhi_posSemidef
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ)
    (hreal : ∀ x, (h x).im = 0) (hnonneg : ∀ x, 0 ≤ (h x).re) :
    (boundaryPhiCLM D h).PosSemidef := by
  have hpositive : ∀ᵐ x ∂mu, (h x • D.density x).PosSemidef := by
    filter_upwards [D.posSemidef_ae] with x hx
    have hh : h x = ((h x).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hreal x
    rw [hh]
    have hs := hx.smul (hnonneg x)
    simpa only [Complex.real_smul] using hs
  have hintegral := integral_posSemidef_of_ae hpositive
  rw [boundaryPhiCLM_apply, boundaryPhi]
  have hhalf := hintegral.smul (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
  have heq :
      ((2 : ℂ)⁻¹) • (∫ x, h x • D.density x ∂mu) =
        ((2 : ℝ)⁻¹) • (∫ x, h x • D.density x ∂mu) := by
    ext a b
    norm_num [Complex.real_smul]
  rw [heq]
  exact hhalf

/-- A convenient positivity law for arbitrary boundary functions with nonnegative
real part. -/
theorem rePart_boundaryPhi_posSemidef
    (D : PositiveBoundaryDensity (n := n) mu) (h : i →ᵇ ℂ)
    (hRe : ∀ x, 0 ≤ (h x).re) :
    (rePart (boundaryPhiCLM D h)).PosSemidef := by
  rw [rePart_boundaryPhi]
  apply boundaryPhi_posSemidef D (boundaryRealPart h)
  · intro x
    simp
  · intro x
    simpa using hRe x

end CrouzeixConjecture
