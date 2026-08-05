module

public import CrouzeixConjecture.HolomorphicRadialContour
public import CrouzeixConjecture.PerturbationInsideDomain
public import CrouzeixConjecture.SimpleSpectrumBridge
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexOrder Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {i n : Type*} [TopologicalSpace i] [CompactSpace i]
  [MeasurableSpace i] [OpensMeasurableSpace i]
  [Fintype n] [DecidableEq n] [Nonempty n]
  {mu : Measure i} [IsFiniteMeasure mu] {Omega : Set ℂ}

/-- Integration against the analytic half of a supported parametrized boundary density.
It becomes the normalized holomorphic functional-calculus value only for the oriented radial
boundary and parameter measure used below. -/
def parametricBoundaryIntegral
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (f : ℂ → ℂ) (B : SquareMatrix n) : SquareMatrix n :=
  ∫ x, f (Gamma.point x) • parametricBoundaryFirstPart Gamma B x ∂mu

omit [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
private theorem continuousOn_parametricBoundaryFirstPart_uncurry
    (Gamma : ParametricConvexBoundary (i := i) Omega) :
    ContinuousOn
      (fun p : SquareMatrix n × i ↦
        parametricBoundaryFirstPart Gamma p.1 p.2)
      ({B : SquareMatrix n | numericalRange B ⊆ Omega} ×ˢ (Set.univ : Set i)) := by
  intro p hp
  have hmatrix : Continuous
      (fun q : SquareMatrix n × i ↦
        Gamma.point q.2 • (1 : SquareMatrix n) - q.1) := by
    fun_prop
  have hunit := scalar_sub_matrix_isUnit_of_outwardBoundarySupport
    (Gamma.supported p.2) p.1 hp.1
  have hdet : IsUnit
      (Gamma.point p.2 • (1 : SquareMatrix n) - p.1).det :=
    (Gamma.point p.2 • (1 : SquareMatrix n) - p.1).isUnit_iff_isUnit_det.mp hunit
  have hinverse : ContinuousAt Ring.inverse
      (Gamma.point p.2 • (1 : SquareMatrix n) - p.1).det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet.ne_zero
  have hinverseMatrix : ContinuousAt
      (Inv.inv : SquareMatrix n → SquareMatrix n)
      (Gamma.point p.2 • (1 : SquareMatrix n) - p.1) :=
    continuousAt_matrix_inv _ hinverse
  have hresolvent : ContinuousAt
      (fun q : SquareMatrix n × i ↦
        (Gamma.point q.2 • (1 : SquareMatrix n) - q.1)⁻¹) p :=
    hinverseMatrix.comp'
      (f := fun q : SquareMatrix n × i ↦
        Gamma.point q.2 • (1 : SquareMatrix n) - q.1)
      hmatrix.continuousAt
  have hspeed : ContinuousAt
      (fun q : SquareMatrix n × i ↦
        (2 * Real.pi : ℝ)⁻¹ * Gamma.speed q.2) p := by
    fun_prop
  have hnormal : ContinuousAt
      (fun q : SquareMatrix n × i ↦ Gamma.normal q.2) p := by
    fun_prop
  change ContinuousWithinAt
    (fun q : SquareMatrix n × i ↦
      ((2 * Real.pi : ℝ)⁻¹ * Gamma.speed q.2) •
        (Gamma.normal q.2 •
          (Gamma.point q.2 • (1 : SquareMatrix n) - q.1)⁻¹))
    ({B : SquareMatrix n | numericalRange B ⊆ Omega} ×ˢ Set.univ) p
  exact (hspeed.smul (hnormal.smul hresolvent)).continuousWithinAt

omit [Nonempty n] in
/-- For a fixed compact supported contour, holomorphic evaluation depends continuously on
the matrix as long as its numerical range remains in the supported domain.  Only continuity
of the scalar function on the closed domain is used in this step. -/
theorem continuousOn_parametricBoundaryIntegral
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (f : ℂ → ℂ) (hf : ContinuousOn f (closure Omega)) :
    ContinuousOn (parametricBoundaryIntegral Gamma mu f)
      {B : SquareMatrix n | numericalRange B ⊆ Omega} := by
  apply continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
  · have hpoint : MapsTo
        (fun p : SquareMatrix n × i ↦ Gamma.point p.2)
        ({B : SquareMatrix n | numericalRange B ⊆ Omega} ×ˢ Set.univ)
        (closure Omega) := by
      intro p hp
      exact frontier_subset_closure (Gamma.supported p.2).boundary_point
    have hscalar : ContinuousOn
        (fun p : SquareMatrix n × i ↦ f (Gamma.point p.2))
        ({B : SquareMatrix n | numericalRange B ⊆ Omega} ×ˢ Set.univ) :=
      hf.comp (Gamma.point.continuous.comp continuous_snd).continuousOn hpoint
    simpa [Function.uncurry_def, parametricBoundaryIntegral] using
      hscalar.smul (continuousOn_parametricBoundaryFirstPart_uncurry Gamma)
  · intro B x hB hx
    exact (hx (Set.mem_univ x)).elim

namespace PositivePeriodicRadialData
namespace OrientedRadialConvexBoundary

omit [Nonempty n] in
/-- On an oriented radial boundary, normalized parametric evaluation agrees with the
simple-diagonalization holomorphic functional calculus. -/
theorem parametricBoundaryIntegral_eq_functionEval
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    parametricBoundaryIntegral (G.parametricBoundary R c)
        contourParameterMeasure f B =
      hB.functionEval f := by
  let k : ℂ := -Complex.I * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)
  let F : ℝ → SquareMatrix n := fun t ↦
    k • (f (R.point c t) •
      (R.tangent t • doubleLayerResolvent B (R.point c t)))
  have hboundary : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
      R.point c t ∈ closure Omega := by
    intro t ht
    exact frontier_subset_closure (G.supported t ht).boundary_point
  have hbase :=
    G.domain.integral_holomorphic_cauchy_resolvent_of_simpleDiagonalization
      R c hVopen hVconvex hclosure hboundary hf B hB hWB
  calc
    parametricBoundaryIntegral (G.parametricBoundary R c)
        contourParameterMeasure f B =
        ∫ x : ContourParameter, F x.1 ∂contourParameterMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change f (R.point c x.1) •
            parametricBoundaryFirstPart (G.parametricBoundary R c) B x = F x.1
        rw [G.parametricBoundaryFirstPart_eq_cauchyIntegrand R c B x]
        ext a b
        simp [F, k, parametricBoundaryResolvent, smul_smul]
        ring
    _ = ∫ t in (0 : ℝ)..contourPeriod, F t :=
      integral_contourParameter_eq_intervalIntegral F
    _ = k • (∫ t in (0 : ℝ)..contourPeriod,
        f (R.point c t) •
          (R.tangent t • doubleLayerResolvent B (R.point c t))) := by
      exact intervalIntegral.integral_smul k _
    _ = k • (((contourPeriod : ℂ) * Complex.I) • hB.functionEval f) := by
      rw [hbase]
    _ = hB.functionEval f := by
      rw [smul_smul, cauchyNormalization_mul_period_I, one_smul]

end OrientedRadialConvexBoundary
end PositivePeriodicRadialData

/-- The simple-spectrum functional-calculus sequence used to extend a fixed contour
evaluation to an arbitrary finite matrix. -/
def simpleSpectrumHolomorphicEval
    (A : SquareMatrix n) (f : ℂ → ℂ) (k : ℕ) : SquareMatrix n :=
  (simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)).functionEval f

/-- A fixed supported contour evaluates the concrete simple-spectrum approximants
continuously at the original matrix. -/
theorem tendsto_parametricBoundaryIntegral_simpleSpectrumApproximation
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (f : ℂ → ℂ) (hf : ContinuousOn f (closure Omega))
    (A : SquareMatrix n) (hOmegaOpen : IsOpen Omega)
    (hWA : numericalRange A ⊆ Omega) :
    Tendsto
      (fun k ↦ parametricBoundaryIntegral Gamma mu f
        (simpleSpectrumApproximation A k)) atTop
      (nhds (parametricBoundaryIntegral Gamma mu f A)) := by
  have hinside : ∀ᶠ k in atTop,
      simpleSpectrumApproximation A k ∈
        {B : SquareMatrix n | numericalRange B ⊆ Omega} :=
    eventually_simpleSpectrumApproximation_numericalRange_subset_open
      A hOmegaOpen hWA
  have hwithin : Tendsto (simpleSpectrumApproximation A) atTop
      (nhdsWithin A {B : SquareMatrix n | numericalRange B ⊆ Omega}) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (simpleSpectrumApproximation A)
      (tendsto_simpleSpectrumApproximation A) hinside
  exact ((continuousOn_parametricBoundaryIntegral Gamma f hf) A hWA).tendsto.comp hwithin

namespace PositivePeriodicRadialData
namespace OrientedRadialConvexBoundary

/-- The common simple-spectrum evaluations converge to the holomorphic evaluation defined
by any fixed admissible oriented radial contour. -/
theorem tendsto_simpleSpectrumHolomorphicEval
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (A : SquareMatrix n) (hWA : numericalRange A ⊆ Omega) :
    Tendsto (simpleSpectrumHolomorphicEval A f) atTop
      (nhds (parametricBoundaryIntegral (G.parametricBoundary R c)
        contourParameterMeasure f A)) := by
  have hcontinuous : ContinuousOn f (closure Omega) :=
    hf.continuousOn.mono hclosure
  have hlimit := tendsto_parametricBoundaryIntegral_simpleSpectrumApproximation
    (mu := contourParameterMeasure) (G.parametricBoundary R c) f hcontinuous A
    G.domain.isOpen_domain hWA
  have hinside :=
    eventually_simpleSpectrumApproximation_numericalRange_subset_open
      A G.domain.isOpen_domain hWA
  have heq :
      (fun k ↦ parametricBoundaryIntegral (G.parametricBoundary R c)
        contourParameterMeasure f (simpleSpectrumApproximation A k)) =ᶠ[atTop]
      simpleSpectrumHolomorphicEval A f := by
    filter_upwards [hinside] with k hk
    exact G.parametricBoundaryIntegral_eq_functionEval
      R c hVopen hVconvex hclosure hf
      (simpleSpectrumApproximation A k)
      (simpleDiagonalization_of_hasDistinctEigenvalues
        (simpleSpectrumApproximation A k)
        (simpleSpectrumApproximation_hasDistinctEigenvalues A k)) hk
  exact hlimit.congr' heq

/-- Two admissible oriented radial contours give the same finite-matrix holomorphic
evaluation.  The proof uses the same concrete simple-spectrum approximants for both
contours, so no Runge or Mergelyan theorem is assumed. -/
theorem parametricBoundaryIntegral_eq_of_two_orientedRadialBoundaries
    (R₁ R₂ : PositivePeriodicRadialData) (c₁ c₂ : ℂ)
    {Omega₁ Omega₂ V₁ V₂ : Set ℂ}
    (G₁ : OrientedRadialConvexBoundary R₁ c₁ Omega₁)
    (G₂ : OrientedRadialConvexBoundary R₂ c₂ Omega₂)
    (hV₁open : IsOpen V₁) (hV₁convex : Convex ℝ V₁)
    (hclosure₁ : closure Omega₁ ⊆ V₁)
    (hV₂open : IsOpen V₂) (hV₂convex : Convex ℝ V₂)
    (hclosure₂ : closure Omega₂ ⊆ V₂)
    {f : ℂ → ℂ} (hf₁ : DifferentiableOn ℂ f V₁)
    (hf₂ : DifferentiableOn ℂ f V₂)
    (A : SquareMatrix n)
    (hWA₁ : numericalRange A ⊆ Omega₁)
    (hWA₂ : numericalRange A ⊆ Omega₂) :
    parametricBoundaryIntegral (G₁.parametricBoundary R₁ c₁)
        contourParameterMeasure f A =
      parametricBoundaryIntegral (G₂.parametricBoundary R₂ c₂)
        contourParameterMeasure f A := by
  have hlimit₁ := G₁.tendsto_simpleSpectrumHolomorphicEval
    R₁ c₁ hV₁open hV₁convex hclosure₁ hf₁ A hWA₁
  have hlimit₂ := G₂.tendsto_simpleSpectrumHolomorphicEval
    R₂ c₂ hV₂open hV₂convex hclosure₂ hf₂ A hWA₂
  exact tendsto_nhds_unique hlimit₁ hlimit₂

end OrientedRadialConvexBoundary
end PositivePeriodicRadialData

end CrouzeixConjecture
