module

public import CrouzeixConjecture.HolomorphicRadialContour
public import CrouzeixConjecture.CompletionDiagonalization

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {i n : Type*} [TopologicalSpace i] [CompactSpace i]
  [MeasurableSpace i] [OpensMeasurableSpace i]
  [Fintype n] [DecidableEq n] [Nonempty n]
  {mu : Measure i} [IsFiniteMeasure mu] {Omega : Set ℂ}

/-- The exact Cauchy data used by the holomorphic double-layer argument.  The
zeroth power is the mass normalization; the positive powers are precisely the
coefficients transported by the Cayley series. -/
def HasParametricPowerCauchyFormula
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n)
    (f : ContractiveBoundaryFunction i) (T : SquareMatrix n) : Prop :=
  ∀ m : ℕ,
    ∫ x, (f.function x) ^ m •
      parametricBoundaryFirstPart Gamma B x ∂mu = T ^ m

omit [CompactSpace i] [OpensMeasurableSpace i] [Nonempty n]
  [IsFiniteMeasure mu] in
/-- The zeroth power Cauchy identity is exactly the mass normalization. -/
theorem HasParametricPowerCauchyFormula.mass_eq_one
    {Gamma : ParametricConvexBoundary (i := i) Omega}
    {B : SquareMatrix n} {f : ContractiveBoundaryFunction i}
    {T : SquareMatrix n}
    (hCauchy : HasParametricPowerCauchyFormula Gamma mu B f T) :
    ∫ x, parametricBoundaryFirstPart Gamma B x ∂mu =
      (1 : SquareMatrix n) := by
  simpa using hCauchy 0

/-- A scalar function bounded by one on the closed domain gives the
contractive boundary function used by the Cayley construction. -/
def parametricContractiveBoundaryFunctionOfContinuousOn
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (f : ℂ → ℂ) (hf : ContinuousOn f (closure Omega))
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ 1) :
    ContractiveBoundaryFunction i where
  function := BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ f (Gamma.point x), by
      rw [← continuousOn_univ]
      simpa only [Function.comp_apply] using
        hf.comp Gamma.point.continuous.continuousOn
          (fun x _ ↦ frontier_subset_closure
            (Gamma.supported x).boundary_point)⟩
  norm_le_one x := hbound (Gamma.point x)
    (frontier_subset_closure (Gamma.supported x).boundary_point)

omit [MeasurableSpace i] [OpensMeasurableSpace i] [Nonempty n] in
@[simp]
theorem parametricContractiveBoundaryFunctionOfContinuousOn_apply
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (f : ℂ → ℂ) (hf : ContinuousOn f (closure Omega))
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ 1) (x : i) :
    (parametricContractiveBoundaryFunctionOfContinuousOn Gamma f hf hbound).function x =
      f (Gamma.point x) := rfl

/-- The positive boundary density normalized by the mass identity. -/
def parametricPositiveBoundaryDensityOfMass
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hmass :
      ∫ x, parametricBoundaryFirstPart Gamma B x ∂mu =
        (1 : SquareMatrix n)) :
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
    rw [show (fun x ↦ parametricDoubleLayerDensity Gamma B x) =
        fun x ↦ parametricBoundaryFirstPart Gamma B x +
          (parametricBoundaryFirstPart Gamma B x)ᴴ by
      rfl]
    rw [integral_add hfirst hadjoint, ← conjTranspose_integral hfirst,
      hmass, Matrix.conjTranspose_one]
    module

/-- The power Cauchy identities transport the uniformly convergent scalar
Cayley series to the matrix Cayley transform. -/
theorem parametricBoundaryFirstPartIntegral_cayley_eq_of_powerCauchy
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (f : ContractiveBoundaryFunction i) (T : SquareMatrix n)
    (hCauchy : HasParametricPowerCauchyFormula Gamma mu B f T)
    (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    (z : ℂ) (hz : z ∈ unitDisk) :
    (∫ x, cayleyBoundaryFunction z
          (by simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz)
          f x • parametricBoundaryFirstPart Gamma B x ∂mu) =
      matrixCayleyTransform z T := by
  let L := parametricBoundaryFirstPartIntegralCLM (mu := mu) Gamma B hWB
  have hznorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hmapped := (cayleyBoundarySeriesTerm_hasSum z hznorm f).mapL L
  have hmatrix := matrixCayleySeriesTerm_hasSum T hspectrum hz
  have heq :
      (fun m ↦ L (cayleyBoundarySeriesTerm z f m)) =
        matrixCayleySeriesTerm z T := by
    funext m
    cases m with
    | zero =>
        change (∫ x, (1 : ℂ) •
          parametricBoundaryFirstPart Gamma B x ∂mu) = 1
        simpa using hCauchy 0
    | succ m =>
        change L ((2 * z ^ (m + 1)) • (f.function ^ (m + 1))) =
          (2 * z ^ (m + 1)) • T ^ (m + 1)
        rw [map_smul]
        change (2 * z ^ (m + 1)) •
            (∫ x, (f.function x) ^ (m + 1) •
              parametricBoundaryFirstPart Gamma B x ∂mu) = _
        rw [hCauchy (m + 1)]
  rw [heq] at hmapped
  exact hmapped.unique hmatrix

/-- The companion for an arbitrary contractive boundary function. -/
def parametricPowerCayleyCompanion
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (mu : Measure i) (B : SquareMatrix n)
    (f : ContractiveBoundaryFunction i) (z : ℂ) : SquareMatrix n := by
  classical
  exact if hz : z ∈ unitDisk then
    parametricBoundaryCompanion Gamma mu B
      (cayleyBoundaryFunction z
        (by simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz) f)
  else 0

omit [Nonempty n] in
theorem parametricPowerCayleyCompanion_mem_generatedAlgebra
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (f : ContractiveBoundaryFunction i) (z : ℂ) (hz : z ∈ unitDisk) :
    parametricPowerCayleyCompanion Gamma mu B f z ∈ generatedAlgebra B := by
  rw [parametricPowerCayleyCompanion, dif_pos hz]
  exact parametricBoundaryCompanion_mem_generatedAlgebra Gamma B hWB _

omit [Nonempty n] in
/-- Generic double-layer identity using only the mass normalization. -/
theorem two_smul_boundaryPhi_parametric_eq_of_mass
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (hmass :
      ∫ x, parametricBoundaryFirstPart Gamma B x ∂mu =
        (1 : SquareMatrix n))
    (h : i →ᵇ ℂ) (X : SquareMatrix n)
    (hfirstIntegral :
      ∫ x, h x • parametricBoundaryFirstPart Gamma B x ∂mu = X) :
    (2 : ℂ) • boundaryPhiCLM
        (parametricPositiveBoundaryDensityOfMass Gamma B hWB hmass) h =
      X + (parametricBoundaryCompanion Gamma mu B h)ᴴ := by
  let first : i → SquareMatrix n := parametricBoundaryFirstPart Gamma B
  have hfirst : Integrable (fun x ↦ h x • first x) mu := by
    apply integrable_of_continuous_compact
    exact h.continuous.smul
      (continuous_parametricBoundaryFirstPart Gamma B hWB)
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
  rw [integral_add hfirst hsecond, hfirstIntegral, hsecondIntegral]

/-- The full direct Cayley identity obtained from the exact power Cauchy data. -/
theorem parametric_direct_cayley_identity_of_powerCauchy
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (f : ContractiveBoundaryFunction i) (T : SquareMatrix n)
    (hCauchy : HasParametricPowerCauchyFormula Gamma mu B f T)
    (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    (z : ℂ) (hz : z ∈ unitDisk) :
    (2 : ℂ) • doubleLayerCayleySeries
        (parametricPositiveBoundaryDensityOfMass
          Gamma B hWB hCauchy.mass_eq_one) f z =
      matrixCayleyTransform z T +
        (parametricPowerCayleyCompanion Gamma mu B f z)ᴴ := by
  let D : PositiveBoundaryDensity (n := n) mu :=
    parametricPositiveBoundaryDensityOfMass Gamma B hWB hCauchy.mass_eq_one
  have hznorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  rw [doubleLayerCayleySeries_eq_value D f z hznorm]
  rw [parametricPowerCayleyCompanion, dif_pos hz]
  exact two_smul_boundaryPhi_parametric_eq_of_mass
    Gamma B hWB hCauchy.mass_eq_one _ _
    (parametricBoundaryFirstPartIntegral_cayley_eq_of_powerCauchy
      Gamma B hWB f T hCauchy hspectrum z hz)

/-- A supported parametrization with the exact power Cauchy identities
constructs a positive-real completion of the prescribed target. -/
theorem exists_positiveRealCompletion_of_parametricPowerCauchy
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (f : ContractiveBoundaryFunction i) (T : SquareMatrix n)
    (hCauchy : HasParametricPowerCauchyFormula Gamma mu B f T)
    (hspectrum : matrixSpectrum T ⊆ closedUnitDisk) :
    ∃ H : ℂ → SquareMatrix n, IsPositiveRealCompletion B T H := by
  let D : PositiveBoundaryDensity (n := n) mu :=
    parametricPositiveBoundaryDensityOfMass Gamma B hWB hCauchy.mass_eq_one
  let g : ℂ → SquareMatrix n :=
    parametricPowerCayleyCompanion Gamma mu B f
  refine ⟨doubleLayerCayleySeries D f, ?_⟩
  apply isPositiveRealCompletion_of_direct_cayley_identity
    B T (doubleLayerCayleySeries D f) g
  · exact hspectrum
  · exact doubleLayerCayleySeries_analyticOnNhd D f
  · exact doubleLayerCayleySeries_zero D f
  · exact doubleLayerCayleySeries_rePart_posSemidef D f
  · intro z hz
    exact parametricPowerCayleyCompanion_mem_generatedAlgebra
      Gamma B hWB f z hz
  · intro z hz
    exact parametric_direct_cayley_identity_of_powerCauchy
      Gamma B hWB f T hCauchy hspectrum z hz

/-- The normalized constant-two estimate needs no statement stronger than the
power Cauchy identities used by the Cayley series. -/
theorem norm_le_two_of_parametricPowerCauchy
    (Gamma : ParametricConvexBoundary (i := i) Omega)
    (B T : SquareMatrix n) (hWB : numericalRange B ⊆ Omega)
    (f : ContractiveBoundaryFunction i)
    (hCauchy : HasParametricPowerCauchyFormula Gamma mu B f T)
    (hB : SimpleDiagonalization B) (lambda : n → ℂ)
    (htarget : T = innerConjugation hB.changeBasis (Matrix.diagonal lambda))
    (hlambda : ∀ j, ‖lambda j‖ ≤ 1) :
    ‖T‖ ≤ 2 := by
  have hspectrum : matrixSpectrum T ⊆ closedUnitDisk := by
    rw [htarget, matrixSpectrum, AlgEquiv.spectrum_eq, spectrum_diagonal]
    rintro z ⟨j, rfl⟩
    simpa [closedUnitDisk, Metric.mem_closedBall, dist_eq_norm] using hlambda j
  obtain ⟨H, hH⟩ := exists_positiveRealCompletion_of_parametricPowerCauchy
    Gamma B hWB f T hCauchy hspectrum
  exact positiveRealCompletionStatement B T H hB lambda htarget hlambda hH

omit [CompactSpace i] [MeasurableSpace i] [OpensMeasurableSpace i]
  [IsFiniteMeasure mu] [Nonempty n] in
/-- Function evaluation through a simple diagonalization respects powers. -/
theorem SimpleDiagonalization.functionEval_pow
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (f : ℂ → ℂ) (m : ℕ) :
    hB.functionEval (fun z ↦ f z ^ m) = (hB.functionEval f) ^ m := by
  rw [SimpleDiagonalization.functionEval, SimpleDiagonalization.functionEval]
  rw [← map_pow]
  congr 1
  simpa only [Pi.pow_apply] using
    (map_pow (Matrix.diagonalAlgHom ℂ) (fun j ↦ f (hB.eigenvalues j)) m)

namespace PositivePeriodicRadialData
namespace OrientedRadialConvexBoundary

omit [Nonempty n] in
/-- A holomorphic function on a neighborhood of the compact closed radial domain supplies
exactly the power Cauchy identities used by the Cayley-series argument. -/
theorem hasParametricPowerCauchyFormula_of_holomorphic_of_simpleDiagonalization
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hclosureCompact : IsCompact (closure Omega))
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ 1)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    HasParametricPowerCauchyFormula
      (G.parametricBoundary R c) contourParameterMeasure B
      (parametricContractiveBoundaryFunctionOfContinuousOn
        (G.parametricBoundary R c) f
        (hf.continuousOn.mono hclosure) hbound)
      (hB.functionEval f) := by
  obtain ⟨epsilon, hepsilon, hbuffer⟩ :=
    hclosureCompact.exists_cthickening_subset_open hVopen hclosure
  let W := Metric.thickening epsilon (closure Omega)
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hWconvex : Convex ℝ W :=
    G.domain.convex_domain.closure.thickening epsilon
  have hclosureW : closure Omega ⊆ W :=
    Metric.self_subset_thickening hepsilon (closure Omega)
  have hWsubsetV : W ⊆ V :=
    (Metric.thickening_subset_cthickening epsilon (closure Omega)).trans hbuffer
  have hfW : DifferentiableOn ℂ f W := hf.mono hWsubsetV
  intro m
  let k : ℂ := -Complex.I * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)
  let q : ℝ → SquareMatrix n := fun t ↦
    k • ((f (R.point c t)) ^ m •
      (R.tangent t • doubleLayerResolvent B (R.point c t)))
  have hboundary : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
      R.point c t ∈ closure Omega := fun t ht ↦
    frontier_subset_closure (G.supported t ht).boundary_point
  have hbase :=
    RadialConvexDomain.integral_holomorphic_cauchy_resolvent_of_simpleDiagonalization
      R c G.domain hWopen hWconvex hclosureW hboundary
      (hfW.fun_pow m) B hB hWB
  calc
    (∫ x, ((parametricContractiveBoundaryFunctionOfContinuousOn
          (G.parametricBoundary R c) f
          (hf.continuousOn.mono hclosure) hbound).function x) ^ m •
        parametricBoundaryFirstPart (G.parametricBoundary R c) B x
        ∂contourParameterMeasure) =
        ∫ x : ContourParameter, q x.1 ∂contourParameterMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (f (R.point c x.1)) ^ m •
          parametricBoundaryFirstPart (G.parametricBoundary R c) B x = q x.1
        rw [G.parametricBoundaryFirstPart_eq_cauchyIntegrand R c B x]
        ext i j
        simp [q, k, parametricBoundaryResolvent, smul_smul]
        ring
    _ = ∫ t in (0 : ℝ)..contourPeriod, q t :=
      integral_contourParameter_eq_intervalIntegral q
    _ = k • (∫ t in (0 : ℝ)..contourPeriod,
        (f (R.point c t)) ^ m •
          (R.tangent t • doubleLayerResolvent B (R.point c t))) := by
      exact intervalIntegral.integral_smul k _
    _ = k • (((contourPeriod : ℂ) * Complex.I) •
        hB.functionEval (fun z ↦ f z ^ m)) := by
      rw [hbase]
    _ = hB.functionEval (fun z ↦ f z ^ m) := by
      rw [smul_smul, cauchyNormalization_mul_period_I, one_smul]
    _ = (hB.functionEval f) ^ m := hB.functionEval_pow f m

/-- The normalized holomorphic estimate on a supported radial convex domain. -/
theorem norm_functionEval_le_two_of_holomorphic_of_simpleDiagonalization
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hclosureCompact : IsCompact (closure Omega))
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ 1)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    ‖hB.functionEval f‖ ≤ 2 := by
  apply norm_le_two_of_parametricPowerCauchy
    (mu := contourParameterMeasure) (G.parametricBoundary R c)
    B (hB.functionEval f) hWB
    (parametricContractiveBoundaryFunctionOfContinuousOn
      (G.parametricBoundary R c) f
      (hf.continuousOn.mono hclosure) hbound)
    (G.hasParametricPowerCauchyFormula_of_holomorphic_of_simpleDiagonalization
      R c hVopen hclosureCompact hclosure hf hbound B hB hWB)
    hB (fun j ↦ f (hB.eigenvalues j)) rfl
  intro j
  apply hbound (hB.eigenvalues j)
  exact subset_closure
    (hWB (matrixSpectrum_subset_numericalRange B
      (hB.eigenvalue_mem_matrixSpectrum j)))

end OrientedRadialConvexBoundary
end PositivePeriodicRadialData

end CrouzeixConjecture
