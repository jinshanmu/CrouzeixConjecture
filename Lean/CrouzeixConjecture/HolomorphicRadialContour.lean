module

public import CrouzeixConjecture.RadialContour
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ComplexOrder Interval Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- Evaluation of a scalar function through a fixed simple diagonalization. -/
def SimpleDiagonalization.functionEval
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (f : ℂ → ℂ) :
    SquareMatrix n :=
  innerConjugation hB.changeBasis
    (Matrix.diagonal fun i ↦ f (hB.eigenvalues i))

private theorem function_mul_div_sub_eq_add_dslope
    (f : ℂ → ℂ) {z w v : ℂ} (hzw : z ≠ w) :
    f z * (v / (z - w)) =
      f w * (v / (z - w)) + dslope f w z * v := by
  have hdecomp : f z = f w + (z - w) * dslope f w z := by
    have hslope := sub_smul_dslope f w z
    simp only [smul_eq_mul] at hslope
    calc
      f z = (f z - f w) + f w := by ring
      _ = (z - w) * dslope f w z + f w := by rw [← hslope]
      _ = f w + (z - w) * dslope f w z := by ring
  rw [hdecomp]
  field_simp [sub_ne_zero.mpr hzw]

namespace PositivePeriodicRadialData
namespace RadialConvexDomain

/-- Scalar Cauchy formula for a holomorphic function on an open convex neighborhood of the
closed domain.  At the level of `RadialConvexDomain`, boundary membership is stated explicitly;
it follows from the support field of an `OrientedRadialConvexBoundary`. -/
theorem integral_holomorphic_cauchy
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (D : RadialConvexDomain R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
      R.point c t ∈ closure Omega)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    {w : ℂ} (hw : w ∈ Omega) :
    (∫ t in (0 : ℝ)..contourPeriod,
      f (R.point c t) *
        (R.tangent t / (R.point c t - w))) =
      f w * ((contourPeriod : ℂ) * Complex.I) := by
  have hwV : w ∈ V := hclosure (subset_closure hw)
  have hdslope : DifferentiableOn ℂ (dslope f w) V :=
    (Complex.differentiableOn_dslope (hVopen.mem_nhds hwV)).2 hf
  obtain ⟨F, hF⟩ := hVconvex.exists_forall_hasDerivWithinAt hdslope
  have hpointV (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) contourPeriod) :
      R.point c t ∈ V :=
    hclosure (hboundary t ht)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
      HasDerivAt (fun s : ℝ ↦ F (R.point c s))
        (dslope f w (R.point c t) * R.tangent t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) contourPeriod := by
      simpa only [uIcc_of_le contourPeriod_nonneg] using ht
    have hFat : HasDerivAt F (dslope f w (R.point c t)) (R.point c t) :=
      (hF (R.point c t) (hpointV t htIcc)).hasDerivAt
        (hVopen.mem_nhds (hpointV t htIcc))
    convert (hFat.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (R.point_hasDerivAt c t) using 1
    simp only [ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  have hdslopePath : ContinuousOn
      (fun t : ℝ ↦ dslope f w (R.point c t))
      (Set.Icc (0 : ℝ) contourPeriod) :=
    hdslope.continuousOn.comp (R.point_continuous c).continuousOn hpointV
  have hquotientContinuous : ContinuousOn
      (fun t : ℝ ↦ dslope f w (R.point c t) * R.tangent t)
      (Set.Icc (0 : ℝ) contourPeriod) :=
    hdslopePath.mul R.tangent_continuous.continuousOn
  have hquotientInt : IntervalIntegrable
      (fun t : ℝ ↦ dslope f w (R.point c t) * R.tangent t)
      volume 0 contourPeriod :=
    hquotientContinuous.intervalIntegrable_of_Icc contourPeriod_nonneg
  have hquotientZero :
      (∫ t in (0 : ℝ)..contourPeriod,
        dslope f w (R.point c t) * R.tangent t) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hquotientInt,
      R.point_periodic_endpoint c]
    simp
  have hwind := D.intervalIntegrable_tangent_div_point_sub R c hw
  rw [intervalIntegral.integral_congr (fun t ht ↦
    function_mul_div_sub_eq_add_dslope f
      (RadialConvexDomain.point_ne_interior R c D
        (by
          simpa only [uIcc_of_le contourPeriod_nonneg] using ht)
        hw))]
  rw [intervalIntegral.integral_add
    (hwind.const_mul (f w)) hquotientInt]
  rw [intervalIntegral.integral_const_mul,
    D.integral_tangent_div_point_sub R c hw,
    hquotientZero, add_zero]

private theorem functionResolventIntegrand_eq_innerConjugation_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (f : ℂ → ℂ) {sigma tangent : ℂ}
    (hne : ∀ i, sigma ≠ hB.eigenvalues i) :
    f sigma • (tangent • doubleLayerResolvent B sigma) =
      innerConjugation hB.changeBasis
        (Matrix.diagonal fun i ↦
          f sigma * (tangent / (sigma - hB.eigenvalues i))) := by
  rw [doubleLayerResolvent_eq_innerConjugation_diagonal hB hne]
  let e := innerConjugation hB.changeBasis
  change f sigma •
      (tangent • e (Matrix.diagonal fun i ↦
        (sigma - hB.eigenvalues i)⁻¹)) = _
  rw [smul_smul]
  calc
    (f sigma * tangent) •
          e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) =
        e ((f sigma * tangent) •
          Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) := by
      exact (map_smul e _ _).symm
    _ = e (Matrix.diagonal fun i ↦
          f sigma * (tangent / (sigma - hB.eigenvalues i))) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [div_eq_mul_inv]
        ring
      · simp [Matrix.diagonal, hij]

/-- Matrix Cauchy formula for a holomorphic function at the manuscript's simple-spectrum
stage, proved entrywise in the supplied eigenbasis from the scalar holomorphic formula. -/
theorem integral_holomorphic_cauchy_resolvent_of_simpleDiagonalization
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (D : RadialConvexDomain R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
      R.point c t ∈ closure Omega)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    (∫ t in (0 : ℝ)..contourPeriod,
      f (R.point c t) •
        (R.tangent t • doubleLayerResolvent B (R.point c t))) =
      ((contourPeriod : ℂ) * Complex.I) • hB.functionEval f := by
  let e := innerConjugation hB.changeBasis
  let eCLM := innerConjugationCLM hB.changeBasis
  let F : ℝ → SquareMatrix n := fun t ↦
    Matrix.diagonal fun i ↦
      f (R.point c t) *
        (R.tangent t / (R.point c t - hB.eigenvalues i))
  have hlambda (i : n) : hB.eigenvalues i ∈ Omega :=
    hWB (matrixSpectrum_subset_numericalRange B
      (hB.eigenvalue_mem_matrixSpectrum i))
  have hpointV (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) contourPeriod) :
      R.point c t ∈ V :=
    hclosure (hboundary t ht)
  have hscalarContinuous (i : n) : ContinuousOn
      (fun t : ℝ ↦ f (R.point c t) *
        (R.tangent t / (R.point c t - hB.eigenvalues i)))
      (Set.Icc (0 : ℝ) contourPeriod) := by
    apply ContinuousOn.mul
    · exact hf.continuousOn.comp
        (R.point_continuous c).continuousOn hpointV
    · apply ContinuousOn.div R.tangent_continuous.continuousOn
        ((R.point_continuous c).continuousOn.sub continuousOn_const)
      intro t ht
      exact sub_ne_zero.mpr
        (RadialConvexDomain.point_ne_interior R c D ht (hlambda i))
  have hFcontinuous : ContinuousOn F (Set.Icc (0 : ℝ) contourPeriod) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa [F, Matrix.diagonal] using hscalarContinuous i
    · simpa [F, Matrix.diagonal, hij] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℂ))
          (Set.Icc (0 : ℝ) contourPeriod))
  have hFint : IntervalIntegrable F volume 0 contourPeriod :=
    hFcontinuous.intervalIntegrable_of_Icc contourPeriod_nonneg
  have hFintegral :
      (∫ t in (0 : ℝ)..contourPeriod, F t) =
        Matrix.diagonal (fun i ↦ f (hB.eigenvalues i) *
          ((contourPeriod : ℂ) * Complex.I)) := by
    ext i j
    change matrixEntryCLM i j (∫ t in (0 : ℝ)..contourPeriod, F t) = _
    rw [← (matrixEntryCLM i j).intervalIntegral_comp_comm hFint]
    by_cases hij : i = j
    · subst j
      simpa [F, matrixEntryCLM, Matrix.diagonal] using
        D.integral_holomorphic_cauchy R c hVopen hVconvex
          hclosure hboundary hf (hlambda i)
    · simp [F, matrixEntryCLM, Matrix.diagonal, hij]
  have hintegrand : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
      f (R.point c t) •
          (R.tangent t • doubleLayerResolvent B (R.point c t)) =
        eCLM (F t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) contourPeriod := by
      simpa only [uIcc_of_le contourPeriod_nonneg] using ht
    simpa [eCLM, innerConjugationCLM, F, e] using
      functionResolventIntegrand_eq_innerConjugation_diagonal hB f
        (fun i ↦ RadialConvexDomain.point_ne_interior R c D htIcc (hlambda i))
  rw [intervalIntegral.integral_congr hintegrand,
    eCLM.intervalIntegral_comp_comm hFint]
  change e (∫ t in (0 : ℝ)..contourPeriod, F t) = _
  rw [hFintegral]
  calc
    e (Matrix.diagonal fun i ↦ f (hB.eigenvalues i) *
          ((contourPeriod : ℂ) * Complex.I)) =
        e (((contourPeriod : ℂ) * Complex.I) •
          Matrix.diagonal fun i ↦ f (hB.eigenvalues i)) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp
        ring
      · simp [Matrix.diagonal, hij]
    _ = ((contourPeriod : ℂ) * Complex.I) •
        e (Matrix.diagonal fun i ↦ f (hB.eigenvalues i)) :=
      map_smul e _ _
    _ = ((contourPeriod : ℂ) * Complex.I) • hB.functionEval f := rfl

end RadialConvexDomain
end PositivePeriodicRadialData

end CrouzeixConjecture
