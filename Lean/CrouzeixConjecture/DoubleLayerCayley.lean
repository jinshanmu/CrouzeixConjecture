module

public import CrouzeixConjecture.DoubleLayerPositiveMap
public import CrouzeixConjecture.CompletionStatement
public import CrouzeixConjecture.MatrixPowerSeries
public import CrouzeixConjecture.ResolventSeries

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {i n : Type*} [TopologicalSpace i] [MeasurableSpace i]
  [OpensMeasurableSpace i] [Fintype n] [DecidableEq n] [Nonempty n]

/-- A bounded continuous boundary function satisfying the unit sup-norm hypothesis in
manuscript lines 236--238. -/
structure ContractiveBoundaryFunction (i : Type*) [TopologicalSpace i] where
  function : i →ᵇ ℂ
  norm_le_one : ∀ x, ‖function x‖ ≤ 1

private theorem one_sub_mul_ne_zero_of_norm_lt_one
    {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) : 1 - z * w ≠ 0 := by
  intro hzero
  have hprod : ‖z * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg z)).trans_lt (by simpa using hz)
  have : z * w = 1 := (sub_eq_zero.mp hzero).symm
  rw [this, norm_one] at hprod
  exact (lt_irrefl 1 hprod).elim

private theorem norm_cayleyTransform_le
    {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖cayleyTransform z w‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
  have hzw : ‖z * w‖ ≤ ‖z‖ := by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left hw (norm_nonneg z)
  have hdenlower : 1 - ‖z‖ ≤ ‖1 - z * w‖ := by
    calc
      1 - ‖z‖ ≤ 1 - ‖z * w‖ := sub_le_sub_left hzw 1
      _ ≤ |(1 : ℝ) - ‖z * w‖| := le_abs_self _
      _ ≤ ‖(1 : ℂ) - z * w‖ := by
        simpa using abs_norm_sub_norm_le (1 : ℂ) (z * w)
  have hnum : ‖1 + z * w‖ ≤ 1 + ‖z‖ := by
    calc
      ‖1 + z * w‖ ≤ ‖(1 : ℂ)‖ + ‖z * w‖ := norm_add_le _ _
      _ ≤ 1 + ‖z‖ := by simpa using add_le_add_left hzw 1
  have hdenpos : 0 < ‖1 - z * w‖ :=
    norm_pos_iff.mpr (one_sub_mul_ne_zero_of_norm_lt_one hz hw)
  have hgap : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  rw [cayleyTransform, norm_div]
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖1 + z * w‖ ≤ 1 + ‖z‖ := hnum
    _ = ((1 + ‖z‖) / (1 - ‖z‖)) * (1 - ‖z‖) := by
      field_simp [hgap.ne']
    _ ≤ ((1 + ‖z‖) / (1 - ‖z‖)) * ‖1 - z * w‖ := by
      exact mul_le_mul_of_nonneg_left hdenlower (div_nonneg (by positivity) hgap.le)

/-- The manuscript's Cayley boundary function `h_z`, bundled as a bounded continuous
function.  Its boundedness is proved from the exact disk and unit-sup hypotheses. -/
def cayleyBoundaryFunction (z : ℂ) (hz : ‖z‖ < 1)
    (f : ContractiveBoundaryFunction i) : i →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ cayleyTransform z (f.function x), by
      unfold cayleyTransform
      exact
        (continuous_const.add (continuous_const.mul f.function.continuous)).div
          (continuous_const.sub (continuous_const.mul f.function.continuous))
          (fun x ↦ one_sub_mul_ne_zero_of_norm_lt_one hz (f.norm_le_one x))⟩
    (2 * ((1 + ‖z‖) / (1 - ‖z‖)))
    (fun x y ↦ by
      rw [dist_eq_norm]
      calc
        ‖cayleyTransform z (f.function x) - cayleyTransform z (f.function y)‖ ≤
            ‖cayleyTransform z (f.function x)‖ +
              ‖cayleyTransform z (f.function y)‖ := norm_sub_le _ _
        _ ≤ (1 + ‖z‖) / (1 - ‖z‖) +
              (1 + ‖z‖) / (1 - ‖z‖) :=
          add_le_add
            (norm_cayleyTransform_le hz (f.norm_le_one x))
            (norm_cayleyTransform_le hz (f.norm_le_one y))
        _ = 2 * ((1 + ‖z‖) / (1 - ‖z‖)) := by ring)

omit [MeasurableSpace i] [OpensMeasurableSpace i] in
@[simp]
theorem cayleyBoundaryFunction_apply (z : ℂ) (hz : ‖z‖ < 1)
    (f : ContractiveBoundaryFunction i) (x : i) :
    cayleyBoundaryFunction z hz f x = cayleyTransform z (f.function x) := rfl

variable {mu : Measure i}

/-- The value `H(z)=Φ(h_z)` from manuscript equation (318), for a point of the open disk. -/
def doubleLayerCayleyValue (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (z : ℂ) (hz : ‖z‖ < 1) :
    SquareMatrix n :=
  boundaryPhiCLM D (cayleyBoundaryFunction z hz f)

omit [Nonempty n] in
/-- The constructed Cayley completion has value `I` at the origin. -/
@[simp]
theorem doubleLayerCayleyValue_zero
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (hz : ‖(0 : ℂ)‖ < 1) :
    doubleLayerCayleyValue D f 0 hz = 1 := by
  have hboundary : cayleyBoundaryFunction 0 hz f = (1 : i →ᵇ ℂ) := by
    ext x
    rw [cayleyBoundaryFunction_apply]
    simp [cayleyTransform]
  rw [doubleLayerCayleyValue, hboundary, boundaryPhi_one]

omit [Nonempty n] in
/-- The real part of every constructed Cayley value is positive semidefinite, proving the
positivity assertion in manuscript equation (323). -/
theorem doubleLayerCayleyValue_rePart_posSemidef
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (z : ℂ) (hz : ‖z‖ < 1) :
    (rePart (doubleLayerCayleyValue D f z hz)).PosSemidef := by
  apply rePart_boundaryPhi_posSemidef
  intro x
  rw [cayleyBoundaryFunction_apply]
  exact cayleyTransform_re_nonneg hz (f.norm_le_one x)

/-- Coefficients of the analytic series obtained by applying the bounded positive map to the
uniform Cayley expansion in manuscript equations (327)--(335). -/
def doubleLayerCayleySeriesCoefficient
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) : ℕ → SquareMatrix n
  | 0 => 1
  | m + 1 => (2 : ℂ) • boundaryPhiCLM D (f.function ^ (m + 1))

/-- The coefficients of the double-layer Cayley series are uniformly bounded. -/
theorem doubleLayerCayleySeriesCoefficient_norm_le
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (m : ℕ) :
    ‖doubleLayerCayleySeriesCoefficient D f m‖ ≤
      max 1 (2 * ‖boundaryPhiCLM D‖) := by
  cases m with
  | zero =>
      change ‖(1 : SquareMatrix n)‖ ≤ max 1 (2 * ‖boundaryPhiCLM D‖)
      rw [norm_one]
      exact le_max_left _ _
  | succ m =>
      have hpow : ‖f.function ^ (m + 1)‖ ≤ 1 := by
        apply (BoundedContinuousFunction.norm_le (f := f.function ^ (m + 1))
          (by norm_num)).2
        intro x
        rw [BoundedContinuousFunction.pow_apply, norm_pow]
        exact pow_le_one₀ (norm_nonneg (f.function x)) (f.norm_le_one x)
      have hmap := (boundaryPhiCLM D).le_opNorm (f.function ^ (m + 1))
      calc
        ‖doubleLayerCayleySeriesCoefficient D f (m + 1)‖ =
            2 * ‖boundaryPhiCLM D (f.function ^ (m + 1))‖ := by
          simp [doubleLayerCayleySeriesCoefficient, norm_smul]
        _ ≤ 2 * (‖boundaryPhiCLM D‖ * ‖f.function ^ (m + 1)‖) := by
          exact mul_le_mul_of_nonneg_left hmap (by norm_num)
        _ ≤ 2 * ‖boundaryPhiCLM D‖ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc
            ‖boundaryPhiCLM D‖ * ‖f.function ^ (m + 1)‖ ≤
                ‖boundaryPhiCLM D‖ * 1 :=
              mul_le_mul_of_nonneg_left hpow (norm_nonneg (boundaryPhiCLM D))
            _ = ‖boundaryPhiCLM D‖ := mul_one _
        _ ≤ max 1 (2 * ‖boundaryPhiCLM D‖) := le_max_right _ _

/-- The analytic matrix function defined by the norm-convergent double-layer Cayley series. -/
def doubleLayerCayleySeries
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) : ℂ → SquareMatrix n :=
  matrixPowerSeriesSum (doubleLayerCayleySeriesCoefficient D f)

/-- The series construction is analytic on the whole open unit disk. -/
theorem doubleLayerCayleySeries_analyticOnNhd
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) :
    AnalyticOnNhd ℂ (doubleLayerCayleySeries D f) unitDisk := by
  exact matrixPowerSeriesSum_analyticOnNhd_unitDisk
    (doubleLayerCayleySeriesCoefficient D f)
    (max 1 (2 * ‖boundaryPhiCLM D‖))
    (doubleLayerCayleySeriesCoefficient_norm_le D f)

omit [Nonempty n] in
/-- The analytic series has the required normalization at zero. -/
@[simp]
theorem doubleLayerCayleySeries_zero
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) :
    doubleLayerCayleySeries D f 0 = 1 := by
  simp [doubleLayerCayleySeries, doubleLayerCayleySeriesCoefficient]

/-- Exact norm-convergent coefficient expansion of the analytic double-layer Cayley series. -/
theorem doubleLayerCayleySeries_hasSum
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum
      (fun m ↦ z ^ m • doubleLayerCayleySeriesCoefficient D f m)
      (doubleLayerCayleySeries D f z) := by
  exact matrixPowerSeries_hasSum
    (doubleLayerCayleySeriesCoefficient D f)
    (max 1 (2 * ‖boundaryPhiCLM D‖))
    (doubleLayerCayleySeriesCoefficient_norm_le D f) hz

/-- The bounded-continuous-function terms in the uniform Cayley expansion. -/
def cayleyBoundarySeriesTerm (z : ℂ)
    (f : ContractiveBoundaryFunction i) : ℕ → (i →ᵇ ℂ)
  | 0 => 1
  | m + 1 => (2 * z ^ (m + 1)) • (f.function ^ (m + 1))

omit [MeasurableSpace i] [OpensMeasurableSpace i] in
/-- The scalar Cayley series converges in boundary sup norm, not merely pointwise. -/
theorem cayleyBoundarySeriesTerm_hasSum (z : ℂ) (hz : ‖z‖ < 1)
    (f : ContractiveBoundaryFunction i) :
    HasSum (cayleyBoundarySeriesTerm z f) (cayleyBoundaryFunction z hz f) := by
  let xfun : i →ᵇ ℂ := z • f.function
  have hfNorm : ‖f.function‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le (f := f.function) (by norm_num)).2 f.norm_le_one
  have hxfun : ‖xfun‖ < 1 := by
    rw [show ‖xfun‖ = ‖z‖ * ‖f.function‖ by simp [xfun, norm_smul]]
    exact (mul_le_mul_of_nonneg_left hfNorm (norm_nonneg z)).trans_lt (by simpa using hz)
  have hgeom := hasSum_geom_series_inverse xfun hxfun
  have hone := hasSum_ite_eq 0 (1 : i →ᵇ ℂ)
  have hraw := (hgeom.const_smul (2 : ℂ)).sub hone
  have hunit : IsUnit (1 - xfun) := isUnit_one_sub_of_norm_lt_one hxfun
  have hcayley :
      cayleyBoundaryFunction z hz f =
        (1 + xfun) * Ring.inverse (1 - xfun) := by
    apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ hunit).2
    ext y
    have hden : 1 - z * f.function y ≠ 0 :=
      one_sub_mul_ne_zero_of_norm_lt_one hz (f.norm_le_one y)
    change cayleyTransform z (f.function y) * (1 - z * f.function y) =
      1 + z * f.function y
    exact div_mul_cancel₀ (1 + z * f.function y) hden
  have hlimit :
      (2 : ℂ) • Ring.inverse (1 - xfun) - 1 =
        cayleyBoundaryFunction z hz f := by
    rw [hcayley]
    have hinverse :
        (1 - xfun) * Ring.inverse (1 - xfun) = 1 :=
      Ring.mul_inverse_cancel (1 - xfun) hunit
    calc
      (2 : ℂ) • Ring.inverse (1 - xfun) - 1 =
          (2 : ℂ) • Ring.inverse (1 - xfun) -
            (1 - xfun) * Ring.inverse (1 - xfun) := by rw [hinverse]
      _ = (1 + xfun) * Ring.inverse (1 - xfun) := by
        rw [show (2 : ℂ) • Ring.inverse (1 - xfun) =
            Ring.inverse (1 - xfun) + Ring.inverse (1 - xfun) by
          rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]]
        ring
  rw [← hlimit]
  convert hraw using 1
  funext m
  cases m with
  | zero =>
      change (1 : i →ᵇ ℂ) = (2 : ℂ) • (1 : i →ᵇ ℂ) - 1
      rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
      abel
  | succ m =>
      change (2 * z ^ (m + 1)) • (f.function ^ (m + 1)) =
        (2 : ℂ) • (z • f.function) ^ (m + 1) - 0
      rw [sub_zero, smul_pow, smul_smul]

/-- The analytic coefficient series agrees, point by point in the disk, with the positive-map
definition `Φ(h_z)`.  This justifies both the analyticity and positivity claims for one and the
same function, rather than for two separately postulated objects. -/
theorem doubleLayerCayleySeries_eq_value
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (z : ℂ) (hz : ‖z‖ < 1) :
    doubleLayerCayleySeries D f z = doubleLayerCayleyValue D f z hz := by
  have hzDisk : z ∈ unitDisk := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hboundary := (cayleyBoundarySeriesTerm_hasSum z hz f).mapL (boundaryPhiCLM D)
  have hmapped :
      HasSum
        (fun m ↦ z ^ m • doubleLayerCayleySeriesCoefficient D f m)
        (doubleLayerCayleyValue D f z hz) := by
    convert hboundary using 1
    funext m
    cases m with
    | zero =>
        simpa only [pow_zero, one_smul, doubleLayerCayleySeriesCoefficient,
          cayleyBoundarySeriesTerm] using (boundaryPhi_one D).symm
    | succ m =>
        simp [cayleyBoundarySeriesTerm, doubleLayerCayleySeriesCoefficient,
          mul_smul]
        module
  exact (doubleLayerCayleySeries_hasSum D f hzDisk).unique hmapped

/-- Positivity of the real part of the analytic series throughout the disk. -/
theorem doubleLayerCayleySeries_rePart_posSemidef
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i) (z : ℂ) (hz : z ∈ unitDisk) :
    (rePart (doubleLayerCayleySeries D f z)).PosSemidef := by
  have hznorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  rw [doubleLayerCayleySeries_eq_value D f z hznorm]
  exact doubleLayerCayleyValue_rePart_posSemidef D f z hznorm

/-- The analytic, positive Cayley series supplies a genuine positive-real completion once the
contour companion identity and its generated-algebra membership have been established.  These
are exactly the remaining analytic conclusions of manuscript equations (308) and (343), not a
norm estimate or a restatement of the completion conclusion. -/
theorem doubleLayerCayleySeries_isPositiveRealCompletion
    (D : PositiveBoundaryDensity (n := n) mu)
    (f : ContractiveBoundaryFunction i)
    (B T : SquareMatrix n) (G : ℕ → SquareMatrix n)
    (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    (hAlg : generatedAlgebra T = generatedAlgebra B)
    (hG : ∀ m : ℕ, G (m + 1) ∈ generatedAlgebra B)
    (hcoefficient : ∀ m : ℕ,
      doubleLayerCayleySeriesCoefficient D f (m + 1) =
        T ^ (m + 1) + (G (m + 1))ᴴ) :
    IsPositiveRealCompletion T (doubleLayerCayleySeries D f) := by
  refine ⟨doubleLayerCayleySeries_analyticOnNhd D f,
    doubleLayerCayleySeries_zero D f, ?_, ?_⟩
  · intro z hz
    exact doubleLayerCayleySeries_rePart_posSemidef D f z hz
  · intro z hz
    have hfull := doubleLayerCayleySeries_hasSum D f hz
    have htail :
        HasSum (doubleLayerCompletionTailTerm z T G)
          (doubleLayerCayleySeries D f z - 1) := by
      convert (hasSum_nat_add_iff' 1).mpr hfull using 1
      · funext m
        rw [hcoefficient m]
        simp [doubleLayerCompletionTailTerm, doubleLayerCompletionCoefficient]
      · simp [doubleLayerCayleySeriesCoefficient]
    exact completion_sub_resolvent_mem_generatedAlgebra_conjTranspose
      z B T (doubleLayerCayleySeries D f z) G hAlg hG htail
      (hasSum_resolventSeriesTerm_of_spectrum_subset_closedUnitDisk T hspectrum hz)

end CrouzeixConjecture
