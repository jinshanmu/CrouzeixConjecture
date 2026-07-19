module

public import CrouzeixConjecture.CompletionStatement
public import CrouzeixConjecture.DoubleLayerAlgebra
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

@[expose] public section

noncomputable section

open Filter Metric
open scoped ENNReal Matrix Matrix.Norms.L2Operator NNReal Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A matrix whose spectrum is contained in the closed unit disk has spectral radius at most
one. -/
theorem matrix_spectralRadius_le_one_of_spectrum_subset_closedUnitDisk
    (T : SquareMatrix n) (hspectrum : matrixSpectrum T ⊆ closedUnitDisk) :
    spectralRadius ℂ T ≤ 1 := by
  obtain ⟨lambda, hlambdaSpectrum, hlambdaRadius⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius T
  rw [← hlambdaRadius]
  have hlambda := hspectrum hlambdaSpectrum
  have hnorm : ‖lambda‖ ≤ 1 := by
    simpa [closedUnitDisk, Metric.mem_closedBall, dist_eq_norm] using hlambda
  exact_mod_cast hnorm

/-- The Neumann series for `(I-zT)⁻¹` converges throughout the open unit disk under the
manuscript's spectral (rather than operator-norm) hypothesis. -/
theorem hasSum_resolvent_series_of_spectrum_subset_closedUnitDisk
    (T : SquareMatrix n) (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (fun k : ℕ ↦ z ^ k • T ^ k) (1 - z • T)⁻¹ := by
  have hzNorm : ‖z‖ < 1 := by
    simpa [unitDisk, Metric.mem_ball, dist_eq_norm] using hz
  let r : ℝ≥0 := ⟨(‖z‖ + 1) / 2, by positivity⟩
  have hrPos : 0 < r := by
    change 0 < (‖z‖ + 1) / 2
    positivity
  have hzLtR : ‖z‖ < (r : ℝ) := by
    change ‖z‖ < (‖z‖ + 1) / 2
    linarith
  have hrLtOne : (r : ℝ) < 1 := by
    change (‖z‖ + 1) / 2 < 1
    linarith
  have hspectralRadius : spectralRadius ℂ T ≤ 1 :=
    matrix_spectralRadius_le_one_of_spectrum_subset_closedUnitDisk T hspectrum
  have hOneLeInv : (1 : ℝ≥0∞) ≤ (spectralRadius ℂ T)⁻¹ := by
    simpa using (ENNReal.inv_le_inv.mpr hspectralRadius)
  have hradius : (r : ℝ≥0∞) < (spectralRadius ℂ T)⁻¹ := by
    exact (ENNReal.coe_lt_one_iff.mpr hrLtOne).trans_le hOneLeInv
  have hlocal :=
    (spectrum.differentiableOn_inverse_one_sub_smul (a := T) hradius)
      |>.hasFPowerSeriesOnBall hrPos
  have hseries :=
    (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ T).exchange_radius hlocal
  have hzBall : z ∈ Metric.eball (0 : ℂ) (r : ℝ≥0∞) := by
    rw [Metric.eball_coe, mem_ball_zero_iff]
    exact hzLtR
  rw [Matrix.nonsing_inv_eq_ringInverse]
  simpa [ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const] using
    hseries.hasSum_sub hzBall

/-- The same result in the exact coefficient notation of the double-layer construction. -/
theorem hasSum_resolventSeriesTerm_of_spectrum_subset_closedUnitDisk
    (T : SquareMatrix n) (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (resolventSeriesTerm z T) (1 - z • T)⁻¹ := by
  simpa only [resolventSeriesTerm] using
    hasSum_resolvent_series_of_spectrum_subset_closedUnitDisk T hspectrum hz

/-- Consequently the positive-degree resolvent tail has the manuscript's claimed sum. -/
theorem hasSum_resolventTailTerm_of_spectrum_subset_closedUnitDisk
    (T : SquareMatrix n) (hspectrum : matrixSpectrum T ⊆ closedUnitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (resolventTailTerm z T) ((1 - z • T)⁻¹ - 1) := by
  exact resolventTailTerm_hasSum_of_resolventSeries z T
    (hasSum_resolventSeriesTerm_of_spectrum_subset_closedUnitDisk T hspectrum hz)

end CrouzeixConjecture
