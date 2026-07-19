module

public import CrouzeixConjecture.CompletionStatement
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

noncomputable section

open scoped ENNReal Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The formal matrix-valued power series with coefficients `a m`; its `m`-linear term sends
`(z,…,z)` to `z^m • a m`. -/
def matrixPowerSeries (a : ℕ → SquareMatrix n) :
    FormalMultilinearSeries ℂ ℂ (SquareMatrix n) :=
  fun m ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin m) (a m)

omit [Fintype n] [DecidableEq n] in
/-- Evaluation of a formal matrix power-series term on a repeated scalar argument. -/
theorem matrixPowerSeries_apply (a : ℕ → SquareMatrix n) (m : ℕ) (z : ℂ) :
    matrixPowerSeries a m (fun _ ↦ z) = z ^ m • a m := by
  simp [matrixPowerSeries, ContinuousMultilinearMap.mkPiRing_apply]

/-- A uniform coefficient bound gives radius of convergence at least one. -/
theorem one_le_matrixPowerSeries_radius (a : ℕ → SquareMatrix n) (C : ℝ)
    (ha : ∀ m, ‖a m‖ ≤ C) :
    (1 : ℝ≥0∞) ≤ (matrixPowerSeries a).radius := by
  apply (matrixPowerSeries a).le_radius_of_bound C
  intro m
  simpa [matrixPowerSeries] using ha m

/-- The norm-convergent sum of a matrix-valued power series. -/
def matrixPowerSeriesSum (a : ℕ → SquareMatrix n) : ℂ → SquareMatrix n :=
  (matrixPowerSeries a).sum

/-- A uniformly bounded matrix coefficient sequence defines an analytic function throughout
the open unit disk. -/
theorem matrixPowerSeriesSum_analyticOnNhd_unitDisk
    (a : ℕ → SquareMatrix n) (C : ℝ) (ha : ∀ m, ‖a m‖ ≤ C) :
    AnalyticOnNhd ℂ (matrixPowerSeriesSum a) unitDisk := by
  have hradius : (1 : ℝ≥0∞) ≤ (matrixPowerSeries a).radius :=
    one_le_matrixPowerSeries_radius a C ha
  have hradius_pos : 0 < (matrixPowerSeries a).radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hradius
  have hseries := (matrixPowerSeries a).hasFPowerSeriesOnBall hradius_pos
  have hone := hseries.mono (by norm_num : (0 : ℝ≥0∞) < 1) hradius
  intro z hz
  apply hone.analyticAt_of_mem
  change z ∈ Metric.eball (0 : ℂ) (((1 : NNReal) : ENNReal))
  rw [Metric.eball_coe, mem_ball_zero_iff]
  simpa [unitDisk] using hz

/-- Inside the disk, the analytic sum is the norm sum of the expected matrix monomials. -/
theorem matrixPowerSeries_hasSum (a : ℕ → SquareMatrix n) (C : ℝ)
    (ha : ∀ m, ‖a m‖ ≤ C) {z : ℂ} (hz : z ∈ unitDisk) :
    HasSum (fun m ↦ z ^ m • a m) (matrixPowerSeriesSum a z) := by
  have hradius : (1 : ℝ≥0∞) ≤ (matrixPowerSeries a).radius :=
    one_le_matrixPowerSeries_radius a C ha
  have hradius_pos : 0 < (matrixPowerSeries a).radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hradius
  have hseries := (matrixPowerSeries a).hasFPowerSeriesOnBall hradius_pos
  have hone := hseries.mono (by norm_num : (0 : ℝ≥0∞) < 1) hradius
  have hz' : z ∈ Metric.eball (0 : ℂ) (((1 : NNReal) : ENNReal)) := by
    rw [Metric.eball_coe, mem_ball_zero_iff]
    simpa [unitDisk] using hz
  have hs :
      HasSum (fun m ↦ matrixPowerSeries a m (fun _ ↦ z))
        (matrixPowerSeriesSum a z) := by
    simpa only [matrixPowerSeriesSum, zero_add] using hone.hasSum hz'
  simpa only [matrixPowerSeries_apply] using hs

/-- The value at zero is the constant coefficient. -/
@[simp]
theorem matrixPowerSeriesSum_zero (a : ℕ → SquareMatrix n) :
    matrixPowerSeriesSum a 0 = a 0 := by
  change (∑' m, matrixPowerSeries a m (fun _ ↦ (0 : ℂ))) = a 0
  rw [show (∑' m, matrixPowerSeries a m (fun _ ↦ (0 : ℂ))) =
      ∑' m, (0 : ℂ) ^ m • a m from
    tsum_congr (fun m ↦ matrixPowerSeries_apply a m 0)]
  exact (HasSum.hasSum_at_zero a).tsum_eq

end CrouzeixConjecture
