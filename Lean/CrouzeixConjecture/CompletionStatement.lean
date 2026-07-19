module

public import CrouzeixConjecture.Spectrum
public import Mathlib.Analysis.Analytic.Basic

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The open unit disk used throughout the positive-real argument. -/
def unitDisk : Set ℂ := Metric.ball 0 1

/-- The closed unit disk containing the spectrum in the completion lemma. -/
def closedUnitDisk : Set ℂ := Metric.closedBall 0 1

/-- A spectral encoding of “all eigenvalues are distinct”.  Over `ℂ`, the characteristic
polynomial splits and has degree `card n`, so noduplicity of its roots is exactly the
manuscript's simple-spectrum hypothesis. -/
def HasDistinctEigenvalues (T : SquareMatrix n) : Prop := T.charpoly.roots.Nodup

/-- The pointwise analytic positive-real completion conditions from lines 33--39.  The function
is represented on all of `ℂ`, but every condition is restricted to the open unit disk, so values
outside the manuscript's domain are immaterial. -/
def IsPositiveRealCompletion (T : SquareMatrix n) (H : ℂ → SquareMatrix n) : Prop :=
  AnalyticOnNhd ℂ H unitDisk ∧
  H 0 = 1 ∧
  (∀ z ∈ unitDisk, IsPositiveMatrix (rePart (H z))) ∧
  ∀ z ∈ unitDisk,
    H z - (1 - z • T)⁻¹ ∈ generatedAlgebra Tᴴ

/-- Exact proposition asserted by the positive-real completion lemma at lines 30--42. -/
def PositiveRealCompletionStatement : Prop :=
  ∀ (T : SquareMatrix n) (H : ℂ → SquareMatrix n),
    HasDistinctEigenvalues T →
    matrixSpectrum T ⊆ closedUnitDisk →
    IsPositiveRealCompletion T H →
    ‖T‖ ≤ 2

end CrouzeixConjecture
