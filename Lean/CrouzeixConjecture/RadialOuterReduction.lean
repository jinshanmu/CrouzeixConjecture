module

public import CrouzeixConjecture.ParallelRadialBoundary
public import CrouzeixConjecture.MainOuterLimit

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A bounded open convex domain has the exact radial `C¹` boundary package consumed by
the proved Cauchy and double-layer constructions. -/
def HasOrientedRadialConvexBoundary (Omega : Set ℂ) : Prop :=
  ∃ R : PositivePeriodicRadialData, ∃ c : ℂ,
    Nonempty (R.OrientedRadialConvexBoundary c Omega)

/-- The sole remaining geometric assertion for the canonical parallel bodies used in the
outer-limit argument. -/
def CanonicalParallelOrientedRadialBoundaryStatement : Prop :=
  ∀ (A : SquareMatrix n) (k : ℕ),
    HasOrientedRadialConvexBoundary
      (parallelOuterDomain (numericalRange A) k)

/-- The canonical positive parallel bodies of the numerical range have the required oriented
radial `C¹` boundaries. -/
theorem canonicalParallelOrientedRadialBoundaryStatement :
    CanonicalParallelOrientedRadialBoundaryStatement (n := n) := by
  intro A k
  unfold HasOrientedRadialConvexBoundary
  simpa only [parallelOuterDomain] using
    (exists_orientedRadialConvexBoundary_thickening
      (numericalRange A) (numericalRange_nonempty A)
      (isCompact_numericalRange A) (numericalRange_convex A)
      (outerApproximationRadius_pos k))

/-- The radial boundary geometry implies the previously isolated canonical double-layer
statement.  All Cauchy, positivity, companion, algebra-membership, and coefficient claims are
discharged by the permanent radial and parametric-boundary modules. -/
theorem canonicalParallelDoubleLayerStatement_of_orientedRadialBoundaries
    (hGeometry : CanonicalParallelOrientedRadialBoundaryStatement (n := n)) :
    CanonicalParallelDoubleLayerStatement (n := n) := by
  intro A k
  obtain ⟨R, c, ⟨G⟩⟩ := hGeometry A k
  let B := simpleSpectrumApproximation A k
  have hB : HasDistinctEigenvalues B :=
    simpleSpectrumApproximation_hasDistinctEigenvalues A k
  have hWB : numericalRange B ⊆
      parallelOuterDomain (numericalRange A) k :=
    numericalRange_simpleSpectrumApproximation_subset_parallelOuterDomain A k
  exact G.hasDoubleLayerCompletionProvider_of_simpleDiagonalization
    R c B (simpleDiagonalization_of_hasDistinctEigenvalues B hB) hWB

/-- The manuscript's final theorem now follows from exactly the canonical radial-boundary
geometry statement. -/
theorem mainTheoremStatement_of_canonicalParallelOrientedRadialBoundaries
    (hGeometry : CanonicalParallelOrientedRadialBoundaryStatement (n := n)) :
    MainTheoremStatement (n := n) :=
  mainTheoremStatement_of_canonicalParallelDoubleLayer
    (canonicalParallelDoubleLayerStatement_of_orientedRadialBoundaries hGeometry)

/-- The manuscript's polynomial Crouzeix estimate with the exact constant `2`, for nonempty
finite complex Euclidean matrix spaces. -/
theorem crouzeixConjecture_mainTheorem : MainTheoremStatement (n := n) :=
  mainTheoremStatement_of_canonicalParallelOrientedRadialBoundaries
    canonicalParallelOrientedRadialBoundaryStatement

end CrouzeixConjecture
