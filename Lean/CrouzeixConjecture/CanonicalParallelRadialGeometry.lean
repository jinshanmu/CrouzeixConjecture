module

public import CrouzeixConjecture.ParallelRadialBoundary
public import CrouzeixConjecture.NumericalRangeConvexity
public import CrouzeixConjecture.SmoothConvexOuterApproximation

@[expose] public section

noncomputable section

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A bounded open convex domain has the exact radial `C¹` boundary package consumed by
the proved Cauchy and double-layer constructions. -/
def HasOrientedRadialConvexBoundary (Omega : Set ℂ) : Prop :=
  ∃ R : PositivePeriodicRadialData, ∃ c : ℂ,
    Nonempty (R.OrientedRadialConvexBoundary c Omega)

/-- The geometric statement for the canonical parallel bodies used in the
holomorphic outer-limit argument. -/
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

end CrouzeixConjecture
