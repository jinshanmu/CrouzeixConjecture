module

public import CrouzeixConjecture.CanonicalParallelRadialGeometry
public import CrouzeixConjecture.MainOuterLimit

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The radial boundary geometry supplies the double-layer completion for every simple auxiliary
matrix lying in a fixed canonical outer body. -/
theorem canonicalParallelDoubleLayerStatement_of_orientedRadialBoundaries
    (hGeometry : CanonicalParallelOrientedRadialBoundaryStatement (n := n)) :
    CanonicalParallelDoubleLayerStatement (n := n) := by
  intro A B k hB hWB
  obtain ⟨R, c, ⟨G⟩⟩ := hGeometry A k
  exact G.hasDoubleLayerCompletionProvider_of_simpleDiagonalization
    R c B (simpleDiagonalization_of_hasDistinctEigenvalues B hB) hWB

/-- The polynomial endpoint follows from exactly the canonical radial-boundary geometry
statement. -/
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
