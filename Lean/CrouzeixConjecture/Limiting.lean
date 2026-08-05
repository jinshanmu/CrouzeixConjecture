module

public import CrouzeixConjecture.Definitions
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix polynomial evaluation is continuous in its matrix argument. -/
theorem tendsto_polynomialEval {ι : Type*} {l : Filter ι} (p : Polynomial ℂ)
    {B : ι → SquareMatrix n} {A : SquareMatrix n} (hB : Tendsto B l (𝓝 A)) :
    Tendsto (fun k ↦ polynomialEval p (B k)) l (𝓝 (polynomialEval p A)) := by
  simpa only [polynomialEval] using (p.continuous_aeval.tendsto A).comp hB

/-- An eventual uniform bound on `‖p(B k)‖` is preserved when `B k` tends to
`A`.  This is the abstract topological limiting step used at the end of the
manuscript. -/
theorem norm_polynomialEval_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (p : Polynomial ℂ) {B : ι → SquareMatrix n} {A : SquareMatrix n} {C : ℝ}
    (hB : Tendsto B l (𝓝 A))
    (hBound : ∀ᶠ k in l, ‖polynomialEval p (B k)‖ ≤ C) :
    ‖polynomialEval p A‖ ≤ C := by
  exact le_of_tendsto (tendsto_polynomialEval p hB).norm hBound

end CrouzeixConjecture
