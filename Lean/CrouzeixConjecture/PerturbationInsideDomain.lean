module

public import CrouzeixConjecture.NumericalRange
public import CrouzeixConjecture.SimpleSpectrumDensity
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If matrices converge to `A`, their numerical ranges are eventually contained in every open
set containing `W(A)`.  This is the compact-buffer step based on
`eq:numerical-range-Lipschitz`, using the exact induced Euclidean operator norm perturbation
estimate. -/
theorem eventually_numericalRange_subset_open_of_tendsto
    {kappa : Type*} {l : Filter kappa}
    (A : SquareMatrix n) {B : kappa → SquareMatrix n}
    (hB : Tendsto B l (nhds A))
    {Omega : Set ℂ} (hOmegaOpen : IsOpen Omega)
    (hWA : numericalRange A ⊆ Omega) :
    ∀ᶠ k in l, numericalRange (B k) ⊆ Omega := by
  obtain ⟨delta, hdelta, hbuffer⟩ :=
    (isCompact_numericalRange A).exists_cthickening_subset_open hOmegaOpen hWA
  have hclose : ∀ᶠ k in l, dist (B k) A < delta :=
    (Metric.tendsto_nhds.1 hB delta hdelta)
  filter_upwards [hclose] with k hk
  intro z hz
  obtain ⟨w, hw, hzw⟩ := numericalRange_perturbation A (B k) hz
  apply hbuffer
  apply Metric.mem_cthickening_of_dist_le z w delta (numericalRange A) hw
  rw [dist_eq_norm]
  exact (hzw.trans_lt (by simpa [dist_eq_norm] using hk)).le

/-- Sequence specialization for the concrete simple-spectrum approximants. -/
theorem eventually_simpleSpectrumApproximation_numericalRange_subset_open
    [Nonempty n] (A : SquareMatrix n)
    {Omega : Set ℂ} (hOmegaOpen : IsOpen Omega)
    (hWA : numericalRange A ⊆ Omega) :
    ∀ᶠ k in atTop, numericalRange (simpleSpectrumApproximation A k) ⊆ Omega :=
  eventually_numericalRange_subset_open_of_tendsto A
    (tendsto_simpleSpectrumApproximation A) hOmegaOpen hWA

end CrouzeixConjecture
