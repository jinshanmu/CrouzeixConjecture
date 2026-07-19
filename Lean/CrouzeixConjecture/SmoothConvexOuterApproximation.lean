module

public import CrouzeixConjecture.Definitions
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CrouzeixConjecture

/-- The canonical positive radii used for outer parallel bodies. -/
def outerApproximationRadius (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1)

theorem outerApproximationRadius_pos (k : ℕ) :
    0 < outerApproximationRadius k := by
  unfold outerApproximationRadius
  positivity

theorem outerApproximationRadius_le_one (k : ℕ) :
    outerApproximationRadius k ≤ 1 := by
  unfold outerApproximationRadius
  apply (div_le_one (by positivity)).2
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

theorem tendsto_outerApproximationRadius :
    Tendsto outerApproximationRadius atTop (nhds 0) := by
  unfold outerApproximationRadius
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The open outer parallel body of `K` at the canonical radius. -/
def parallelOuterDomain (K : Set ℂ) (k : ℕ) : Set ℂ :=
  Metric.thickening (outerApproximationRadius k) K

/-- Exact nonsmooth geometric data supplied by a convex outer approximation. -/
structure ConvexOuterApproximationData
    (K Omega : Set ℂ) (radius : ℝ) : Prop where
  radius_pos : 0 < radius
  domain_isOpen : IsOpen Omega
  domain_isBounded : Bornology.IsBounded Omega
  domain_convex : Convex ℝ Omega
  domain_nonempty : Omega.Nonempty
  contains : K ⊆ Omega
  closure_eq_closedThickening :
    closure Omega = Metric.cthickening radius K
  closure_isCompact : IsCompact (closure Omega)
  closure_convex : Convex ℝ (closure Omega)
  closure_nonempty : (closure Omega).Nonempty
  closure_near : ∀ z ∈ closure Omega, ∃ w ∈ K, ‖z - w‖ ≤ radius

theorem parallelOuterDomain_closure
    (K : Set ℂ) (k : ℕ) :
    closure (parallelOuterDomain K k) =
      Metric.cthickening (outerApproximationRadius k) K := by
  exact closure_thickening (outerApproximationRadius_pos k) K

theorem parallelOuterDomain_closure_near
    {K : Set ℂ} (hKcompact : IsCompact K) (k : ℕ)
    {z : ℂ} (hz : z ∈ closure (parallelOuterDomain K k)) :
    ∃ w ∈ K, ‖z - w‖ ≤ outerApproximationRadius k := by
  rw [parallelOuterDomain_closure] at hz
  rw [hKcompact.cthickening_eq_biUnion_closedBall
    (outerApproximationRadius_pos k).le] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨w, hwK, hzw⟩ := hz
  exact ⟨w, hwK, by simpa [dist_eq_norm] using hzw⟩

theorem parallelOuterDomain_data
    {K : Set ℂ} (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKne : K.Nonempty)
    (k : ℕ) :
    ConvexOuterApproximationData K (parallelOuterDomain K k)
      (outerApproximationRadius k) := by
  refine
    { radius_pos := outerApproximationRadius_pos k
      domain_isOpen := Metric.isOpen_thickening
      domain_isBounded := hKcompact.isBounded.thickening
      domain_convex := hKconvex.thickening _
      domain_nonempty := hKne.mono
        (Metric.self_subset_thickening (outerApproximationRadius_pos k) K)
      contains := Metric.self_subset_thickening (outerApproximationRadius_pos k) K
      closure_eq_closedThickening := parallelOuterDomain_closure K k
      closure_isCompact := ?_
      closure_convex := ?_
      closure_nonempty := ?_
      closure_near := ?_ }
  · rw [parallelOuterDomain_closure]
    exact hKcompact.cthickening
  · rw [parallelOuterDomain_closure]
    exact hKconvex.cthickening _
  · exact hKne.mono <|
      (Metric.self_subset_thickening (outerApproximationRadius_pos k) K).trans
        subset_closure
  · intro z hz
    exact parallelOuterDomain_closure_near hKcompact k hz

theorem hausdorffDist_parallelOuterDomain_closure_le
    {K : Set ℂ} (hKcompact : IsCompact K) (k : ℕ) :
    Metric.hausdorffDist (closure (parallelOuterDomain K k)) K ≤
      outerApproximationRadius k := by
  apply Metric.hausdorffDist_le_of_mem_dist
    (outerApproximationRadius_pos k).le
  · intro z hz
    exact parallelOuterDomain_closure_near hKcompact k hz
  · intro w hw
    refine ⟨w, ?_, ?_⟩
    · exact subset_closure
        (Metric.self_subset_thickening (outerApproximationRadius_pos k) K hw)
    · simp [(outerApproximationRadius_pos k).le]

theorem tendsto_hausdorffDist_parallelOuterDomain_closure
    {K : Set ℂ} (hKcompact : IsCompact K) :
    Tendsto
      (fun k ↦ Metric.hausdorffDist
        (closure (parallelOuterDomain K k)) K)
      atTop (nhds 0) := by
  exact squeeze_zero
    (fun _ ↦ Metric.hausdorffDist_nonneg)
    (fun k ↦ hausdorffDist_parallelOuterDomain_closure_le hKcompact k)
    tendsto_outerApproximationRadius

/-- All canonical approximants lie in one fixed compact neighborhood of `K`. -/
theorem parallelOuterDomain_closure_subset_fixedNeighborhood
    (K : Set ℂ) (k : ℕ) :
    closure (parallelOuterDomain K k) ⊆ Metric.cthickening 1 K := by
  rw [parallelOuterDomain_closure]
  exact Metric.cthickening_mono (outerApproximationRadius_le_one k) K

theorem fixedOuterNeighborhood_isCompact
    {K : Set ℂ} (hKcompact : IsCompact K) :
    IsCompact (Metric.cthickening 1 K) :=
  hKcompact.cthickening

theorem exists_convexOuterApproximationSequence
    {K : Set ℂ} (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKne : K.Nonempty) :
    ∃ Omega : ℕ → Set ℂ, ∃ radius : ℕ → ℝ,
      Tendsto radius atTop (nhds 0) ∧
      (∀ k, ConvexOuterApproximationData K (Omega k) (radius k)) ∧
      Tendsto (fun k ↦ Metric.hausdorffDist (closure (Omega k)) K)
        atTop (nhds 0) := by
  exact ⟨parallelOuterDomain K, outerApproximationRadius,
    tendsto_outerApproximationRadius,
    parallelOuterDomain_data hKcompact hKconvex hKne,
    tendsto_hausdorffDist_parallelOuterDomain_closure hKcompact⟩

end CrouzeixConjecture
