module

public import CrouzeixConjecture.ConvexDistance
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

noncomputable section

open Set
open scoped Pointwise Topology

namespace CrouzeixConjecture

/-- The positive parallel body, translated so that the chosen point `c` is the origin. -/
def translatedParallelDomain (K : Set ℂ) (c : ℂ) (r : ℝ) : Set ℂ :=
  (fun z : ℂ ↦ c + z) ⁻¹' Metric.thickening r K

/-- The unit vector of polar angle `t`. -/
def parallelRadialDirection (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I)

/-- The radial distance to the boundary of a translated parallel body, defined as the
inverse of its Minkowski gauge in the corresponding unit direction. -/
def parallelGaugeRadius (K : Set ℂ) (c : ℂ) (r : ℝ) (t : ℝ) : ℝ :=
  (gauge (translatedParallelDomain K c r) (parallelRadialDirection t))⁻¹

/-- The polar boundary point of a parallel body, translated back to the original center. -/
def parallelRadialPoint (K : Set ℂ) (c : ℂ) (r : ℝ) (t : ℝ) : ℂ :=
  c + parallelGaugeRadius K c r t • parallelRadialDirection t

/-- The translated parallel body is open. -/
theorem isOpen_translatedParallelDomain (K : Set ℂ) (c : ℂ) (r : ℝ) :
    IsOpen (translatedParallelDomain K c r) := by
  exact Metric.isOpen_thickening.preimage (continuous_const.add continuous_id)

/-- Translation preserves convexity of the parallel body. -/
theorem convex_translatedParallelDomain
    (K : Set ℂ) (hKconvex : Convex ℝ K) (c : ℂ) (r : ℝ) :
    Convex ℝ (translatedParallelDomain K c r) := by
  exact (hKconvex.thickening r).translate_preimage_right c

/-- A chosen point of `K` becomes the origin in the translated positive parallel body. -/
theorem zero_mem_translatedParallelDomain
    (K : Set ℂ) {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) :
    (0 : ℂ) ∈ translatedParallelDomain K c r := by
  change c + 0 ∈ Metric.thickening r K
  simpa only [add_zero] using Metric.self_subset_thickening hr K hc

/-- The translated positive parallel body is a neighborhood of the origin. -/
theorem translatedParallelDomain_mem_nhds_zero
    (K : Set ℂ) {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) :
    translatedParallelDomain K c r ∈ nhds (0 : ℂ) :=
  (isOpen_translatedParallelDomain K c r).mem_nhds
    (zero_mem_translatedParallelDomain K hc hr)

/-- Translating a bounded parallel body back to the origin preserves boundedness. -/
theorem isBounded_translatedParallelDomain
    (K : Set ℂ) (hKcompact : IsCompact K) (c : ℂ) (r : ℝ) :
    Bornology.IsBounded (translatedParallelDomain K c r) := by
  have hthick : Bornology.IsBounded (Metric.thickening r K) :=
    hKcompact.isBounded.thickening
  obtain ⟨C, hC⟩ := hthick.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨C + ‖c‖, ?_⟩
  intro z hz
  have hcz : c + z ∈ Metric.thickening r K := hz
  calc
    ‖z‖ = ‖(c + z) - c‖ := by congr 1; abel
    _ ≤ ‖c + z‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ C + ‖c‖ := by linarith [hC (c + z) hcz]

/-- The polar direction is never zero. -/
theorem parallelRadialDirection_ne_zero (t : ℝ) :
    parallelRadialDirection t ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- The polar direction depends continuously on the angle. -/
theorem continuous_parallelRadialDirection :
    Continuous parallelRadialDirection := by
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

/-- The polar direction has real period `2π`. -/
theorem periodic_parallelRadialDirection :
    Function.Periodic parallelRadialDirection (2 * Real.pi) := by
  intro t
  simp only [parallelRadialDirection]
  simp [add_mul, Complex.exp_periodic _]

/-- The gauge of every unit direction is strictly positive. -/
theorem gauge_parallelRadialDirection_pos
    (K : Set ℂ) (hKcompact : IsCompact K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < gauge (translatedParallelDomain K c r) (parallelRadialDirection t) := by
  have habsorbent : Absorbent ℝ (translatedParallelDomain K c r) :=
    absorbent_nhds_zero (translatedParallelDomain_mem_nhds_zero K hc hr)
  have hbounded : Bornology.IsVonNBounded ℝ (translatedParallelDomain K c r) :=
    (NormedSpace.isVonNBounded_iff ℝ).2
      (isBounded_translatedParallelDomain K hKcompact c r)
  exact (gauge_pos habsorbent hbounded).2 (parallelRadialDirection_ne_zero t)

/-- The inverse-gauge radial distance is strictly positive. -/
theorem parallelGaugeRadius_pos
    (K : Set ℂ) (hKcompact : IsCompact K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < parallelGaugeRadius K c r t := by
  exact inv_pos.mpr (gauge_parallelRadialDirection_pos K hKcompact hc hr t)

/-- The inverse-gauge radial distance depends continuously on the angle. -/
theorem continuous_parallelGaugeRadius
    (K : Set ℂ) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) :
    Continuous (parallelGaugeRadius K c r) := by
  apply Continuous.inv₀
  · exact
      (continuous_gauge
          (convex_translatedParallelDomain K hKconvex c r)
          (translatedParallelDomain_mem_nhds_zero K hc hr)).comp
        continuous_parallelRadialDirection
  · intro t
    exact (gauge_parallelRadialDirection_pos K hKcompact hc hr t).ne'

/-- The inverse-gauge radial distance has period `2π`. -/
theorem periodic_parallelGaugeRadius
    (K : Set ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (parallelGaugeRadius K c r) (2 * Real.pi) := by
  intro t
  unfold parallelGaugeRadius
  rw [periodic_parallelRadialDirection t]

/-- The inverse-gauge radius normalizes its direction to gauge one. -/
theorem gauge_radialVector_eq_one
    (K : Set ℂ) (hKcompact : IsCompact K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    gauge (translatedParallelDomain K c r)
        (parallelGaugeRadius K c r t • parallelRadialDirection t) = 1 := by
  rw [gauge_smul_of_nonneg
    (parallelGaugeRadius_pos K hKcompact hc hr t).le]
  change parallelGaugeRadius K c r t *
      gauge (translatedParallelDomain K c r) (parallelRadialDirection t) = 1
  unfold parallelGaugeRadius
  exact inv_mul_cancel₀
    (gauge_parallelRadialDirection_pos K hKcompact hc hr t).ne'

/-- The normalized radial vector lies on the frontier of the translated parallel body. -/
theorem radialVector_mem_frontier_translatedParallelDomain
    (K : Set ℂ) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    parallelGaugeRadius K c r t • parallelRadialDirection t ∈
      frontier (translatedParallelDomain K c r) := by
  apply (gauge_eq_one_iff_mem_frontier
    (convex_translatedParallelDomain K hKconvex c r)
    (translatedParallelDomain_mem_nhds_zero K hc hr)).mp
  exact gauge_radialVector_eq_one K hKcompact hc hr t

/-- The polar point lies on the frontier of the original positive parallel body. -/
theorem parallelRadialPoint_mem_frontier_thickening
    (K : Set ℂ) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    parallelRadialPoint K c r t ∈ frontier (Metric.thickening r K) := by
  have hv := radialVector_mem_frontier_translatedParallelDomain
    K hKcompact hKconvex hc hr t
  have hv' :
      parallelGaugeRadius K c r t • parallelRadialDirection t ∈
        frontier ((Homeomorph.addLeft c) ⁻¹' Metric.thickening r K) := by
    simpa only [translatedParallelDomain] using hv
  rw [← (Homeomorph.addLeft c).preimage_frontier] at hv'
  simpa only [Set.mem_preimage, Homeomorph.coe_addLeft,
    parallelRadialPoint] using hv'

/-- The polar boundary point depends continuously on the angle. -/
theorem continuous_parallelRadialPoint
    (K : Set ℂ) (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    {c : ℂ} (hc : c ∈ K) {r : ℝ} (hr : 0 < r) :
    Continuous (parallelRadialPoint K c r) := by
  exact continuous_const.add
    ((continuous_parallelGaugeRadius K hKcompact hKconvex hc hr).smul
      continuous_parallelRadialDirection)

/-- The polar boundary point has period `2π`. -/
theorem periodic_parallelRadialPoint
    (K : Set ℂ) (c : ℂ) (r : ℝ) :
    Function.Periodic (parallelRadialPoint K c r) (2 * Real.pi) := by
  intro t
  unfold parallelRadialPoint
  rw [periodic_parallelGaugeRadius K c r t,
    periodic_parallelRadialDirection t]

/-- Squared distance to `K` is exactly `r²` along the inverse-gauge boundary point. -/
theorem convexSquaredDistance_parallelRadialPoint
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    convexSquaredDistance K hKne hKcompact hKconvex
        (parallelRadialPoint K c r t) = r ^ 2 := by
  have hfront := parallelRadialPoint_mem_frontier_thickening
    K hKcompact hKconvex hc hr t
  rw [frontier_thickening_eq_infDist_level K hKne hr] at hfront
  unfold convexSquaredDistance
  rw [← infDist_eq_norm_sub_convexProjection
    K hKne hKcompact hKconvex (parallelRadialPoint K c r t), hfront]

end CrouzeixConjecture
