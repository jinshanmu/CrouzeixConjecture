module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace CrouzeixConjecture

/-- The metric projection onto a nonempty compact convex subset of the complex plane. -/
def convexProjection
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) : ℂ :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex
      hKne hKcompact.isComplete hKconvex z)

/-- The metric projection belongs to the convex set. -/
theorem convexProjection_mem
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) :
    convexProjection K hKne hKcompact hKconvex z ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      hKne hKcompact.isComplete hKconvex z)).1

/-- The projection realizes the infimum of the distances to the convex set. -/
theorem norm_sub_convexProjection_eq_iInf
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) :
    ‖z - convexProjection K hKne hKcompact hKconvex z‖ =
      ⨅ w : K, ‖z - w‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex
      hKne hKcompact.isComplete hKconvex z)).2

/-- The real infimum distance to a compact convex set is the norm of the projection residual. -/
theorem infDist_eq_norm_sub_convexProjection
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) :
    Metric.infDist z K =
      ‖z - convexProjection K hKne hKcompact hKconvex z‖ := by
  rw [Metric.infDist_eq_iInf]
  simpa only [dist_eq_norm] using
    (norm_sub_convexProjection_eq_iInf K hKne hKcompact hKconvex z).symm

/-- Variational characterization of the metric projection. -/
theorem convexProjection_variational
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z w : ℂ) (hw : w ∈ K) :
    ⟪z - convexProjection K hKne hKcompact hKconvex z,
      w - convexProjection K hKne hKcompact hKconvex z⟫_ℝ ≤ 0 := by
  exact
    (norm_eq_iInf_iff_real_inner_le_zero hKconvex
      (convexProjection_mem K hKne hKcompact hKconvex z)).mp
      (norm_sub_convexProjection_eq_iInf K hKne hKcompact hKconvex z) w hw

/-- A point of the convex set satisfying the projection variational inequality is the projection. -/
theorem eq_convexProjection_of_mem_of_variational
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) {v : ℂ} (hv : v ∈ K)
    (hvar : ∀ w ∈ K, ⟪z - v, w - v⟫_ℝ ≤ 0) :
    v = convexProjection K hKne hKcompact hKconvex z := by
  let p := convexProjection K hKne hKcompact hKconvex z
  have hp : p ∈ K := by
    simpa only [p] using convexProjection_mem K hKne hKcompact hKconvex z
  have hvp : ⟪z - v, p - v⟫_ℝ ≤ 0 := hvar p hp
  have hpv : ⟪z - p, v - p⟫_ℝ ≤ 0 := by
    simpa only [p] using
      convexProjection_variational K hKne hKcompact hKconvex z v hv
  have hself : ⟪v - p, v - p⟫_ℝ ≤ 0 := by
    calc
      ⟪v - p, v - p⟫_ℝ =
          ⟪z - v, p - v⟫_ℝ + ⟪z - p, v - p⟫_ℝ := by
        simp only [inner_sub_left, inner_sub_right]
        ring
      _ ≤ 0 := add_nonpos hvp hpv
  exact sub_eq_zero.mp (real_inner_self_nonpos.mp hself)

/-- The metric projection is firmly nonexpansive in the real inner product. -/
theorem convexProjection_firm_nonexpansive
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x y : ℂ) :
    ⟪convexProjection K hKne hKcompact hKconvex x -
        convexProjection K hKne hKcompact hKconvex y,
      convexProjection K hKne hKcompact hKconvex x -
        convexProjection K hKne hKcompact hKconvex y⟫_ℝ ≤
      ⟪x - y,
        convexProjection K hKne hKcompact hKconvex x -
          convexProjection K hKne hKcompact hKconvex y⟫_ℝ := by
  let p := convexProjection K hKne hKcompact hKconvex x
  let q := convexProjection K hKne hKcompact hKconvex y
  change ⟪p - q, p - q⟫_ℝ ≤ ⟪x - y, p - q⟫_ℝ
  have hp : p ∈ K := by
    simpa only [p] using convexProjection_mem K hKne hKcompact hKconvex x
  have hq : q ∈ K := by
    simpa only [q] using convexProjection_mem K hKne hKcompact hKconvex y
  have hxp : ⟪x - p, q - p⟫_ℝ ≤ 0 := by
    simpa only [p] using
      convexProjection_variational K hKne hKcompact hKconvex x q hq
  have hyq : ⟪y - q, p - q⟫_ℝ ≤ 0 := by
    simpa only [q] using
      convexProjection_variational K hKne hKcompact hKconvex y p hp
  have hid :
      ⟪x - y, p - q⟫_ℝ - ⟪p - q, p - q⟫_ℝ =
        -⟪x - p, q - p⟫_ℝ - ⟪y - q, p - q⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  linarith

/-- The metric projection does not increase Euclidean distances. -/
theorem norm_convexProjection_sub_le
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x y : ℂ) :
    ‖convexProjection K hKne hKcompact hKconvex x -
        convexProjection K hKne hKcompact hKconvex y‖ ≤ ‖x - y‖ := by
  let p := convexProjection K hKne hKcompact hKconvex x
  let q := convexProjection K hKne hKcompact hKconvex y
  change ‖p - q‖ ≤ ‖x - y‖
  have hfirm : ⟪p - q, p - q⟫_ℝ ≤ ⟪x - y, p - q⟫_ℝ := by
    simpa only [p, q] using
      convexProjection_firm_nonexpansive K hKne hKcompact hKconvex x y
  have hprod : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by
    calc
      ‖p - q‖ * ‖p - q‖ = ⟪p - q, p - q⟫_ℝ :=
        (real_inner_self_eq_norm_mul_norm (p - q)).symm
      _ ≤ ⟪x - y, p - q⟫_ℝ := hfirm
      _ ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  by_cases hd : ‖p - q‖ = 0
  · simpa only [hd] using norm_nonneg (x - y)
  · have hdpos : 0 < ‖p - q‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    exact le_of_mul_le_mul_right hprod hdpos

/-- The metric projection is `1`-Lipschitz. -/
theorem convexProjection_lipschitzWith_one
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) :
    LipschitzWith 1 (convexProjection K hKne hKcompact hKconvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    norm_convexProjection_sub_le K hKne hKcompact hKconvex x y

/-- The metric projection is continuous. -/
theorem continuous_convexProjection
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) :
    Continuous (convexProjection K hKne hKcompact hKconvex) :=
  (convexProjection_lipschitzWith_one K hKne hKcompact hKconvex).continuous

/-- The frontier of a positive open thickening is exactly an `infEDist` level set. -/
theorem frontier_thickening_eq_infEDist_level
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) {r : ℝ} (hr : 0 < r) :
    frontier (Metric.thickening r K) =
      {x | Metric.infEDist x K = ENNReal.ofReal r} := by
  have hopen : IsOpen (Metric.thickening r K) := Metric.isOpen_thickening
  rw [hopen.frontier_eq, closure_thickening hr K]
  ext x
  simp only [Set.mem_diff, Metric.mem_cthickening_iff,
    Metric.mem_thickening_iff_infEDist_lt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hle, hnlt⟩
    exact le_antisymm hle (not_lt.mp hnlt)
  · intro h
    refine ⟨h.le, ?_⟩
    simpa only [h] using (lt_irrefl (ENNReal.ofReal r))

/-- For a nonempty set, the frontier of a positive open thickening is the corresponding
real infimum-distance level set. -/
theorem frontier_thickening_eq_infDist_level
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hKne : K.Nonempty) {r : ℝ} (hr : 0 < r) :
    frontier (Metric.thickening r K) =
      {x | Metric.infDist x K = r} := by
  rw [frontier_thickening_eq_infEDist_level K hr]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    change ENNReal.toReal (Metric.infEDist x K) = r
    rw [h, ENNReal.toReal_ofReal hr.le]
  · intro h
    change ENNReal.toReal (Metric.infEDist x K) = r at h
    have hh := congrArg ENNReal.ofReal h
    rw [ENNReal.ofReal_toReal
      (Metric.infEDist_ne_top (s := K) (x := x) hKne)] at hh
    exact hh

end CrouzeixConjecture
