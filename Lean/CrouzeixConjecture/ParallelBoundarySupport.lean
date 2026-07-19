module

public import CrouzeixConjecture.ConvexProjection
public import CrouzeixConjecture.DoubleLayerGeometry

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace CrouzeixConjecture

/-- The outward normal field of a positive parallel body, expressed using metric projection
onto its compact convex core. -/
def parallelBoundaryNormal
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (r : ℝ) (z : ℂ) : ℂ :=
  r⁻¹ • (z - convexProjection K hKne hKcompact hKconvex z)

/-- The parallel-body normal field is continuous on the whole plane. -/
theorem continuous_parallelBoundaryNormal
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (r : ℝ) :
    Continuous (parallelBoundaryNormal K hKne hKcompact hKconvex r) := by
  exact continuous_const.smul
    (continuous_id.sub (continuous_convexProjection K hKne hKcompact hKconvex))

/-- At the frontier of a positive thickening, the projection residual has exactly the
thickening radius as its norm. -/
theorem norm_sub_convexProjection_eq_of_mem_frontier_thickening
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) :
    ‖z - convexProjection K hKne hKcompact hKconvex z‖ = r := by
  rw [← infDist_eq_norm_sub_convexProjection K hKne hKcompact hKconvex]
  have hlevel : Metric.infDist z K = r := by
    have : z ∈ {w : ℂ | Metric.infDist w K = r} := by
      rwa [← frontier_thickening_eq_infDist_level K hKne hr]
    exact this
  exact hlevel

/-- The projection residual at a parallel-body boundary point points strictly away from every
point of the open thickening. -/
theorem real_inner_projectionResidual_sub_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) {y : ℂ}
    (hy : y ∈ Metric.thickening r K) :
    0 < ⟪z - convexProjection K hKne hKcompact hKconvex z, z - y⟫_ℝ := by
  let p := convexProjection K hKne hKcompact hKconvex z
  have hp : p ∈ K := by
    simpa only [p] using
      convexProjection_mem K hKne hKcompact hKconvex z
  have hresidual : ‖z - p‖ = r := by
    simpa only [p] using
      norm_sub_convexProjection_eq_of_mem_frontier_thickening
        K hKne hKcompact hKconvex hr hz
  obtain ⟨w, hw, hyw⟩ := Metric.mem_thickening_iff.mp hy
  have hywnorm : ‖y - w‖ < r := by
    simpa only [dist_eq_norm] using hyw
  have hvariational : ⟪z - p, w - p⟫_ℝ ≤ 0 := by
    simpa only [p] using
      convexProjection_variational K hKne hKcompact hKconvex z w hw
  have hcauchy : ⟪z - p, y - w⟫_ℝ ≤ ‖z - p‖ * ‖y - w‖ :=
    real_inner_le_norm _ _
  have hstrict : ‖z - p‖ * ‖y - w‖ < r * r := by
    rw [hresidual]
    exact mul_lt_mul_of_pos_left hywnorm hr
  have hforward : ⟪z - p, y - p⟫_ℝ < r * r := by
    calc
      ⟪z - p, y - p⟫_ℝ =
          ⟪z - p, w - p⟫_ℝ + ⟪z - p, y - w⟫_ℝ := by
        simp only [inner_sub_right]
        ring
      _ ≤ 0 + ‖z - p‖ * ‖y - w‖ := add_le_add hvariational hcauchy
      _ < r * r := by simpa only [zero_add] using hstrict
  calc
    0 < r * r - ⟪z - p, y - p⟫_ℝ := sub_pos.mpr hforward
    _ = ⟪z - p, z - y⟫_ℝ := by
      rw [← hresidual, ← real_inner_self_eq_norm_mul_norm]
      simp only [inner_sub_right]
      ring

/-- At a parallel-body boundary point, the projection residual has strictly positive
component away from every chosen point of the compact convex core. -/
theorem real_inner_projectionResidual_sub_corePoint_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z c : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) (hc : c ∈ K) :
    0 < ⟪z - convexProjection K hKne hKcompact hKconvex z, z - c⟫_ℝ := by
  let p := convexProjection K hKne hKcompact hKconvex z
  have hresidual : ‖z - p‖ = r := by
    simpa only [p] using
      norm_sub_convexProjection_eq_of_mem_frontier_thickening
        K hKne hKcompact hKconvex hr hz
  have hvariational : ⟪z - p, c - p⟫_ℝ ≤ 0 := by
    simpa only [p] using
      convexProjection_variational K hKne hKcompact hKconvex z c hc
  calc
    0 < r * r := mul_pos hr hr
    _ = ⟪z - p, z - p⟫_ℝ := by
      rw [real_inner_self_eq_norm_mul_norm, hresidual]
    _ ≤ ⟪z - p, z - p⟫_ℝ - ⟪z - p, c - p⟫_ℝ := by
      linarith
    _ = ⟪z - p, z - c⟫_ℝ := by
      simp only [inner_sub_right]
      ring

/-- If a parallel-body boundary point is written on a positive ray from a core point, then
the projection residual has strictly positive component along that ray. -/
theorem real_inner_projectionResidual_direction_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z c u : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) (hc : c ∈ K)
    {rho : ℝ} (hrho : 0 < rho) (hzray : z = c + rho • u) :
    0 < ⟪z - convexProjection K hKne hKcompact hKconvex z, u⟫_ℝ := by
  have hpositive :=
    real_inner_projectionResidual_sub_corePoint_pos
      K hKne hKcompact hKconvex hr hz hc
  have hproduct :
      0 < rho *
        ⟪z - convexProjection K hKne hKcompact hKconvex z, u⟫_ℝ := by
    convert hpositive using 1
    rw [hzray]
    simp only [add_sub_cancel_left, real_inner_smul_right]
  exact pos_of_mul_pos_right hproduct hrho.le

/-- The normalized parallel-body normal has strictly positive component along every positive
radial representation based at a point of the core. -/
theorem real_inner_parallelBoundaryNormal_direction_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z c u : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) (hc : c ∈ K)
    {rho : ℝ} (hrho : 0 < rho) (hzray : z = c + rho • u) :
    0 < ⟪parallelBoundaryNormal K hKne hKcompact hKconvex r z, u⟫_ℝ := by
  rw [parallelBoundaryNormal, real_inner_smul_left]
  exact mul_pos (inv_pos.mpr hr)
    (real_inner_projectionResidual_direction_pos
      K hKne hKcompact hKconvex hr hz hc hrho hzray)

/-- The normalized projection residual is the exact outward supporting unit normal of a
positive convex parallel body. -/
theorem outwardBoundarySupport_thickening
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ frontier (Metric.thickening r K)) :
    OutwardBoundarySupport (Metric.thickening r K) z
      (parallelBoundaryNormal K hKne hKcompact hKconvex r z) := by
  refine
    { isOpen_domain := Metric.isOpen_thickening
      boundary_point := hz
      unit_normal := ?_
      support_inequality := ?_ }
  · rw [parallelBoundaryNormal, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hr]
    rw [norm_sub_convexProjection_eq_of_mem_frontier_thickening
      K hKne hKcompact hKconvex hr hz]
    exact inv_mul_cancel₀ hr.ne'
  · intro y hy
    have hpositive :=
      real_inner_projectionResidual_sub_pos
        K hKne hKcompact hKconvex hr hz hy
    have hscaled :
        0 ≤ ⟪parallelBoundaryNormal K hKne hKcompact hKconvex r z,
          z - y⟫_ℝ := by
      rw [parallelBoundaryNormal, real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.mpr hr.le) hpositive.le
    simpa only [real_inner_eq_re_inner, RCLike.inner_apply',
      starRingEnd_apply] using hscaled

end CrouzeixConjecture
