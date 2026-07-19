module

public import CrouzeixConjecture.ParallelRadialDifferentiability
public import CrouzeixConjecture.RadialOrientation
public import CrouzeixConjecture.RadialContour

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace CrouzeixConjecture

/-- The inverse-gauge radius, bundled with its continuous derivative and `2π`-periodicity. -/
def parallelPositivePeriodicRadialData
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) : PositivePeriodicRadialData where
  radius := parallelGaugeRadius K c r
  radiusDeriv := deriv (parallelGaugeRadius K c r)
  radius_pos := parallelGaugeRadius_pos K hKcompact hc hr
  radius_hasDerivAt t :=
    ((contDiff_one_parallelGaugeRadius
      K hKne hKcompact hKconvex hc hr).differentiable_one t).hasDerivAt
  radiusDeriv_continuous :=
    (contDiff_one_parallelGaugeRadius
      K hKne hKcompact hKconvex hc hr).continuous_deriv_one
  radius_periodic := by
    simpa only [contourPeriod] using periodic_parallelGaugeRadius K c r

@[simp]
theorem parallelPositivePeriodicRadialData_radius
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).radius t =
      parallelGaugeRadius K c r t := rfl

@[simp]
theorem parallelPositivePeriodicRadialData_radiusDeriv
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).radiusDeriv t =
      deriv (parallelGaugeRadius K c r) t := rfl

@[simp]
theorem parallelPositivePeriodicRadialData_point
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).point c t =
      parallelRadialPoint K c r t := by
  simp only [PositivePeriodicRadialData.point,
    parallelPositivePeriodicRadialData_radius,
    parallelRadialPoint, parallelRadialDirection, Complex.real_smul]

theorem parallelPositivePeriodicRadialData_tangent_formula
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).tangent t =
      (((deriv (𝕜 := ℝ) (parallelGaugeRadius K c r) t : ℝ) : ℂ) +
        Complex.I * (parallelGaugeRadius K c r t : ℂ)) *
        parallelRadialDirection t := by
  simp only [PositivePeriodicRadialData.tangent,
    parallelPositivePeriodicRadialData_radius,
    parallelPositivePeriodicRadialData_radiusDeriv,
    parallelRadialDirection]

/-- The bundled radial contour lies on the frontier of the positive parallel body. -/
theorem parallelPositivePeriodicRadialData_point_mem_frontier
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).point c t ∈
      frontier (Metric.thickening r K) := by
  rw [parallelPositivePeriodicRadialData_point]
  exact parallelRadialPoint_mem_frontier_thickening
    K hKcompact hKconvex hc hr t

/-- Differentiating the constant squared-distance boundary equation makes the projection
normal orthogonal to the radial tangent. -/
theorem parallelPositivePeriodicRadialData_normal_tangent_orthogonal
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ⟪parallelBoundaryNormal K hKne hKcompact hKconvex r
        ((parallelPositivePeriodicRadialData
          K hKne hKcompact hKconvex hc hr).point c t),
      (parallelPositivePeriodicRadialData
        K hKne hKcompact hKconvex hc hr).tangent t⟫_ℝ = 0 := by
  let R := parallelPositivePeriodicRadialData
    K hKne hKcompact hKconvex hc hr
  let z := R.point c t
  have hdistance :=
    (hasFDerivAt_convexSquaredDistance K hKne hKcompact hKconvex z).comp_hasDerivAt t
      (R.point_hasDerivAt c t)
  have hfunction :
      convexSquaredDistance K hKne hKcompact hKconvex ∘ R.point c =
        fun _ : ℝ ↦ r ^ 2 := by
    funext s
    change convexSquaredDistance K hKne hKcompact hKconvex (R.point c s) = r ^ 2
    rw [show R.point c s = parallelRadialPoint K c r s by
      simpa only [R] using
        parallelPositivePeriodicRadialData_point
          K hKne hKcompact hKconvex hc hr s]
    exact convexSquaredDistance_parallelRadialPoint
      K hKne hKcompact hKconvex hc hr s
  rw [hfunction] at hdistance
  have hzero :
      (2 * ⟪z - convexProjection K hKne hKcompact hKconvex z,
        R.tangent t⟫_ℝ) = 0 := by
    have hderivative := hdistance.unique (hasDerivAt_const t (r ^ 2))
    simpa only [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      smul_eq_mul] using hderivative
  rw [parallelBoundaryNormal, real_inner_smul_left]
  have hinner : ⟪z - convexProjection K hKne hKcompact hKconvex z,
      R.tangent t⟫_ℝ = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  exact mul_eq_zero.mpr (Or.inr hinner)

/-- The normalized projection normal has positive component in the outward radial direction. -/
theorem parallelPositivePeriodicRadialData_normal_direction_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < ⟪parallelBoundaryNormal K hKne hKcompact hKconvex r
        ((parallelPositivePeriodicRadialData
          K hKne hKcompact hKconvex hc hr).point c t),
      parallelRadialDirection t⟫_ℝ := by
  let R := parallelPositivePeriodicRadialData
    K hKne hKcompact hKconvex hc hr
  have hfront : R.point c t ∈ frontier (Metric.thickening r K) := by
    simpa only [R] using
      parallelPositivePeriodicRadialData_point_mem_frontier
        K hKne hKcompact hKconvex hc hr t
  have hradius : 0 < R.radius t := R.radius_pos t
  have hray :
      R.point c t = c + R.radius t • parallelRadialDirection t := by
    simp only [R, parallelPositivePeriodicRadialData_point,
      parallelRadialPoint, parallelPositivePeriodicRadialData_radius]
  exact real_inner_parallelBoundaryNormal_direction_pos
    K hKne hKcompact hKconvex hr hfront hc hradius hray

/-- Every positive thickening of a nonempty compact convex planar set has the complete
positively oriented radial `C¹` boundary package consumed by the contour proof. -/
def orientedRadialConvexBoundary_thickening
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) :
    (parallelPositivePeriodicRadialData
      K hKne hKcompact hKconvex hc hr).OrientedRadialConvexBoundary c
        (Metric.thickening r K) := by
  let R := parallelPositivePeriodicRadialData
    K hKne hKcompact hKconvex hc hr
  let normal : C(ℝ, ℂ) :=
    ⟨fun t ↦ parallelBoundaryNormal K hKne hKcompact hKconvex r (R.point c t),
      (continuous_parallelBoundaryNormal K hKne hKcompact hKconvex r).comp
        (R.point_continuous c)⟩
  let speed : C(ℝ, ℝ) :=
    ⟨fun t ↦ ‖R.tangent t‖, R.tangent_continuous.norm⟩
  refine
    { domain :=
        { isOpen_domain := Metric.isOpen_thickening
          convex_domain := hKconvex.thickening r
          center_mem := Metric.self_subset_thickening hr K hc
          point_not_mem := ?_ }
      normal := normal
      speed := speed
      speed_nonneg := ?_
      supported := ?_
      tangent_eq := ?_ }
  · intro t ht hmem
    have hfront : R.point c t ∈ frontier (Metric.thickening r K) := by
      simpa only [R] using
        parallelPositivePeriodicRadialData_point_mem_frontier
          K hKne hKcompact hKconvex hc hr t
    have hinter : R.point c t ∈
        Metric.thickening r K ∩ frontier (Metric.thickening r K) :=
      ⟨hmem, hfront⟩
    rw [Metric.isOpen_thickening.inter_frontier_eq] at hinter
    exact hinter
  · intro t ht
    change 0 ≤ ‖R.tangent t‖
    exact norm_nonneg _
  · intro t ht
    exact outwardBoundarySupport_thickening
      K hKne hKcompact hKconvex hr
        (by
          simpa only [R] using
            parallelPositivePeriodicRadialData_point_mem_frontier
              K hKne hKcompact hKconvex hc hr t)
  · intro t ht
    have hnormal : ‖normal t‖ = 1 :=
      (outwardBoundarySupport_thickening
        K hKne hKcompact hKconvex hr
          (by
            simpa only [R] using
              parallelPositivePeriodicRadialData_point_mem_frontier
                K hKne hKcompact hKconvex hc hr t)).unit_normal
    have horth : ⟪normal t, R.tangent t⟫_ℝ = 0 := by
      simpa only [normal, R] using
        parallelPositivePeriodicRadialData_normal_tangent_orthogonal
          K hKne hKcompact hKconvex hc hr t
    have hforward : 0 < ⟪normal t, parallelRadialDirection t⟫_ℝ := by
      simpa only [normal, R] using
        parallelPositivePeriodicRadialData_normal_direction_pos
          K hKne hKcompact hKconvex hc hr t
    have htangent :
        R.tangent t =
          (((deriv (𝕜 := ℝ) (parallelGaugeRadius K c r) t : ℝ) : ℂ) +
            Complex.I * (parallelGaugeRadius K c r t : ℂ)) *
            parallelRadialDirection t := by
      simpa only [R] using
        parallelPositivePeriodicRadialData_tangent_formula
          K hKne hKcompact hKconvex hc hr t
    have hdirection : ‖parallelRadialDirection t‖ = 1 := by
      exact Complex.norm_exp_ofReal_mul_I t
    have hradius : 0 < parallelGaugeRadius K c r t :=
      parallelGaugeRadius_pos K hKcompact hc hr t
    have horiented := radialTangent_eq_I_mul_normal_mul_norm
      htangent hdirection hradius hnormal horth hforward
    simpa only [normal, speed, R, ContinuousMap.coe_mk] using horiented

/-- Existence form of the positive parallel-body radial boundary theorem. -/
theorem exists_orientedRadialConvexBoundary_thickening
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {r : ℝ} (hr : 0 < r) :
    ∃ R : PositivePeriodicRadialData, ∃ c : ℂ,
      Nonempty (R.OrientedRadialConvexBoundary c (Metric.thickening r K)) := by
  let c : ℂ := Classical.choose hKne
  have hc : c ∈ K := Classical.choose_spec hKne
  let R := parallelPositivePeriodicRadialData
    K hKne hKcompact hKconvex hc hr
  exact ⟨R, c, ⟨orientedRadialConvexBoundary_thickening
    K hKne hKcompact hKconvex hc hr⟩⟩

end CrouzeixConjecture
