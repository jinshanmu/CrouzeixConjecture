module

public import CrouzeixConjecture.ParallelRadialTopology
public import CrouzeixConjecture.ParallelBoundarySupport
public import CrouzeixConjecture.ScalarImplicit
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

noncomputable section

open scoped InnerProductSpace Topology

namespace CrouzeixConjecture

/-- The two-variable polar point map before solving the boundary equation. -/
def parallelRadialParameterPoint (c : ℂ) (ts : ℝ × ℝ) : ℂ :=
  c + ts.2 • parallelRadialDirection ts.1

/-- The polar point map is continuously differentiable in angle and radius. -/
theorem contDiff_one_parallelRadialParameterPoint (c : ℂ) :
    ContDiff ℝ 1 (parallelRadialParameterPoint c) := by
  have ht : ContDiff ℝ 1 (fun ts : ℝ × ℝ ↦ (ts.1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hs : ContDiff ℝ 1 (fun ts : ℝ × ℝ ↦ (ts.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have hdirection :
      ContDiff ℝ 1 (fun ts : ℝ × ℝ ↦ parallelRadialDirection ts.1) := by
    exact (ht.mul contDiff_const).cexp
  unfold parallelRadialParameterPoint
  exact contDiff_const.add (hs.mul hdirection)

/-- The scalar equation whose positive root is the inverse-gauge radius. -/
def parallelRadialDistanceEquation
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (c : ℂ) (r : ℝ) (ts : ℝ × ℝ) : ℝ :=
  convexSquaredDistance K hKne hKcompact hKconvex
      (parallelRadialParameterPoint c ts) - r ^ 2

/-- The radial distance equation is `C¹`. -/
theorem contDiff_one_parallelRadialDistanceEquation
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (c : ℂ) (r : ℝ) :
    ContDiff ℝ 1
      (parallelRadialDistanceEquation K hKne hKcompact hKconvex c r) := by
  unfold parallelRadialDistanceEquation
  exact
    ((contDiff_one_convexSquaredDistance K hKne hKcompact hKconvex).comp
      (contDiff_one_parallelRadialParameterPoint c)).sub contDiff_const

/-- Substituting the inverse-gauge radius solves the distance equation globally. -/
theorem parallelRadialDistanceEquation_root
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    parallelRadialDistanceEquation K hKne hKcompact hKconvex c r
        (t, parallelGaugeRadius K c r t) = 0 := by
  rw [parallelRadialDistanceEquation]
  have hpoint :
      parallelRadialParameterPoint c (t, parallelGaugeRadius K c r t) =
        parallelRadialPoint K c r t := rfl
  rw [hpoint,
    convexSquaredDistance_parallelRadialPoint
      K hKne hKcompact hKconvex hc hr t, sub_self]

/-- Along a fixed polar direction, the parameter point has derivative equal to that direction. -/
theorem parallelRadialParameterPoint_slice_hasDerivAt
    (c : ℂ) (t s : ℝ) :
    HasDerivAt (fun y : ℝ ↦ parallelRadialParameterPoint c (t, y))
      (parallelRadialDirection t) s := by
  have hbase : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) (1 : ℂ) s :=
    Complex.ofRealCLM.hasDerivAt
  have h := hbase.mul_const (parallelRadialDirection t)
  simpa only [one_mul] using h.const_add c

/-- The derivative of the distance equation in the radial variable is twice the radial
component of the projection residual. -/
theorem parallelRadialDistanceEquation_slice_hasDerivAt
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (c : ℂ) (r t s : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦
        parallelRadialDistanceEquation K hKne hKcompact hKconvex c r (t, y))
      (2 * ⟪parallelRadialParameterPoint c (t, s) -
          convexProjection K hKne hKcompact hKconvex
            (parallelRadialParameterPoint c (t, s)),
        parallelRadialDirection t⟫_ℝ) s := by
  have hdistance :=
    (hasFDerivAt_convexSquaredDistance K hKne hKcompact hKconvex
      (parallelRadialParameterPoint c (t, s))).comp_hasDerivAt s
        (parallelRadialParameterPoint_slice_hasDerivAt c t s)
  have hsub := hdistance.sub_const (r ^ 2)
  simpa only [parallelRadialDistanceEquation,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul] using hsub

/-- The radial partial derivative at every inverse-gauge boundary point is strictly positive. -/
theorem fderiv_parallelRadialDistanceEquation_radial_pos
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < fderiv ℝ
      (parallelRadialDistanceEquation K hKne hKcompact hKconvex c r)
      (t, parallelGaugeRadius K c r t) (0, 1) := by
  let rho := parallelGaugeRadius K c r t
  let z := parallelRadialPoint K c r t
  have hFdiff : DifferentiableAt ℝ
      (parallelRadialDistanceEquation K hKne hKcompact hKconvex c r)
      (t, rho) :=
    (contDiff_one_parallelRadialDistanceEquation
      K hKne hKcompact hKconvex c r).differentiable_one (t, rho)
  have hslice := parallelRadialDistanceEquation_slice_hasDerivAt
    K hKne hKcompact hKconvex c r t rho
  have hpartial := fderiv_apply_inr_one_eq_of_hasDerivAt_slice
    (parallelRadialDistanceEquation K hKne hKcompact hKconvex c r)
    t rho
    (2 * ⟪parallelRadialParameterPoint c (t, rho) -
        convexProjection K hKne hKcompact hKconvex
          (parallelRadialParameterPoint c (t, rho)),
      parallelRadialDirection t⟫_ℝ)
    hFdiff hslice
  have hfront : z ∈ frontier (Metric.thickening r K) := by
    exact parallelRadialPoint_mem_frontier_thickening
      K hKcompact hKconvex hc hr t
  have hrho : 0 < rho := by
    exact parallelGaugeRadius_pos K hKcompact hc hr t
  have hray : z = c + rho • parallelRadialDirection t := rfl
  have hinner :
      0 < ⟪z - convexProjection K hKne hKcompact hKconvex z,
        parallelRadialDirection t⟫_ℝ :=
    real_inner_projectionResidual_direction_pos
      K hKne hKcompact hKconvex hr hfront hc hrho hray
  rw [hpartial]
  simpa only [rho, z] using mul_pos (by norm_num : (0 : ℝ) < 2) hinner

/-- The inverse-gauge radial function of a positive compact convex parallel body is `C¹`. -/
theorem contDiff_one_parallelGaugeRadius
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) {c : ℂ} (hc : c ∈ K)
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 1 (parallelGaugeRadius K c r) := by
  apply contDiff_one_of_continuous_implicit_scalar
    (parallelRadialDistanceEquation K hKne hKcompact hKconvex c r)
  · exact contDiff_one_parallelRadialDistanceEquation
      K hKne hKcompact hKconvex c r
  · exact continuous_parallelGaugeRadius K hKcompact hKconvex hc hr
  · exact parallelRadialDistanceEquation_root
      K hKne hKcompact hKconvex hc hr
  · intro t
    exact (fderiv_parallelRadialDistanceEquation_radial_pos
      K hKne hKcompact hKconvex hc hr t).ne'

end CrouzeixConjecture
