module

public import CrouzeixConjecture.ConvexProjection
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

noncomputable section

open scoped InnerProductSpace Topology

namespace CrouzeixConjecture

/-- The squared Euclidean distance to a nonempty compact real-convex subset of the
complex plane, written using its metric projection. -/
def convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (z : ℂ) : ℝ :=
  ‖z - convexProjection K hKne hKcompact hKconvex z‖ ^ 2

/-- The error after subtracting the first-order term of squared distance is nonnegative
and bounded by the square of the increment. -/
theorem convexSquaredDistance_remainder_bounds
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x y : ℂ) :
    0 ≤ convexSquaredDistance K hKne hKcompact hKconvex y -
        convexSquaredDistance K hKne hKcompact hKconvex x -
          2 * ⟪x - convexProjection K hKne hKcompact hKconvex x, y - x⟫_ℝ ∧
      convexSquaredDistance K hKne hKcompact hKconvex y -
          convexSquaredDistance K hKne hKcompact hKconvex x -
            2 * ⟪x - convexProjection K hKne hKcompact hKconvex x, y - x⟫_ℝ ≤
        ‖y - x‖ ^ 2 := by
  let p := convexProjection K hKne hKcompact hKconvex x
  let q := convexProjection K hKne hKcompact hKconvex y
  change
    0 ≤ ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ∧
      ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ≤
        ‖y - x‖ ^ 2
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
  have hyq_decomp :
      y - q = (x - p) + ((y - x) - (q - p)) := by
    abel
  have hremainder :
      ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ =
        ‖(y - x) - (q - p)‖ ^ 2 - 2 * ⟪x - p, q - p⟫_ℝ := by
    rw [hyq_decomp, norm_add_sq_real]
    simp only [inner_sub_right]
    ring
  have hlower :
      0 ≤ ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ := by
    rw [hremainder]
    nlinarith [sq_nonneg ‖(y - x) - (q - p)‖]
  have hyp_decomp : y - p = (y - q) - (p - q) := by
    abel
  have hcompare : ‖y - q‖ ^ 2 ≤ ‖y - p‖ ^ 2 := by
    calc
      ‖y - q‖ ^ 2 ≤
          ‖y - q‖ ^ 2 - 2 * ⟪y - q, p - q⟫_ℝ + ‖p - q‖ ^ 2 := by
        nlinarith [sq_nonneg ‖p - q‖]
      _ = ‖(y - q) - (p - q)‖ ^ 2 := (norm_sub_sq_real _ _).symm
      _ = ‖y - p‖ ^ 2 := by rw [← hyp_decomp]
  have hypx_decomp : y - p = (x - p) + (y - x) := by
    abel
  have hupper :
      ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ≤
        ‖y - x‖ ^ 2 := by
    calc
      ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ≤
          ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ := by
        linarith
      _ = ‖y - x‖ ^ 2 := by
        rw [hypx_decomp, norm_add_sq_real]
        ring
  exact ⟨hlower, hupper⟩

/-- The squared distance has gradient twice the projection residual. -/
theorem hasFDerivAt_convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x : ℂ) :
    HasFDerivAt (convexSquaredDistance K hKne hKcompact hKconvex)
      ((2 : ℝ) • innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x)) x := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (g := fun y : ℂ ↦ ‖y - x‖)
  · intro y
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · intro y
    have hbounds :=
      convexSquaredDistance_remainder_bounds
        K hKne hKcompact hKconvex x y
    have hbounds' :
        0 ≤ convexSquaredDistance K hKne hKcompact hKconvex y -
              convexSquaredDistance K hKne hKcompact hKconvex x -
                ((2 : ℝ) • innerSL ℝ
                  (x - convexProjection K hKne hKcompact hKconvex x)) (y - x) ∧
          convexSquaredDistance K hKne hKcompact hKconvex y -
              convexSquaredDistance K hKne hKcompact hKconvex x -
                ((2 : ℝ) • innerSL ℝ
                  (x - convexProjection K hKne hKcompact hKconvex x)) (y - x) ≤
            ‖y - x‖ ^ 2 := by
      simpa only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul] using hbounds
    have hnorm :
        ‖convexSquaredDistance K hKne hKcompact hKconvex y -
            convexSquaredDistance K hKne hKcompact hKconvex x -
              ((2 : ℝ) • innerSL ℝ
                (x - convexProjection K hKne hKcompact hKconvex x)) (y - x)‖ ≤
          ‖y - x‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hbounds'.1]
      exact hbounds'.2
    by_cases hyx : ‖y - x‖ = 0
    · have hy : y = x := sub_eq_zero.mp (norm_eq_zero.mp hyx)
      subst y
      simp
    · calc
        ‖y - x‖⁻¹ *
              ‖convexSquaredDistance K hKne hKcompact hKconvex y -
                convexSquaredDistance K hKne hKcompact hKconvex x -
                  ((2 : ℝ) • innerSL ℝ
                    (x - convexProjection K hKne hKcompact hKconvex x)) (y - x)‖ ≤
            ‖y - x‖⁻¹ * ‖y - x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm
            (inv_nonneg.mpr (norm_nonneg _))
        _ = ‖y - x‖ := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hyx, one_mul]
  · exact tendsto_norm_sub_self x

/-- Fully elaborated formula for the Fréchet derivative of squared distance. -/
@[simp]
theorem fderiv_convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x : ℂ) :
    fderiv ℝ (convexSquaredDistance K hKne hKcompact hKconvex) x =
      (2 : ℝ) • innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x) :=
  (hasFDerivAt_convexSquaredDistance K hKne hKcompact hKconvex x).fderiv

/-- The derivative field of squared distance is continuous. -/
theorem continuous_convexSquaredDistanceDerivative
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) :
    Continuous (fun x : ℂ ↦
      (2 : ℝ) • innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x)) := by
  have hresidual : Continuous (fun x : ℂ ↦
      x - convexProjection K hKne hKcompact hKconvex x) :=
    continuous_id.sub
      (continuous_convexProjection K hKne hKcompact hKconvex)
  have hinner : Continuous (fun x : ℂ ↦
      innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x)) :=
    (innerSL ℝ).continuous.comp hresidual
  exact hinner.const_smul (2 : ℝ)

/-- The squared distance to a compact convex set is continuously Fréchet differentiable. -/
theorem contDiff_one_convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) :
    ContDiff ℝ 1 (convexSquaredDistance K hKne hKcompact hKconvex) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨fun x ↦
      (2 : ℝ) • innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x),
    continuous_convexSquaredDistanceDerivative K hKne hKcompact hKconvex,
    hasFDerivAt_convexSquaredDistance K hKne hKcompact hKconvex⟩

/-- The actual `fderiv` field is continuous. -/
theorem continuous_fderiv_convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) :
    Continuous (fderiv ℝ
      (convexSquaredDistance K hKne hKcompact hKconvex)) := by
  have heq :
      fderiv ℝ (convexSquaredDistance K hKne hKcompact hKconvex) =
        fun x : ℂ ↦ (2 : ℝ) • innerSL ℝ
          (x - convexProjection K hKne hKcompact hKconvex x) := by
    funext x
    exact fderiv_convexSquaredDistance K hKne hKcompact hKconvex x
  rw [heq]
  exact continuous_convexSquaredDistanceDerivative K hKne hKcompact hKconvex

/-- Since it is `C¹`, squared distance has the displayed strict Fréchet derivative. -/
theorem hasStrictFDerivAt_convexSquaredDistance
    (K : Set ℂ) (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hKconvex : Convex ℝ K) (x : ℂ) :
    HasStrictFDerivAt (convexSquaredDistance K hKne hKcompact hKconvex)
      ((2 : ℝ) • innerSL ℝ
        (x - convexProjection K hKne hKcompact hKconvex x)) x :=
  (contDiff_one_convexSquaredDistance K hKne hKcompact hKconvex).contDiffAt.hasStrictFDerivAt'
    (hasFDerivAt_convexSquaredDistance K hKne hKcompact hKconvex x) one_ne_zero

end CrouzeixConjecture
