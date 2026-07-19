module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CrouzeixConjecture

/-- The second-coordinate value of a two-variable Fréchet derivative is identified by the
ordinary derivative of the corresponding one-variable slice. -/
theorem fderiv_apply_inr_one_eq_of_hasDerivAt_slice
    (F : ℝ × ℝ → ℝ) (t s alpha : ℝ)
    (hF : DifferentiableAt ℝ F (t, s))
    (hslice : HasDerivAt (fun y : ℝ ↦ F (t, y)) alpha s) :
    fderiv ℝ F (t, s) (0, 1) = alpha := by
  have hcomp :
      HasFDerivAt (fun y : ℝ ↦ F (t, y))
        ((fderiv ℝ F (t, s)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) s :=
    hF.hasFDerivAt.comp s (hasFDerivAt_prodMk_right t s)
  have hcomp' :
      HasDerivAt (fun y : ℝ ↦ F (t, y))
        (fderiv ℝ F (t, s) (0, 1)) s := by
    exact hcomp.hasDerivAt
  exact hcomp'.unique hslice

/-- A continuous global scalar root of a `C¹` equation is `C¹` when the derivative in the
root variable never vanishes.  This is the exact globalized form of the implicit-function
theorem needed by the radial boundary construction. -/
theorem contDiff_one_of_continuous_implicit_scalar
    (F : ℝ × ℝ → ℝ) (rho : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hrho : Continuous rho)
    (hroot : ∀ t, F (t, rho t) = 0)
    (hpartial : ∀ t, fderiv ℝ F (t, rho t) (0, 1) ≠ 0) :
    ContDiff ℝ 1 rho := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let a : ℝ × ℝ := (t, rho t)
  let F' : ℝ × ℝ →L[ℝ] ℝ := fderiv ℝ F a
  let L : ℝ →L[ℝ] ℝ :=
    F'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hL_apply (x : ℝ) : L x = x * L 1 := by
    calc
      L x = L (x • (1 : ℝ)) := by simp only [smul_eq_mul, mul_one]
      _ = x • L 1 := map_smul L x 1
      _ = x * L 1 := by rfl
  have hL_one : L 1 ≠ 0 := by
    simpa only [L, F', a, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hpartial t
  have hL_bijective : Function.Bijective L := by
    constructor
    · intro x y hxy
      rw [hL_apply x, hL_apply y] at hxy
      exact mul_right_cancel₀ hL_one hxy
    · intro y
      refine ⟨y / L 1, ?_⟩
      rw [hL_apply]
      exact div_mul_cancel₀ y hL_one
  have hImplicit : IsContDiffImplicitAt 1 F F' a := by
    refine
      { hasFDerivAt := ?_
        contDiffAt := hF.contDiffAt
        bijective := ?_
        ne_zero := one_ne_zero }
    · exact (hF.differentiable_one a).hasFDerivAt
    · simpa only [L] using hL_bijective
  have hpair :
      Tendsto (fun x : ℝ ↦ (x, rho x)) (nhds t) (nhds a) := by
    simpa only [a] using tendsto_id.prodMk_nhds hrho.continuousAt
  have hlocalEquation :=
    hpair.eventually hImplicit.eventually_implicitFunction_apply_eq
  have heq : rho =ᶠ[nhds t] hImplicit.implicitFunction := by
    filter_upwards [hlocalEquation] with x hx
    symm
    apply hx
    simp only [a, hroot x, hroot t]
  exact hImplicit.contDiffAt_implicitFunction.congr_of_eventuallyEq heq

end CrouzeixConjecture
