module

public import CrouzeixConjecture.QNumericalRange
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- The real scalar equation used to choose the disk automorphism in the
similarity-orbit extraction argument. -/
def extractionEquation (t c a : ℝ) : ℝ :=
  t * c * (1 + a ^ 2) - a * (1 + t ^ 2)

/-- For a norm level `t > 1` and an acute singular-vector angle `c`, the
manuscript's orthogonalizing disk-automorphism parameter exists in `[0,1)`. -/
theorem exists_extractionParameter {t c : ℝ}
    (ht : 1 < t) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ extractionEquation t c a = 0 := by
  by_cases hc : c = 0
  · exact ⟨0, le_rfl, zero_lt_one, by simp [extractionEquation, hc]⟩
  · have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    let F : ℝ → ℝ := fun a ↦ extractionEquation t c a
    have hFcont : Continuous F := by
      dsimp [F, extractionEquation]
      fun_prop
    have hF0 : 0 < F 0 := by
      have ht0 : 0 < t := zero_lt_one.trans ht
      simpa [F, extractionEquation] using mul_pos ht0 hcpos
    have hF1 : F 1 < 0 := by
      simp only [F, extractionEquation, one_pow, one_mul]
      nlinarith
    have hzero : (0 : ℝ) ∈ Set.Icc (F 1) (F 0) := ⟨hF1.le, hF0.le⟩
    obtain ⟨a, ha, hFa⟩ :=
      intermediate_value_Icc' (a := (0 : ℝ)) (b := 1)
        zero_le_one hFcont.continuousOn hzero
    refine ⟨a, ha.1, ?_, hFa⟩
    exact lt_of_le_of_ne ha.2 fun haeq ↦ by
      rw [haeq] at hFa
      linarith

/-- The scalar amplification identity behind the extraction lemma. -/
theorem extraction_amplification_identity {t c a : ℝ}
    (heq : extractionEquation t c a = 0) :
    (t ^ 2 + a ^ 2 - 2 * a * t * c) -
        t ^ 2 * (1 + a ^ 2 * t ^ 2 - 2 * a * t * c) =
      a * t * c * (t ^ 2 - 1) * (1 - a ^ 2) := by
  rw [extractionEquation] at heq
  linear_combination a * (t ^ 2 - 1) * heq

/-- The orthogonality identity produced by the same scalar equation. -/
theorem extraction_orthogonality_identity {t c a : ℝ}
    (heq : extractionEquation t c a = 0) :
    t * c * (1 + a ^ 2) - a * (1 + t ^ 2) = 0 := by
  exact heq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Norm expansion for `x - at y` when `x,y` are unit vectors and their inner
product is the real number `c`. -/
theorem norm_sub_real_smul_unit_sq {x y : E} {a t c : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hyx : ⟪y, x⟫_ℂ = (c : ℂ)) :
    ‖x - (a * t : ℂ) • y‖ ^ 2 = 1 + a ^ 2 * t ^ 2 - 2 * a * t * c := by
  have hxy : ⟪x, y⟫_ℂ = (c : ℂ) := by
    rw [← inner_conj_symm, hyx]
    simp
  rw [@norm_sub_sq ℂ, hx, norm_smul, hy, mul_one, inner_smul_right, hxy]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs, sq_abs]
  have hre : RCLike.re ((a : ℂ) * (t : ℂ) * (c : ℂ)) = a * t * c := by
    norm_num [Complex.mul_re]
  rw [hre]
  ring

/-- Norm expansion for `t y - a x` under the same hypotheses. -/
theorem norm_real_smul_sub_unit_sq {x y : E} {a t c : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hyx : ⟪y, x⟫_ℂ = (c : ℂ)) :
    ‖(t : ℂ) • y - (a : ℂ) • x‖ ^ 2 = t ^ 2 + a ^ 2 - 2 * a * t * c := by
  rw [@norm_sub_sq ℂ, norm_smul, hy, mul_one, norm_smul, hx, mul_one,
    inner_smul_left, inner_smul_right, hyx]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs, sq_abs]
  have hstar : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [hstar]
  have hre : RCLike.re ((t : ℂ) * ((a : ℂ) * (c : ℂ))) = t * a * c := by
    norm_num [Complex.mul_re]
    ring
  rw [hre]
  ring

/-- The selected Möbius numerator and denominator vectors are orthogonal. -/
theorem extraction_vectors_inner_eq_zero {x y : E} {a t c : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hyx : ⟪y, x⟫_ℂ = (c : ℂ))
    (heq : extractionEquation t c a = 0) :
    ⟪x - (a * t : ℂ) • y, (t : ℂ) • y - (a : ℂ) • x⟫_ℂ = 0 := by
  have hxy : ⟪x, y⟫_ℂ = (c : ℂ) := by
    rw [← inner_conj_symm, hyx]
    simp
  have hfirst :
      ⟪x, (t : ℂ) • y - (a : ℂ) • x⟫_ℂ =
        (t : ℂ) * (c : ℂ) - (a : ℂ) := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hxy,
      inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hsecond :
      ⟪(a * t : ℂ) • y, (t : ℂ) • y - (a : ℂ) • x⟫_ℂ =
        (a * t : ℂ) * ((t : ℂ) - (a : ℂ) * (c : ℂ)) := by
    rw [inner_smul_left, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hy, hyx]
    have hstar : (starRingEnd ℂ) (a * t : ℂ) = (a * t : ℂ) := by simp
    rw [hstar]
    norm_num
  calc
    ⟪x - (a * t : ℂ) • y, (t : ℂ) • y - (a : ℂ) • x⟫_ℂ =
        (t : ℂ) * (c : ℂ) - (a : ℂ) -
          (a * t : ℂ) * ((t : ℂ) - (a : ℂ) * (c : ℂ)) := by
      rw [inner_sub_left, hfirst, hsecond]
    _ = (extractionEquation t c a : ℂ) := by
      have hreal :
          t * c - a - a * t * (t - a * c) = extractionEquation t c a := by
        rw [extractionEquation]
        ring
      exact_mod_cast hreal
    _ = 0 := by rw [heq]; norm_num

/-- Algebraic core of similarity-orbit extraction: after the adapted disk
automorphism, the output/input norm ratio is at least the original norm level. -/
theorem extraction_vectors_amplify {x y : E} {a t c : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hyx : ⟪y, x⟫_ℂ = (c : ℂ))
    (ht : 1 ≤ t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hc0 : 0 ≤ c)
    (heq : extractionEquation t c a = 0) :
    t * ‖x - (a * t : ℂ) • y‖ ≤ ‖(t : ℂ) • y - (a : ℂ) • x‖ := by
  have hu := norm_sub_real_smul_unit_sq hx hy hyx (a := a) (t := t)
  have hw := norm_real_smul_sub_unit_sq hx hy hyx (a := a) (t := t)
  have hid := extraction_amplification_identity heq
  have htSq : 0 ≤ t ^ 2 - 1 := by nlinarith
  have haSq : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hnonneg : 0 ≤ a * t * c * (t ^ 2 - 1) * (1 - a ^ 2) := by
    positivity
  have hsq : t ^ 2 * ‖x - (a * t : ℂ) • y‖ ^ 2 ≤
      ‖(t : ℂ) • y - (a : ℂ) • x‖ ^ 2 := by
    rw [hu, hw]
    linarith
  nlinarith [norm_nonneg (x - (a * t : ℂ) • y),
    norm_nonneg ((t : ℂ) • y - (a : ℂ) • x)]

end CrouzeixConjecture
