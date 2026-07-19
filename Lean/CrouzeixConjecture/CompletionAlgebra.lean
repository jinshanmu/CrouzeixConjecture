module

public import CrouzeixConjecture.Definitions
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix

namespace CrouzeixConjecture

variable {n : Type*}

/-- The matrix `P` from manuscript line 105. -/
def completionP (G : SquareMatrix n) (lambda : n → ℂ) : SquareMatrix n :=
  fun i j ↦ G i j / (1 - conj (lambda i) * lambda j / 4)

/-- The matrix `R` from manuscript line 106. -/
def completionR (G : SquareMatrix n) (lambda : n → ℂ) : SquareMatrix n :=
  fun i j ↦ G i j / (1 - conj (lambda i) * lambda j / 2)

/-- The matrix `X = R - P` from manuscript line 107. -/
def completionX (G : SquareMatrix n) (lambda : n → ℂ) : SquareMatrix n :=
  completionR G lambda - completionP G lambda

private theorem completion_product_norm_le_one (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    ‖conj (lambda i) * lambda j‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  calc
    ‖lambda i‖ * ‖lambda j‖ ≤ 1 * 1 :=
      mul_le_mul (hlambda i) (hlambda j) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The denominator defining `P` is nonzero for eigenvalues in the closed unit disk. -/
theorem completionP_denominator_ne_zero (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    1 - conj (lambda i) * lambda j / 4 ≠ 0 := by
  intro hzero
  have hdiv : conj (lambda i) * lambda j / 4 = 1 := (sub_eq_zero.mp hzero).symm
  have hproduct : conj (lambda i) * lambda j = 4 := by
    simpa using (div_eq_iff (by norm_num : (4 : ℂ) ≠ 0)).mp hdiv
  have hnorm := completion_product_norm_le_one lambda hlambda i j
  rw [hproduct] at hnorm
  norm_num at hnorm

/-- The denominator defining `R` is nonzero for eigenvalues in the closed unit disk. -/
theorem completionR_denominator_ne_zero (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    1 - conj (lambda i) * lambda j / 2 ≠ 0 := by
  intro hzero
  have hdiv : conj (lambda i) * lambda j / 2 = 1 := (sub_eq_zero.mp hzero).symm
  have hproduct : conj (lambda i) * lambda j = 2 := by
    simpa using (div_eq_iff (by norm_num : (2 : ℂ) ≠ 0)).mp hdiv
  have hnorm := completion_product_norm_le_one lambda hlambda i j
  rw [hproduct] at hnorm
  norm_num at hnorm

/-- Conjugate transpose commutes with the `P` construction. -/
theorem completionP_conjTranspose (G : SquareMatrix n) (lambda : n → ℂ) :
    (completionP G lambda)ᴴ = completionP Gᴴ lambda := by
  ext i j
  simp [completionP, Matrix.conjTranspose_apply, mul_comm]

/-- Conjugate transpose commutes with the `R` construction. -/
theorem completionR_conjTranspose (G : SquareMatrix n) (lambda : n → ℂ) :
    (completionR G lambda)ᴴ = completionR Gᴴ lambda := by
  ext i j
  simp [completionR, Matrix.conjTranspose_apply, mul_comm]

/-- Conjugate transpose commutes with the `X = R - P` construction. -/
theorem completionX_conjTranspose (G : SquareMatrix n) (lambda : n → ℂ) :
    (completionX G lambda)ᴴ = completionX Gᴴ lambda := by
  simp [completionX, completionP_conjTranspose, completionR_conjTranspose]

/-- If `G` is Hermitian, then the manuscript's matrix `P` is Hermitian. -/
theorem completionP_isHermitian {G : SquareMatrix n} (hG : G.IsHermitian)
    (lambda : n → ℂ) : (completionP G lambda).IsHermitian := by
  rw [Matrix.IsHermitian, completionP_conjTranspose, hG]

/-- If `G` is Hermitian, then the manuscript's matrix `R` is Hermitian. -/
theorem completionR_isHermitian {G : SquareMatrix n} (hG : G.IsHermitian)
    (lambda : n → ℂ) : (completionR G lambda).IsHermitian := by
  rw [Matrix.IsHermitian, completionR_conjTranspose, hG]

/-- If `G` is Hermitian, then the manuscript's matrix `X = R - P` is Hermitian. -/
theorem completionX_isHermitian {G : SquareMatrix n} (hG : G.IsHermitian)
    (lambda : n → ℂ) : (completionX G lambda).IsHermitian := by
  rw [Matrix.IsHermitian, completionX_conjTranspose, hG]

/-- The scalar identity behind manuscript line 145. -/
theorem completion_resolvent_scalar_identity (g a : ℂ)
    (h₂ : 1 - a / 2 ≠ 0) (h₄ : 1 - a / 4 ≠ 0) :
    2 * g / ((1 - a / 2) * (1 - a / 4)) =
      4 * (g / (1 - a / 2)) - 2 * (g / (1 - a / 4)) := by
  conv_rhs =>
    rw [← mul_div_assoc, ← mul_div_assoc, div_sub_div (4 * g) (2 * g) h₂ h₄]
  congr 1
  ring

/-- Entrywise form of the manuscript identity saying that the sampled resolvent contribution is
`4 R - 2 P`. -/
theorem completion_fourR_sub_twoP_apply (G : SquareMatrix n) (lambda : n → ℂ)
    (hlambda : ∀ i, ‖lambda i‖ ≤ 1) (i j : n) :
    (((4 : ℂ) • completionR G lambda - (2 : ℂ) • completionP G lambda) i j) =
      2 * G i j /
        ((1 - conj (lambda i) * lambda j / 2) *
          (1 - conj (lambda i) * lambda j / 4)) := by
  have h₂ := completionR_denominator_ne_zero lambda hlambda i j
  have h₄ := completionP_denominator_ne_zero lambda hlambda i j
  simpa [completionP, completionR] using
    (completion_resolvent_scalar_identity (G i j) (conj (lambda i) * lambda j) h₂ h₄).symm

/-- The noncommutative ring identity used after substituting `v = -G⁻¹ P u` into the sampled
kernel quadratic form.  The two hypotheses abstract the two inverse identities for `G`. -/
theorem completion_substitution_ring_identity {R₀ : Type*} [Ring R₀]
    (G Ginv P R : R₀) (hGinvG : Ginv * G = 1) (hGGinv : G * Ginv = 1) :
    4 * R - 2 * P - (G + R) * Ginv * P - P * Ginv * (G + R) +
        2 * (P * Ginv * P) =
      4 * (R - P) - (R - P) * Ginv * P - P * Ginv * (R - P) := by
  noncomm_ring [hGinvG, hGGinv]

/-- Matrix specialization of `completion_substitution_ring_identity`, with the manuscript's
`G⁻¹` as the inverse. -/
theorem completion_substitution_matrix_identity [Fintype n] [DecidableEq n]
    (G P R : SquareMatrix n) (hG : IsUnit G) :
    4 * R - 2 * P - (G + R) * G⁻¹ * P - P * G⁻¹ * (G + R) +
        2 * (P * G⁻¹ * P) =
      4 * (R - P) - (R - P) * G⁻¹ * P - P * G⁻¹ * (R - P) := by
  have hdet : IsUnit G.det := G.isUnit_iff_isUnit_det.mp hG
  exact completion_substitution_ring_identity G G⁻¹ P R
    (G.nonsing_inv_mul hdet) (G.mul_nonsing_inv hdet)

/-- The vector `v = -G⁻¹ P u` used in manuscript line 121. -/
def completionV [Fintype n] [DecidableEq n]
    (G P : SquareMatrix n) (u : n → ℂ) : n → ℂ :=
  -(G⁻¹ *ᵥ (P *ᵥ u))

/-- The defining cancellation equation `Gv + Pu = 0` for `v = -G⁻¹ P u`. -/
theorem completion_mulVec_add_eq_zero [Fintype n] [DecidableEq n]
    (G P : SquareMatrix n) (u : n → ℂ) (hG : IsUnit G) :
    G *ᵥ completionV G P u + P *ᵥ u = 0 := by
  have hdet : IsUnit G.det := G.isUnit_iff_isUnit_det.mp hG
  rw [completionV, Matrix.mulVec_neg, Matrix.mulVec_mulVec, G.mul_nonsing_inv hdet,
    Matrix.one_mulVec, neg_add_cancel]

/-- The exact `P`, `R`, `X` specialization of the noncommutative substitution in manuscript
line 154. -/
theorem completion_PRX_substitution_identity [Fintype n] [DecidableEq n]
    (G : SquareMatrix n) (lambda : n → ℂ) (hG : IsUnit G) :
    4 * completionR G lambda - 2 * completionP G lambda -
          (G + completionR G lambda) * G⁻¹ * completionP G lambda -
        completionP G lambda * G⁻¹ * (G + completionR G lambda) +
          2 * (completionP G lambda * G⁻¹ * completionP G lambda) =
      4 * completionX G lambda -
          completionX G lambda * G⁻¹ * completionP G lambda -
        completionP G lambda * G⁻¹ * completionX G lambda := by
  simpa only [completionX] using
    completion_substitution_matrix_identity G (completionP G lambda) (completionR G lambda) hG

end CrouzeixConjecture
