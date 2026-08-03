module

public import CrouzeixConjecture.CompletionAlgebra
public import CrouzeixConjecture.HerglotzKernel
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite-sampling inequality can be indexed by an arbitrary finite type, not only by
`Fin m`.  This is the form needed for the manuscript's distinguished point `0` together with
one point for every eigenvalue. -/
theorem finite_type_sampling_quadratic_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : Set ℂ} {L : ℂ → ℂ → SquareMatrix n} (hL : IsPositiveMatrixKernelOn s L)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ s) (ξ : ι → n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := finite_sampling_quadratic_nonneg hL (z ∘ e) (fun i ↦ hz (e i)) (ξ ∘ e)
  simp only [Function.comp_apply] at h
  conv at h =>
    rhs
    enter [2, i]
    rw [e.sum_comp (fun j ↦ star (ξ (e i)) ⬝ᵥ (L (z (e i)) (z j) *ᵥ ξ j))]
  rw [e.sum_comp
    (fun i ↦ ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j))] at h
  exact h

/-- The matrix multiplying `u` after substituting `v = -G⁻¹Pu` into the sampled
Herglotz-kernel quadratic form in `eq:pre-gramian-inequality`. -/
def completionSampleCoefficient (G P R : SquareMatrix n) : SquareMatrix n :=
  4 * R - 2 * P - (G + R) * G⁻¹ * P - P * G⁻¹ * (G + R) +
    2 * (P * G⁻¹ * P)

/-- The sampled coefficient is exactly the anticommutator expression in `X = R - P` from
`eq:Y-inequality`. -/
theorem completionSampleCoefficient_eq (G P R : SquareMatrix n) (hG : IsUnit G) :
    completionSampleCoefficient G P R =
      4 * (R - P) - (R - P) * G⁻¹ * P - P * G⁻¹ * (R - P) := by
  exact completion_substitution_matrix_identity G P R hG

/-- Hermiticity of the sampled coefficient.  The two mixed terms are adjoints of one another,
as in `eq:pre-gramian-inequality`. -/
theorem completionSampleCoefficient_isHermitian {G P R : SquareMatrix n}
    (hG : G.IsHermitian) (hP : P.IsHermitian) (hR : R.IsHermitian) :
    (completionSampleCoefficient G P R).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp only [completionSampleCoefficient, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_ofNat,
    Matrix.conjTranspose_nonsing_inv, hG.eq, hP.eq, hR.eq]
  noncomm_ring

/-- Once kernel positivity supplies the displayed quadratic inequality for every `u`, it is
precisely positive semidefiniteness of the sampled coefficient. -/
theorem completionSampleCoefficient_posSemidef_of_quadratic_nonneg
    {G P R : SquareMatrix n} (hG : G.IsHermitian) (hP : P.IsHermitian)
    (hR : R.IsHermitian)
    (hquad : ∀ u : n → ℂ,
      0 ≤ star u ⬝ᵥ (completionSampleCoefficient G P R *ᵥ u)) :
    (completionSampleCoefficient G P R).PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (completionSampleCoefficient_isHermitian hG hP hR) hquad

/-- Exact matrix form of `eq:Y-inequality`, after applying the preceding sampling calculation
to the three matrices `P`, `R`, and `X`. -/
theorem completion_X_inequality_of_sampling
    {G : SquareMatrix n} {lambda : n → ℂ} (hGherm : G.IsHermitian) (hG : IsUnit G)
    (hquad : ∀ u : n → ℂ,
      0 ≤ star u ⬝ᵥ
        (completionSampleCoefficient G (completionP G lambda) (completionR G lambda) *ᵥ u)) :
    (4 * completionX G lambda - completionX G lambda * G⁻¹ * completionP G lambda -
      completionP G lambda * G⁻¹ * completionX G lambda).PosSemidef := by
  have hsample :
      (completionSampleCoefficient G (completionP G lambda) (completionR G lambda)).PosSemidef :=
    completionSampleCoefficient_posSemidef_of_quadratic_nonneg hGherm
      (completionP_isHermitian hGherm lambda) (completionR_isHermitian hGherm lambda) hquad
  rw [completionSampleCoefficient_eq G (completionP G lambda) (completionR G lambda) hG] at hsample
  simpa only [completionX] using hsample

end CrouzeixConjecture
