module

public import CrouzeixConjecture.CompletionSeries
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.NoncommRing

@[expose] public section

noncomputable section

open scoped ComplexOrder Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Evaluation of the anticommutator in manuscript line 203 on an eigenvector of `P`. -/
theorem anticommutator_quadratic_on_eigenvector
    (P X : SquareMatrix n) (hP : P.IsHermitian) (e : n → ℂ) (p : ℝ)
    (hPe : P *ᵥ e = (p : ℂ) • e) :
    star e ⬝ᵥ (((4 : ℂ) • X - X * P - P * X) *ᵥ e) =
      ((4 : ℂ) - 2 * (p : ℂ)) * (star e ⬝ᵥ (X *ᵥ e)) := by
  have hrow : star e ᵥ* P = star (P *ᵥ e) := by
    calc
      star e ᵥ* P = star e ᵥ* Pᴴ := by rw [hP.eq]
      _ = star (P *ᵥ e) := (Matrix.star_mulVec P e).symm
  have hleft : star e ⬝ᵥ (P *ᵥ (X *ᵥ e)) =
      (p : ℂ) * (star e ⬝ᵥ (X *ᵥ e)) := by
    rw [Matrix.dotProduct_mulVec, hrow, hPe]
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  have hright : star e ⬝ᵥ (X *ᵥ (P *ᵥ e)) =
      (p : ℂ) * (star e ⬝ᵥ (X *ᵥ e)) := by
    rw [hPe]
    rw [Matrix.mulVec_smul, dotProduct_smul]
    rfl
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hleft, hright]
  ring

/-- Under the Gramian anticommutator inequality, every eigenvalue of the `q = 4` Gramian is at
most `2`.  This is the eigenvector contradiction in manuscript lines 200--208. -/
theorem gramian_four_eigenvalues_le_two [Nonempty n] {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M)
    (hineq : ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
      (gramian 2 C - gramian 4 C) * gramian 4 C -
      gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef) :
    ∀ i, (gramian_posSemidef (q := 4) (by norm_num) hM C hbound).isHermitian.eigenvalues i ≤ 2 := by
  let P := gramian 4 C
  let X := gramian 2 C - gramian 4 C
  have hPpos : P.PosSemidef := gramian_posSemidef (q := 4) (by norm_num) hM C hbound
  have hXpos : X.PosSemidef := gramian_two_sub_gramian_four_posSemidef hM C hbound
  have hXrest : (X - (4 : ℝ)⁻¹ • (Cᴴ * C)).PosSemidef :=
    gramian_two_sub_gramian_four_sub_first_posSemidef hM C hbound
  let hPh : P.IsHermitian := hPpos.isHermitian
  change ∀ i, hPh.eigenvalues i ≤ 2
  intro i
  let e : n → ℂ := ⇑(hPh.eigenvectorBasis i)
  let p : ℝ := hPh.eigenvalues i
  have hPe : P *ᵥ e = (p : ℂ) • e := by
    simpa only [e, p, RCLike.real_smul_eq_coe_smul] using hPh.mulVec_eigenvectorBasis i
  by_contra hp
  have hpgt : 2 < p := lt_of_not_ge hp
  have hqnonneg : 0 ≤ star e ⬝ᵥ (X *ᵥ e) := hXpos.dotProduct_mulVec_nonneg e
  have hi := hineq.dotProduct_mulVec_nonneg e
  change 0 ≤ star e ⬝ᵥ (((4 : ℂ) • X - X * P - P * X) *ᵥ e) at hi
  rw [anticommutator_quadratic_on_eigenvector P X hPh e p hPe] at hi
  have hqre : (star e ⬝ᵥ (X *ᵥ e)).re = 0 := by
    have hqparts := Complex.nonneg_iff.mp hqnonneg
    have hiparts := Complex.nonneg_iff.mp hi
    have hprod : 0 ≤ (4 - 2 * p) * (star e ⬝ᵥ (X *ᵥ e)).re := by
      simpa [Complex.mul_re] using hiparts.1
    nlinarith
  have hqzero : star e ⬝ᵥ (X *ᵥ e) = 0 := by
    apply Complex.ext
    · simpa using hqre
    · simpa using (Complex.nonneg_iff.mp hqnonneg).2.symm
  have hXe : X *ᵥ e = 0 := (hXpos.dotProduct_mulVec_zero_iff e).mp hqzero
  let Y : SquareMatrix n := (4 : ℝ)⁻¹ • (Cᴴ * C)
  have hYpos : Y.PosSemidef := by
    exact (Matrix.posSemidef_conjTranspose_mul_self C).smul (by norm_num)
  have hremq : 0 ≤ star e ⬝ᵥ ((X - Y) *ᵥ e) := hXrest.dotProduct_mulVec_nonneg e
  have hYq : 0 ≤ star e ⬝ᵥ (Y *ᵥ e) := hYpos.dotProduct_mulVec_nonneg e
  have hsumzero :
      star e ⬝ᵥ ((X - Y) *ᵥ e) + star e ⬝ᵥ (Y *ᵥ e) = 0 := by
    rw [← hqzero]
    simp [Matrix.sub_mulVec]
  have hYqzero : star e ⬝ᵥ (Y *ᵥ e) = 0 := by
    apply le_antisymm
    · rw [← hsumzero]
      exact le_add_of_nonneg_left hremq
    · exact hYq
  have hCCqzero : star e ⬝ᵥ ((Cᴴ * C) *ᵥ e) = 0 := by
    have hscale : (((4 : ℝ)⁻¹ : ℝ) : ℂ) *
        (star e ⬝ᵥ ((Cᴴ * C) *ᵥ e)) = 0 := by
      change star e ⬝ᵥ (((4 : ℝ)⁻¹ • (Cᴴ * C)) *ᵥ e) = 0 at hYqzero
      rw [Matrix.smul_mulVec, dotProduct_smul] at hYqzero
      change (((4 : ℝ)⁻¹ : ℝ) : ℂ) *
        (star e ⬝ᵥ ((Cᴴ * C) *ᵥ e)) = 0 at hYqzero
      exact hYqzero
    exact (mul_eq_zero.mp hscale).resolve_left (by norm_num)
  have hCe : C *ᵥ e = 0 := by
    apply dotProduct_star_self_eq_zero.mp
    calc
      star (C *ᵥ e) ⬝ᵥ (C *ᵥ e) = star e ⬝ᵥ ((Cᴴ * C) *ᵥ e) := by
        simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_conjTranspose, star_star]
      _ = 0 := hCCqzero
  have hstein : P = 1 + (4 : ℝ)⁻¹ • (Cᴴ * P * C) := by
    simpa [P] using gramian_stein_identity (q := 4) (by norm_num) hM C hbound
  have htriple : (Cᴴ * P * C) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hCe, Matrix.mulVec_zero]
  have hPeOne : P *ᵥ e = e := by
    rw [hstein, Matrix.add_mulVec, Matrix.smul_mulVec, htriple]
    simp
  have heLp : hPh.eigenvectorBasis i ≠ 0 := hPh.eigenvectorBasis.orthonormal.ne_zero i
  have he : e ≠ 0 := by
    intro hezero
    apply heLp
    apply PiLp.ext fun j ↦ by
      simpa [e] using congrFun hezero j
  have hpcomplex : (p : ℂ) = 1 := by
    apply smul_left_injective ℂ he
    simpa only [one_smul] using hPe.symm.trans hPeOne
  have hpone : p = 1 := Complex.ofReal_injective hpcomplex
  nlinarith

/-- The eigenvalue bound is equivalent to the Loewner upper bound `P ≤ 2 I` in manuscript
equation (11). -/
theorem gramian_four_upper_bound_posSemidef [Nonempty n] {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M)
    (hineq : ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
      (gramian 2 C - gramian 4 C) * gramian 4 C -
      gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef) :
    ((2 : ℂ) • (1 : SquareMatrix n) - gramian 4 C).PosSemidef := by
  let P := gramian 4 C
  have hPpos : P.PosSemidef := gramian_posSemidef (q := 4) (by norm_num) hM C hbound
  let hPh : P.IsHermitian := hPpos.isHermitian
  have hp : ∀ i, hPh.eigenvalues i ≤ 2 := by
    simpa [P, hPh] using gramian_four_eigenvalues_le_two hM C hbound hineq
  let U := hPh.eigenvectorUnitary
  let D : SquareMatrix n := Matrix.diagonal (fun i ↦ ((2 - hPh.eigenvalues i : ℝ) : ℂ))
  have hD : D.PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    change (0 : ℂ) ≤ ((2 - hPh.eigenvalues i : ℝ) : ℂ)
    exact_mod_cast sub_nonneg.mpr (hp i)
  have hcong : (((U : SquareMatrix n) * D * (U : SquareMatrix n)ᴴ)).PosSemidef :=
    hD.mul_mul_conjTranspose_same (U : SquareMatrix n)
  have hspec : P = (U : SquareMatrix n) *
      Matrix.diagonal (fun i ↦ (hPh.eigenvalues i : ℂ)) * (U : SquareMatrix n)ᴴ := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hPh.spectral_theorem
  have hdiag : D = (2 : ℂ) • (1 : SquareMatrix n) -
      Matrix.diagonal (fun i ↦ (hPh.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hU : (U : SquareMatrix n) * (U : SquareMatrix n)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self U
  change ((2 : ℂ) • (1 : SquareMatrix n) - P).PosSemidef
  rw [hspec]
  convert hcong using 1
  rw [hdiag, Matrix.mul_sub, Matrix.sub_mul]
  simp [mul_assoc, hU]

/-- The Gramian anticommutator inequality implies the final Stein bound `4 I - Cᴴ C ⪰ 0`. -/
theorem four_sub_conjTranspose_mul_self_posSemidef_of_gramian_inequality
    [Nonempty n] {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M)
    (hineq : ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
      (gramian 2 C - gramian 4 C) * gramian 4 C -
      gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef) :
    ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * C).PosSemidef := by
  let P := gramian 4 C
  have hPpos : P.PosSemidef := gramian_posSemidef (q := 4) (by norm_num) hM C hbound
  have hPupper : ((2 : ℂ) • (1 : SquareMatrix n) - P).PosSemidef := by
    simpa [P] using gramian_four_upper_bound_posSemidef hM C hbound hineq
  have hstein : P = 1 + (4 : ℝ)⁻¹ • (Cᴴ * P * C) := by
    simpa [P] using gramian_stein_identity (q := 4) (by norm_num) hM C hbound
  have hPminusEq : P - 1 = (4 : ℝ)⁻¹ • (Cᴴ * P * C) := by
    calc
      P - 1 = (1 + (4 : ℝ)⁻¹ • (Cᴴ * P * C)) - 1 :=
        congrArg (· - 1) hstein
      _ = (4 : ℝ)⁻¹ • (Cᴴ * P * C) := by simp
  have hPminus : (P - 1).PosSemidef := by
    rw [hPminusEq]
    exact (hPpos.conjTranspose_mul_mul_same C).smul (by norm_num)
  have hCPdiff : (Cᴴ * P * C - Cᴴ * C).PosSemidef := by
    have h := hPminus.conjTranspose_mul_mul_same C
    have hid : Cᴴ * (P - 1) * C = Cᴴ * P * C - Cᴴ * C := by
      noncomm_ring
    rwa [hid] at h
  have hCPC : Cᴴ * P * C = (4 : ℝ) • (P - 1) := by
    calc
      Cᴴ * P * C = (1 : ℝ) • (Cᴴ * P * C) := (one_smul ℝ _).symm
      _ = ((4 : ℝ) * (4 : ℝ)⁻¹) • (Cᴴ * P * C) := by norm_num
      _ = (4 : ℝ) • ((4 : ℝ)⁻¹ • (Cᴴ * P * C)) :=
        (smul_smul (4 : ℝ) (4 : ℝ)⁻¹ (Cᴴ * P * C)).symm
      _ = (4 : ℝ) • (P - 1) := congrArg ((4 : ℝ) • ·) hPminusEq.symm
  have hscaled : ((4 : ℝ) • ((2 : ℂ) • (1 : SquareMatrix n) - P)).PosSemidef :=
    hPupper.smul (by norm_num)
  have h4CP : ((4 : ℂ) • (1 : SquareMatrix n) - Cᴴ * P * C).PosSemidef := by
    rw [hCPC]
    have heq : (4 : ℝ) • ((2 : ℂ) • (1 : SquareMatrix n) - P) =
        (4 : ℂ) • (1 : SquareMatrix n) - (4 : ℝ) • (P - 1) := by
      ext i j
      by_cases hij : i = j
      · simp [hij]
        ring
      · simp [hij]
    rw [← heq]
    exact hscaled
  have hfinal := hCPdiff.add h4CP
  convert hfinal using 1
  simp only [Algebra.smul_def, mul_one]
  noncomm_ring

/-- Completion of manuscript lines 200--221: the anticommutator inequality for the two Gramians
forces the Euclidean operator norm of `C` to be at most `2`. -/
theorem norm_le_two_of_gramian_inequality [Nonempty n] {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M)
    (hineq : ((4 : ℂ) • (gramian 2 C - gramian 4 C) -
      (gramian 2 C - gramian 4 C) * gramian 4 C -
      gramian 4 C * (gramian 2 C - gramian 4 C)).PosSemidef) :
    ‖C‖ ≤ 2 :=
  matrix_norm_le_two_of_four_sub_conjTranspose_mul_self_posSemidef C
    (four_sub_conjTranspose_mul_self_posSemidef_of_gramian_inequality hM C hbound hineq)

end CrouzeixConjecture
