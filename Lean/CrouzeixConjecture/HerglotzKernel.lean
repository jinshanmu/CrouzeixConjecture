module

public import CrouzeixConjecture.Definitions
public import Mathlib.Analysis.Complex.Order

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace CrouzeixConjecture

/-- The open unit disk used in the manuscript. -/
def openUnitDisk : Set ℂ := Metric.ball 0 1

/-- The unit circle supporting a Herglotz representing measure. -/
def unitCircle : Set ℂ := Metric.sphere 0 1

/-- The scalar Herglotz summand attached to a point of the unit circle. -/
def scalarHerglotzSummand (ζ z : ℂ) : ℂ := (ζ + z) / (ζ - z)

/-- The scalar kernel obtained from one Herglotz summand. -/
def scalarHerglotzKernel (ζ z w : ℂ) : ℂ :=
  (scalarHerglotzSummand ζ z + starRingEnd ℂ (scalarHerglotzSummand ζ w)) /
    (1 - z * starRingEnd ℂ w)

/-- The feature whose rank-one kernel is a scalar Herglotz kernel. -/
def circleFeature (ζ z : ℂ) : ℂ := (1 - z * starRingEnd ℂ ζ)⁻¹

/-- The block matrix obtained by sampling a matrix-valued kernel at finitely many points. -/
def sampledKernelMatrix {n : Type*} {m : ℕ}
    (L : ℂ → ℂ → SquareMatrix n) (z : Fin m → ℂ) :
    Matrix (Fin m × n) (Fin m × n) ℂ :=
  fun i j ↦ L (z i.1) (z j.1) i.2 j.2

/-- Positivity of all finite sampling matrices, equivalent to the quadratic-form formulation
in manuscript lines 51--58. -/
def IsPositiveMatrixKernel {n : Type*} (L : ℂ → ℂ → SquareMatrix n) : Prop :=
  ∀ (m : ℕ) (z : Fin m → ℂ), (sampledKernelMatrix L z).PosSemidef

/-- Positivity of every finite sampling whose points lie in a prescribed set. -/
def IsPositiveMatrixKernelOn {n : Type*} (s : Set ℂ)
    (L : ℂ → ℂ → SquareMatrix n) : Prop :=
  ∀ (m : ℕ) (z : Fin m → ℂ),
    (∀ i, z i ∈ s) → (sampledKernelMatrix L z).PosSemidef

/-- The matrix-valued Herglotz kernel from manuscript equation (1). -/
def matrixHerglotzKernel {n : Type*} (K : ℂ → SquareMatrix n) (z w : ℂ) :
    SquareMatrix n :=
  (1 - z * starRingEnd ℂ w)⁻¹ • (K z + (K w)ᴴ)

private lemma one_sub_mul_star_ne_zero_of_norm_lt_one {a b : ℂ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : 1 - a * starRingEnd ℂ b ≠ 0 := by
  intro h
  have hab : a * starRingEnd ℂ b = 1 := (sub_eq_zero.mp h).symm
  have hnorm : ‖a * starRingEnd ℂ b‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg a) ha hb
  rw [hab, norm_one] at hnorm
  exact (lt_irrefl 1 hnorm).elim

private lemma unitCircle_mul_conj { ζ : ℂ } (hζ : ζ ∈ unitCircle) :
    ζ * starRingEnd ℂ ζ = 1 := by
  have hnorm : ‖ζ‖ = 1 := by
    simpa [unitCircle, Metric.mem_sphere, dist_eq_norm] using hζ
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
  norm_num

/-- The elementary scalar identity in manuscript lines 66--76, first isolated with exactly the
nonvanishing denominators required by field algebra. -/
theorem scalar_herglotz_kernel_identity_of_ne { ζ z w : ℂ }
    (hunit : ζ * starRingEnd ℂ ζ = 1)
    (hzw : 1 - z * starRingEnd ℂ w ≠ 0)
    (hz : ζ - z ≠ 0) (hw : ζ - w ≠ 0)
    (hzζ : 1 - z * starRingEnd ℂ ζ ≠ 0)
    (hwζ : 1 - starRingEnd ℂ w * ζ ≠ 0) :
    scalarHerglotzKernel ζ z w =
      2 / ((1 - z * starRingEnd ℂ ζ) * (1 - starRingEnd ℂ w * ζ)) := by
  have hfirst : (ζ + z) / (ζ - z) =
      (1 + z * starRingEnd ℂ ζ) / (1 - z * starRingEnd ℂ ζ) := by
    field_simp [hz, hzζ]
    rw [← hunit]
    ring
  have hconj : starRingEnd ℂ ((ζ + w) / (ζ - w)) =
      (1 + starRingEnd ℂ w * ζ) / (1 - starRingEnd ℂ w * ζ) := by
    have hstar : starRingEnd ℂ ζ - starRingEnd ℂ w ≠ 0 := by
      exact sub_ne_zero.mpr (star_injective.ne (sub_ne_zero.mp hw))
    rw [show starRingEnd ℂ ((ζ + w) / (ζ - w)) =
        (starRingEnd ℂ ζ + starRingEnd ℂ w) /
          (starRingEnd ℂ ζ - starRingEnd ℂ w) by simp]
    field_simp [hstar, hwζ]
    rw [← hunit]
    ring
  simp only [scalarHerglotzKernel, scalarHerglotzSummand]
  rw [hfirst, hconj]
  field_simp [hzw, hzζ, hwζ]
  ring_nf
  calc
    2 - z * starRingEnd ℂ ζ * starRingEnd ℂ w * ζ * 2 =
        2 - 2 * z * starRingEnd ℂ w * (ζ * starRingEnd ℂ ζ) := by ring
    _ = 2 - 2 * z * starRingEnd ℂ w * 1 := by rw [hunit]
    _ = 2 - z * starRingEnd ℂ w * 2 := by ring

/-- The elementary scalar identity with the geometric hypotheses stated in the manuscript. -/
theorem scalar_herglotz_kernel_identity { ζ z w : ℂ } (hζ : ζ ∈ unitCircle)
    (hz : z ∈ openUnitDisk) (hw : w ∈ openUnitDisk) :
    scalarHerglotzKernel ζ z w =
      2 / ((1 - z * starRingEnd ℂ ζ) * (1 - starRingEnd ℂ w * ζ)) := by
  have hζnorm : ‖ζ‖ = 1 := by
    simpa [unitCircle, Metric.mem_sphere, dist_eq_norm] using hζ
  have hznorm : ‖z‖ < 1 := by
    simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hwnorm : ‖w‖ < 1 := by
    simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hw
  have hζz : ζ - z ≠ 0 := by
    intro h
    have : ζ = z := sub_eq_zero.mp h
    rw [this] at hζnorm
    exact (ne_of_lt hznorm) hζnorm
  have hζw : ζ - w ≠ 0 := by
    intro h
    have : ζ = w := sub_eq_zero.mp h
    rw [this] at hζnorm
    exact (ne_of_lt hwnorm) hζnorm
  have hzw := one_sub_mul_star_ne_zero_of_norm_lt_one hznorm hwnorm.le
  have hzζ := one_sub_mul_star_ne_zero_of_norm_lt_one hznorm hζnorm.le
  have hwζ' := one_sub_mul_star_ne_zero_of_norm_lt_one hwnorm hζnorm.le
  have hwζ : 1 - starRingEnd ℂ w * ζ ≠ 0 := by
    have := (map_ne_zero_iff (starRingEnd ℂ) star_injective).2 hwζ'
    simpa [mul_comm] using this
  exact scalar_herglotz_kernel_identity_of_ne (unitCircle_mul_conj hζ) hzw hζz hζw hzζ hwζ

/-- Rank-one factorization of the scalar Herglotz kernel. -/
theorem scalar_herglotz_kernel_factorization { ζ z w : ℂ } (hζ : ζ ∈ unitCircle)
    (hz : z ∈ openUnitDisk) (hw : w ∈ openUnitDisk) :
    scalarHerglotzKernel ζ z w =
      2 * circleFeature ζ z * starRingEnd ℂ (circleFeature ζ w) := by
  rw [scalar_herglotz_kernel_identity hζ hz hw]
  simp [circleFeature, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]

/-- One positive matrix mass multiplied by one scalar Herglotz kernel. -/
def matrixHerglotzAtom {n : Type*} (ζ : ℂ) (M : SquareMatrix n) (z w : ℂ) :
    SquareMatrix n :=
  scalarHerglotzKernel ζ z w • M

/-- One matrix-valued summand in a Herglotz representation. -/
def matrixHerglotzSummand {n : Type*} (ζ : ℂ) (M : SquareMatrix n) (z : ℂ) :
    SquareMatrix n :=
  scalarHerglotzSummand ζ z • M

/-- Taking the manuscript's kernel of one Hermitian Herglotz summand gives its atom kernel. -/
theorem matrixHerglotzKernel_summand_eq_atom {n : Type*} { ζ z w : ℂ }
    {M : SquareMatrix n} (hM : M.IsHermitian) :
    matrixHerglotzKernel (matrixHerglotzSummand ζ M) z w =
      matrixHerglotzAtom ζ M z w := by
  ext i j
  simp [matrixHerglotzKernel, matrixHerglotzSummand, matrixHerglotzAtom,
    scalarHerglotzKernel, hM.eq, div_eq_mul_inv, mul_comm]
  ring

/-- Every finite sampling of a positive matrix Herglotz atom in the disk is positive
semidefinite.  The proof explicitly realizes the sampled matrix as `Bᴴ * (2 • M) * B`. -/
theorem matrixHerglotzAtom_isPositiveMatrixKernelOn {n : Type*} [Fintype n]
    [DecidableEq n] { ζ : ℂ } {M : SquareMatrix n} (hζ : ζ ∈ unitCircle)
    (hM : M.PosSemidef) : IsPositiveMatrixKernelOn openUnitDisk (matrixHerglotzAtom ζ M) := by
  intro m z hz
  let feature : Fin m → ℂ := fun i ↦ circleFeature ζ (z i)
  let B : Matrix n (Fin m × n) ℂ :=
    fun a ib ↦ if a = ib.2 then starRingEnd ℂ (feature ib.1) else 0
  have hfactor (i j : Fin m) : scalarHerglotzKernel ζ (z i) (z j) =
      2 * feature i * starRingEnd ℂ (feature j) := by
    simpa [feature] using scalar_herglotz_kernel_factorization hζ (hz i) (hz j)
  have hblock : sampledKernelMatrix (matrixHerglotzAtom ζ M) z =
      Bᴴ * ((2 : ℂ) • M) * B := by
    ext i j
    change scalarHerglotzKernel ζ (z i.1) (z j.1) * M i.2 j.2 =
      (Bᴴ * ((2 : ℂ) • M) * B) i j
    rw [hfactor]
    simp [Matrix.mul_apply, B, feature, mul_assoc, mul_comm, mul_left_comm]
    have hstarIf (x : n) :
        starRingEnd ℂ
            (if x = i.2 then starRingEnd ℂ (circleFeature ζ (z i.1)) else 0) =
          if x = i.2 then circleFeature ζ (z i.1) else 0 := by
      by_cases hx : x = i.2 <;> simp [hx]
    simp_rw [hstarIf]
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [hblock]
  exact (hM.smul (by positivity : (0 : ℂ) ≤ 2)).conjTranspose_mul_mul_same B

/-- Finite sums of positive matrix-valued kernels remain positive. -/
theorem isPositiveMatrixKernelOn_finset_sum { ι n : Type* } [Fintype n]
    [DecidableEq n] (s : Set ℂ) (t : Finset ι) (L : ι → ℂ → ℂ → SquareMatrix n)
    (hL : ∀ r ∈ t, IsPositiveMatrixKernelOn s (L r)) :
    IsPositiveMatrixKernelOn s (fun z w ↦ ∑ r ∈ t, L r z w) := by
  intro m z hz
  have hsum : sampledKernelMatrix (fun z w ↦ ∑ r ∈ t, L r z w) z =
      ∑ r ∈ t, sampledKernelMatrix (L r) z := by
    ext i j
    simp [sampledKernelMatrix, Matrix.sum_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum t fun r hr ↦ hL r hr m z hz

/-- Kernel of a finitely supported positive matrix-valued Herglotz measure. -/
def finiteMatrixHerglotzKernel { ι n : Type* } [Fintype ι] [DecidableEq ι]
    (ζ : ι → ℂ) (M : ι → SquareMatrix n) (z w : ℂ) : SquareMatrix n :=
  ∑ r, matrixHerglotzAtom (ζ r) (M r) z w

/-- The full finite-atomic case of the matrix Herglotz kernel theorem. -/
theorem finiteMatrixHerglotzKernel_isPositiveMatrixKernelOn
    { ι n : Type* } [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    { ζ : ι → ℂ } {M : ι → SquareMatrix n} (hζ : ∀ r, ζ r ∈ unitCircle)
    (hM : ∀ r, (M r).PosSemidef) :
    IsPositiveMatrixKernelOn openUnitDisk (finiteMatrixHerglotzKernel ζ M) := by
  simpa [finiteMatrixHerglotzKernel] using
    isPositiveMatrixKernelOn_finset_sum openUnitDisk Finset.univ
      (fun r ↦ matrixHerglotzAtom (ζ r) (M r))
      (fun r _ ↦ matrixHerglotzAtom_isPositiveMatrixKernelOn (hζ r) (hM r))

/-- The block-matrix definition of kernel positivity implies exactly the finite quadratic-form
inequality displayed in manuscript equation (2). -/
theorem finite_sampling_quadratic_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {s : Set ℂ} {L : ℂ → ℂ → SquareMatrix n} (hL : IsPositiveMatrixKernelOn s L)
    {m : ℕ} (z : Fin m → ℂ) (hz : ∀ i, z i ∈ s) (ξ : Fin m → n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j) := by
  let x : Fin m × n → ℂ := fun ia ↦ ξ ia.1 ia.2
  have hpair : 0 ≤ ∑ ia : Fin m × n, ∑ jb : Fin m × n,
      star (ξ ia.1 ia.2) * L (z ia.1) (z jb.1) ia.2 jb.2 * ξ jb.1 jb.2 := by
    have h := (hL m z hz).dotProduct_mulVec_nonneg x
    simpa [dotProduct, Matrix.mulVec, sampledKernelMatrix, x, Finset.mul_sum,
      mul_assoc] using h
  rw [show (∑ i, ∑ j, star (ξ i) ⬝ᵥ (L (z i) (z j) *ᵥ ξ j)) =
      ∑ ia : Fin m × n, ∑ jb : Fin m × n,
        star (ξ ia.1 ia.2) * L (z ia.1) (z jb.1) ia.2 jb.2 * ξ jb.1 jb.2 by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    rfl
    ]
  exact hpair

/-- Manuscript equation (2) for a single positive matrix mass in a Herglotz representation. -/
theorem matrixHerglotzAtom_finite_sampling_nonneg {n : Type*} [Fintype n]
    [DecidableEq n] { ζ : ℂ } {M : SquareMatrix n} (hζ : ζ ∈ unitCircle)
    (hM : M.PosSemidef) {m : ℕ} (z : Fin m → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (ξ : Fin m → n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (ξ i) ⬝ᵥ (matrixHerglotzAtom ζ M (z i) (z j) *ᵥ ξ j) :=
  finite_sampling_quadratic_nonneg
    (matrixHerglotzAtom_isPositiveMatrixKernelOn hζ hM) z hz ξ

end CrouzeixConjecture
