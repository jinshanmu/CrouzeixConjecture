module

public import CrouzeixConjecture.FinalTheorems
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

noncomputable section

namespace CrouzeixConjecture

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The numerical range of a bounded operator on a complex Hilbert space.  Mathlib's inner
product is conjugate-linear in the first variable, so `⟪x, A x⟫_ℂ` is the same scalar as the
manuscript's first-variable-linear `⟨A x, x⟩`. -/
def operatorNumericalRange (A : H →L[ℂ] H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z}

/-- Polynomial evaluation at a bounded operator. -/
def operatorPolynomialEval (p : Polynomial ℂ) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  Polynomial.aeval A p

/-- The supremum of a polynomial's modulus on an operator numerical range. -/
def supPolynomialModulusOnOperatorNumericalRange
    (A : H →L[ℂ] H) (p : Polynomial ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖Polynomial.eval z p‖) '' operatorNumericalRange A)

theorem operatorNumericalRange_nonempty [Nontrivial H] (A : H →L[ℂ] H) :
    (operatorNumericalRange A).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let u : H := (‖x‖ : ℂ)⁻¹ • x
  have hnorm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul]
    simp [hx]
  exact ⟨inner ℂ u (A u), u, hnorm, rfl⟩

theorem norm_mem_operatorNumericalRange_le
    (A : H →L[ℂ] H) {z : ℂ} (hz : z ∈ operatorNumericalRange A) :
    ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by
      gcongr
      exact A.le_opNorm x
    _ = ‖A‖ := by rw [hx]; ring

theorem bddAbove_operatorPolynomialModulus
    (A : H →L[ℂ] H) (p : Polynomial ℂ) :
    BddAbove ((fun z : ℂ ↦ ‖Polynomial.eval z p‖) '' operatorNumericalRange A) := by
  have hrange : operatorNumericalRange A ⊆ Metric.closedBall (0 : ℂ) ‖A‖ := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using norm_mem_operatorNumericalRange_le A hz
  apply ((isCompact_closedBall (0 : ℂ) ‖A‖).bddAbove_image
    p.continuous.norm.continuousOn).mono
  exact Set.image_mono hrange

theorem supPolynomialModulusOnOperatorNumericalRange_nonneg [Nontrivial H]
    (A : H →L[ℂ] H) (p : Polynomial ℂ) :
    0 ≤ supPolynomialModulusOnOperatorNumericalRange A p := by
  obtain ⟨z, hz⟩ := operatorNumericalRange_nonempty A
  exact (norm_nonneg (Polynomial.eval z p)).trans
    (le_csSup (bddAbove_operatorPolynomialModulus A p) ⟨z, hz, rfl⟩)

section FiniteDimensional

variable [FiniteDimensional ℂ H]

private def matrixOfOperator
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (A : H →L[ℂ] H) :
    SquareMatrix (Fin (Module.finrank ℂ H)) :=
  LinearMap.toMatrixOrthonormal b A.toLinearMap

private theorem euclideanOperator_matrixOfOperator_apply
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (A : H →L[ℂ] H)
    (x : H) :
    euclideanOperator (matrixOfOperator b A) (b.repr x) = b.repr (A x) := by
  apply PiLp.ext
  intro i
  change (matrixOfOperator b A *ᵥ b.repr x) i = b.repr (A x) i
  simpa only [matrixOfOperator, OrthonormalBasis.coe_toBasis_repr_apply] using
    congrFun (LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A.toLinearMap x) i

private theorem euclideanOperator_polynomial_matrixOfOperator_apply
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (A : H →L[ℂ] H)
    (p : Polynomial ℂ) (x : H) :
    euclideanOperator (polynomialEval p (matrixOfOperator b A)) (b.repr x) =
      b.repr (operatorPolynomialEval p A x) := by
  have hpow : ∀ k : ℕ,
      euclideanOperator ((matrixOfOperator b A) ^ k) (b.repr x) = b.repr ((A ^ k) x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          euclideanOperator ((matrixOfOperator b A) ^ (k + 1)) (b.repr x) =
              euclideanOperator (matrixOfOperator b A)
                (euclideanOperator ((matrixOfOperator b A) ^ k) (b.repr x)) := by
            rw [pow_succ', map_mul]
            rfl
          _ = euclideanOperator (matrixOfOperator b A) (b.repr ((A ^ k) x)) := by rw [ih]
          _ = b.repr (A ((A ^ k) x)) := euclideanOperator_matrixOfOperator_apply b A _
          _ = b.repr ((A ^ (k + 1)) x) := by rw [pow_succ']; rfl
  rw [operatorPolynomialEval, polynomialEval, Polynomial.aeval_eq_sum_range,
    Polynomial.aeval_eq_sum_range]
  simp_rw [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    hpow]
  simp only [map_sum, map_smul]

private theorem numericalRange_matrixOfOperator
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (A : H →L[ℂ] H) :
    numericalRange (matrixOfOperator b A) = operatorNumericalRange A := by
  ext z
  constructor
  · rintro ⟨u, hu, hz⟩
    let x : H := b.repr.symm u
    refine ⟨x, ?_, ?_⟩
    · calc
        ‖x‖ = ‖u‖ := b.repr.symm.norm_map u
        _ = 1 := hu
    · calc
        inner ℂ x (A x) = inner ℂ (b.repr x) (b.repr (A x)) :=
          (b.repr.inner_map_map x (A x)).symm
        _ = inner ℂ u (euclideanOperator (matrixOfOperator b A) u) := by
          rw [← euclideanOperator_matrixOfOperator_apply b A x]
          simp [x]
        _ = z := hz
  · rintro ⟨x, hx, hz⟩
    refine ⟨b.repr x, ?_, ?_⟩
    · simpa only [b.repr.norm_map] using hx
    · calc
        inner ℂ (b.repr x) (euclideanOperator (matrixOfOperator b A) (b.repr x)) =
            inner ℂ (b.repr x) (b.repr (A x)) := by
              rw [euclideanOperator_matrixOfOperator_apply]
        _ = inner ℂ x (A x) := b.repr.inner_map_map x (A x)
        _ = z := hz

/-- The finite-matrix theorem transported to an arbitrary nonzero finite-dimensional complex
Hilbert space. -/
theorem finiteDimensionalHilbertPolynomialCrouzeix [Nontrivial H]
    (A : H →L[ℂ] H) (p : Polynomial ℂ) :
    ‖operatorPolynomialEval p A‖ ≤
      2 * supPolynomialModulusOnOperatorNumericalRange A p := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let C : SquareMatrix (Fin (Module.finrank ℂ H)) := matrixOfOperator b A
  letI : Nonempty (Fin (Module.finrank ℂ H)) := ⟨⟨0, Module.finrank_pos⟩⟩
  have hnorm : ‖operatorPolynomialEval p A‖ ≤ ‖polynomialEval p C‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    calc
      ‖operatorPolynomialEval p A x‖ = ‖b.repr (operatorPolynomialEval p A x)‖ :=
        (b.repr.norm_map _).symm
      _ = ‖euclideanOperator (polynomialEval p C) (b.repr x)‖ := by
        rw [euclideanOperator_polynomial_matrixOfOperator_apply]
      _ ≤ ‖euclideanOperator (polynomialEval p C)‖ * ‖b.repr x‖ :=
        (euclideanOperator (polynomialEval p C)).le_opNorm _
      _ = ‖polynomialEval p C‖ * ‖x‖ := by
        rw [matrix_norm_eq_euclidean_operator_norm, b.repr.norm_map]
  calc
    ‖operatorPolynomialEval p A‖ ≤ ‖polynomialEval p C‖ := hnorm
    _ ≤ 2 * maxPolynomialModulusOnNumericalRange C p := crouzeixConjecture C p
    _ = 2 * supPolynomialModulusOnOperatorNumericalRange A p := by
      congr 1
      exact congrArg sSup (congrArg (Set.image fun z : ℂ ↦ ‖Polynomial.eval z p‖)
        (numericalRange_matrixOfOperator b A))

/-- The finite-dimensional operator numerical range is convex. -/
theorem finiteDimensionalOperatorNumericalRange_convex [Nontrivial H]
    (A : H →L[ℂ] H) : Convex ℝ (operatorNumericalRange A) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  rw [← numericalRange_matrixOfOperator b A]
  exact numericalRange_convex _

end FiniteDimensional

private def krylovSubspace (A : H →L[ℂ] H) (x : H) (d : ℕ) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun k : Fin (d + 1) ↦ (A ^ (k : ℕ)) x)

private theorem pow_mem_krylovSubspace
    (A : H →L[ℂ] H) (x : H) (d k : ℕ) (hk : k ≤ d) :
    (A ^ k) x ∈ krylovSubspace A x d := by
  apply Submodule.subset_span
  exact ⟨⟨k, Nat.lt_succ_iff.mpr hk⟩, rfl⟩

/-- Compression of a bounded operator to a subspace with an orthogonal projection. -/
def operatorCompression (A : H →L[ℂ] H) (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] : M →L[ℂ] M :=
  M.orthogonalProjection.comp (A.comp M.subtypeL)

/-- Compression does not enlarge the operator numerical range. -/
theorem operatorNumericalRange_compression_subset
    (A : H →L[ℂ] H) (M : Submodule ℂ H) [M.HasOrthogonalProjection] :
    operatorNumericalRange (operatorCompression A M) ⊆ operatorNumericalRange A := by
  rintro z ⟨y, hy, hz⟩
  refine ⟨(y : H), hy, ?_⟩
  calc
    inner ℂ (y : H) (A y) = inner ℂ y (M.orthogonalProjection (A y)) :=
      (M.inner_orthogonalProjection_eq_of_mem_left y (A y)).symm
    _ = inner ℂ y (operatorCompression A M y) := rfl
    _ = z := hz

private theorem operatorPolynomialEval_apply_le_of_norm_one [Nontrivial H]
    (A : H →L[ℂ] H) (p : Polynomial ℂ) (x : H) (hx : ‖x‖ = 1) :
    ‖operatorPolynomialEval p A x‖ ≤
      2 * supPolynomialModulusOnOperatorNumericalRange A p := by
  let d : ℕ := p.natDegree
  let M : Submodule ℂ H := krylovSubspace A x d
  letI : FiniteDimensional ℂ M := by
    dsimp [M, krylovSubspace]
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let xm : M := ⟨x, pow_mem_krylovSubspace A x d 0 (Nat.zero_le d)⟩
  have hxm : ‖xm‖ = 1 := hx
  have hxm_ne : xm ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hxm]
    exact one_ne_zero
  letI : Nontrivial M := ⟨⟨xm, 0, hxm_ne⟩⟩
  let T : M →L[ℂ] M := operatorCompression A M
  have hpow : ∀ k : ℕ, k ≤ d → (((T ^ k) xm : M) : H) = (A ^ k) x := by
    intro k
    induction k with
    | zero =>
        intro _
        rfl
    | succ k ih =>
        intro hk
        have ih' := ih (Nat.le_trans (Nat.le_succ k) hk)
        have hmem : (A ^ (k + 1)) x ∈ M :=
          pow_mem_krylovSubspace A x d (k + 1) hk
        calc
          (((T ^ (k + 1)) xm : M) : H) = (T ((T ^ k) xm) : M) := by
            rw [pow_succ']
            rfl
          _ = (M.orthogonalProjection (A (((T ^ k) xm : M) : H)) : M) := rfl
          _ = (M.orthogonalProjection (A ((A ^ k) x)) : M) := by rw [ih']
          _ = (M.orthogonalProjection ((A ^ (k + 1)) x) : M) := by
            rw [pow_succ']
            rfl
          _ = (A ^ (k + 1)) x := congrArg Subtype.val
            (M.orthogonalProjection_mem_subspace_eq_self
              (⟨(A ^ (k + 1)) x, hmem⟩ : M))
  have hpoly :
      ((operatorPolynomialEval p T xm : M) : H) = operatorPolynomialEval p A x := by
    rw [operatorPolynomialEval, operatorPolynomialEval, Polynomial.aeval_eq_sum_range,
      Polynomial.aeval_eq_sum_range]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    change M.subtypeL (∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (T ^ k) xm) =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (A ^ k) x
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
    exact congrArg (fun v : H ↦ p.coeff k • v)
      (hpow k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hmax :
      supPolynomialModulusOnOperatorNumericalRange T p ≤
        supPolynomialModulusOnOperatorNumericalRange A p := by
    apply csSup_le_csSup (bddAbove_operatorPolynomialModulus A p)
    · exact (operatorNumericalRange_nonempty T).image _
    · exact Set.image_mono (operatorNumericalRange_compression_subset A M)
  calc
    ‖operatorPolynomialEval p A x‖ = ‖operatorPolynomialEval p T xm‖ := by
      rw [← hpoly]
      rfl
    _ ≤ ‖operatorPolynomialEval p T‖ * ‖xm‖ :=
      (operatorPolynomialEval p T).le_opNorm xm
    _ = ‖operatorPolynomialEval p T‖ := by rw [hxm, mul_one]
    _ ≤ 2 * supPolynomialModulusOnOperatorNumericalRange T p :=
      finiteDimensionalHilbertPolynomialCrouzeix T p
    _ ≤ 2 * supPolynomialModulusOnOperatorNumericalRange A p := by gcongr

/-- The manuscript's Hilbert-space consequence: every polynomial of a bounded operator is
bounded by twice its supremum on the operator numerical range. -/
theorem hilbertSpacePolynomialCrouzeix [CompleteSpace H] [Nontrivial H]
    (A : H →L[ℂ] H) (p : Polynomial ℂ) :
    ‖operatorPolynomialEval p A‖ ≤
      2 * supPolynomialModulusOnOperatorNumericalRange A p := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (supPolynomialModulusOnOperatorNumericalRange_nonneg A p))
  intro y
  by_cases hy : y = 0
  · simp [hy]
  · let x : H := (‖y‖ : ℂ)⁻¹ • y
    have hx : ‖x‖ = 1 := by
      dsimp [x]
      rw [norm_smul]
      simp [hy]
    have hyx : y = (‖y‖ : ℂ) • x := by
      simp [x, hy]
    calc
      ‖operatorPolynomialEval p A y‖ =
          ‖operatorPolynomialEval p A ((‖y‖ : ℂ) • x)‖ :=
        congrArg (fun v : H ↦ ‖operatorPolynomialEval p A v‖) hyx
      _ = ‖(‖y‖ : ℂ) • operatorPolynomialEval p A x‖ := by rw [map_smul]
      _ = ‖y‖ * ‖operatorPolynomialEval p A x‖ := by rw [norm_smul]; simp
      _ ≤ ‖y‖ * (2 * supPolynomialModulusOnOperatorNumericalRange A p) := by
        gcongr
        exact operatorPolynomialEval_apply_le_of_norm_one A p x hx
      _ = (2 * supPolynomialModulusOnOperatorNumericalRange A p) * ‖y‖ := by ring

end CrouzeixConjecture
