module

public import CrouzeixConjecture.SimpleSpectrumBridge
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.FieldTheory.Separable
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A fixed family of pairwise-distinct complex numbers indexed by `n`. -/
def densityDiagonalEntries (i : n) : ℂ := (Fintype.equivFin n i : ℕ)

omit [DecidableEq n] in
/-- The entries chosen for the comparison diagonal matrix are pairwise distinct. -/
theorem densityDiagonalEntries_injective :
    Function.Injective (densityDiagonalEntries (n := n)) := by
  intro i j hij
  apply (Fintype.equivFin n).injective
  apply Fin.ext
  exact Nat.cast_injective hij

/-- A fixed diagonal matrix with pairwise-distinct diagonal entries. -/
def densityDiagonal (n : Type*) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  Matrix.diagonal (densityDiagonalEntries (n := n))

/-- Explicit simple diagonalization data for `densityDiagonal`. -/
def densityDiagonal_simpleDiagonalization :
    SimpleDiagonalization (densityDiagonal n) where
  eigenvalues := densityDiagonalEntries
  changeBasis := 1
  eq_conjugate := by simp [densityDiagonal, innerConjugation]
  eigenvalues_injective := densityDiagonalEntries_injective

/-- The fixed comparison diagonal matrix has pairwise-distinct characteristic roots. -/
theorem densityDiagonal_hasDistinctEigenvalues :
    HasDistinctEigenvalues (densityDiagonal n) :=
  hasDistinctEigenvalues_of_simpleDiagonalization densityDiagonal_simpleDiagonalization

/-- The polynomial matrix on the affine line from `A` to `densityDiagonal n`.
Evaluating at `η` gives `A + η • (densityDiagonal n - A)`. -/
def simpleSpectrumPencil (A : SquareMatrix n) : Matrix n n (Polynomial ℂ) :=
  fun i j => Polynomial.C (A i j) + Polynomial.X *
    Polynomial.C (densityDiagonal n i j - A i j)

/-- The resultant of the characteristic polynomial of `simpleSpectrumPencil A`
and its derivative, regarded as a polynomial in the affine-line parameter. -/
def simpleSpectrumBadPolynomial (A : SquareMatrix n) : Polynomial ℂ :=
  let f := (simpleSpectrumPencil A).charpoly
  Polynomial.resultant f f.derivative

/-- Evaluation of the polynomial matrix gives the advertised affine matrix line. -/
theorem map_simpleSpectrumPencil (A : SquareMatrix n) (η : ℂ) :
    (simpleSpectrumPencil A).map (Polynomial.evalRingHom η) =
      A + η • (densityDiagonal n - A) := by
  ext i j
  simp [simpleSpectrumPencil]

/-- In positive finite dimension and characteristic zero, the derivative of a
matrix characteristic polynomial has the expected degree. -/
theorem natDegree_derivative_charpoly
    {R : Type*} [CommRing R] [CharZero R]
    (M : Matrix n n R) [Nonempty n] :
    M.charpoly.derivative.natDegree = Fintype.card n - 1 := by
  have hcard : Fintype.card n ≠ 0 := Fintype.card_ne_zero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  simp only [hk, Nat.succ_sub_one]
  apply le_antisymm
  · simpa only [Matrix.charpoly_natDegree_eq_dim, hk, Nat.add_sub_cancel] using
      Polynomial.natDegree_derivative_le M.charpoly
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [Polynomial.coeff_derivative]
    have hlead : M.charpoly.coeff (k + 1) = 1 := by
      have hdeg : M.charpoly.natDegree = k + 1 := by
        simpa only [hk] using Matrix.charpoly_natDegree_eq_dim M
      simpa only [hdeg] using M.charpoly_monic.coeff_natDegree
    rw [hlead, one_mul]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k) : ((k + 1 : ℕ) : R) ≠ 0)

/-- Evaluating the bad-parameter polynomial gives the characteristic resultant
of the corresponding matrix on the affine line. -/
theorem eval_simpleSpectrumBadPolynomial (A : SquareMatrix n) [Nonempty n] (η : ℂ) :
    Polynomial.eval η (simpleSpectrumBadPolynomial A) =
      Polynomial.resultant
        (A + η • (densityDiagonal n - A)).charpoly
        (A + η • (densityDiagonal n - A)).charpoly.derivative := by
  let f := (simpleSpectrumPencil A).charpoly
  let e := Polynomial.evalRingHom η
  have hfdeg : f.natDegree = Fintype.card n := Matrix.charpoly_natDegree_eq_dim _
  have hfderivdeg : f.derivative.natDegree = Fintype.card n - 1 :=
    natDegree_derivative_charpoly _
  have htargetdeg :
      (A + η • (densityDiagonal n - A)).charpoly.natDegree = Fintype.card n :=
    Matrix.charpoly_natDegree_eq_dim _
  have htargetderivdeg :
      (A + η • (densityDiagonal n - A)).charpoly.derivative.natDegree =
        Fintype.card n - 1 := natDegree_derivative_charpoly _
  change e (Polynomial.resultant f f.derivative) = _
  rw [← Polynomial.resultant_map_map f f.derivative f.natDegree f.derivative.natDegree e]
  have hmapf : Polynomial.map e f =
      (A + η • (densityDiagonal n - A)).charpoly := by
    rw [← Matrix.charpoly_map, map_simpleSpectrumPencil]
  have hmapderiv : Polynomial.map e f.derivative =
      (A + η • (densityDiagonal n - A)).charpoly.derivative := by
    rw [← Polynomial.derivative_map, hmapf]
  rw [hmapf, hmapderiv, hfdeg, hfderivdeg, htargetdeg, htargetderivdeg]

/-- Distinct characteristic roots imply that the characteristic polynomial and
its derivative have nonzero resultant. -/
theorem resultant_charpoly_derivative_ne_zero_of_hasDistinctEigenvalues
    (M : SquareMatrix n) (hM : HasDistinctEigenvalues M) :
    Polynomial.resultant M.charpoly M.charpoly.derivative ≠ 0 := by
  have hseparable : M.charpoly.Separable :=
    (Polynomial.nodup_roots_iff_of_splits M.charpoly_monic.ne_zero
      (IsAlgClosed.splits M.charpoly)).mp hM
  have hcoprime : IsCoprime M.charpoly M.charpoly.derivative :=
    (Polynomial.separable_def M.charpoly).mp hseparable
  exact (Polynomial.isUnit_resultant_iff_isCoprime M.charpoly_monic).mpr hcoprime |>.ne_zero

/-- The bad-parameter polynomial is not identically zero: at parameter `1`,
the affine line reaches `densityDiagonal n`, which has simple spectrum. -/
theorem simpleSpectrumBadPolynomial_ne_zero (A : SquareMatrix n) [Nonempty n] :
    simpleSpectrumBadPolynomial A ≠ 0 := by
  intro hzero
  have heval := eval_simpleSpectrumBadPolynomial A 1
  have hleft : Polynomial.eval 1 (simpleSpectrumBadPolynomial A) = 0 := by
    rw [hzero, Polynomial.eval_zero]
  have hright :
      Polynomial.resultant (densityDiagonal n).charpoly
        (densityDiagonal n).charpoly.derivative (Fintype.card n)
          (Fintype.card n - 1) ≠ 0 := by
    have h := resultant_charpoly_derivative_ne_zero_of_hasDistinctEigenvalues
      (densityDiagonal n) densityDiagonal_hasDistinctEigenvalues
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_derivative_charpoly] at h
    exact h
  have hmatrix : A + (1 : ℂ) • (densityDiagonal n - A) = densityDiagonal n := by
    simp
  have heval' : Polynomial.eval 1 (simpleSpectrumBadPolynomial A) =
      Polynomial.resultant (densityDiagonal n).charpoly
        (densityDiagonal n).charpoly.derivative (Fintype.card n)
          (Fintype.card n - 1) := by
    rw [hmatrix] at heval
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_derivative_charpoly] at heval
    exact heval
  exact hright (heval'.symm.trans hleft)

/-- A parameter where the bad-parameter polynomial does not vanish gives a
matrix with pairwise-distinct characteristic roots. -/
theorem hasDistinctEigenvalues_of_badPolynomial_eval_ne_zero
    (A : SquareMatrix n) [Nonempty n] {η : ℂ}
    (hη : Polynomial.eval η (simpleSpectrumBadPolynomial A) ≠ 0) :
    HasDistinctEigenvalues (A + η • (densityDiagonal n - A)) := by
  have hresultant :
      Polynomial.resultant
        (A + η • (densityDiagonal n - A)).charpoly
        (A + η • (densityDiagonal n - A)).charpoly.derivative ≠ 0 := by
    rwa [← eval_simpleSpectrumBadPolynomial]
  have hcoprime : IsCoprime
      (A + η • (densityDiagonal n - A)).charpoly
      (A + η • (densityDiagonal n - A)).charpoly.derivative := by
    by_contra hnot
    apply hresultant
    apply Polynomial.resultant_eq_zero_iff.mpr
    exact ⟨Or.inl (A + η • (densityDiagonal n - A)).charpoly_monic.ne_zero, hnot⟩
  exact Polynomial.nodup_roots
    ((Polynomial.separable_def _).mpr hcoprime)

/-- There are arbitrarily small nonzero parameters on the affine matrix line
for which the characteristic roots are pairwise distinct. -/
theorem exists_small_simpleSpectrumParameter (A : SquareMatrix n) [Nonempty n]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℂ, η ≠ 0 ∧ ‖η‖ < δ ∧
      Polynomial.eval η (simpleSpectrumBadPolynomial A) ≠ 0 := by
  let q := simpleSpectrumBadPolynomial A
  have hq : q ≠ 0 := simpleSpectrumBadPolynomial_ne_zero A
  have hinfinite : (((fun r : ℝ ↦ (r : ℂ)) '' Set.Ioo 0 δ) : Set ℂ).Infinite :=
    (Set.Ioo_infinite hδ).image Complex.ofReal_injective.injOn
  obtain ⟨η, ⟨r, hr, rfl⟩, havoid⟩ :=
    hinfinite.exists_notMem_finite q.roots.toFinset.finite_toSet
  refine ⟨(r : ℂ), ?_, ?_, ?_⟩
  · exact_mod_cast hr.1.ne'
  · simpa [abs_of_pos hr.1] using hr.2
  · intro heval
    apply havoid
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr heval)

/-- Every positive-dimensional complex square matrix can be approximated
arbitrarily closely, in the induced Euclidean operator norm, by a matrix with
pairwise-distinct characteristic roots. -/
theorem exists_hasDistinctEigenvalues_norm_sub_lt
    (A : SquareMatrix n) [Nonempty n] {ε : ℝ} (hε : 0 < ε) :
    ∃ B : SquareMatrix n, HasDistinctEigenvalues B ∧ ‖B - A‖ < ε := by
  let d : ℝ := ‖densityDiagonal n - A‖ + 1
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨η, _, hηnorm, hηgood⟩ :=
    exists_small_simpleSpectrumParameter A (show 0 < ε / d by positivity)
  let B := A + η • (densityDiagonal n - A)
  refine ⟨B, hasDistinctEigenvalues_of_badPolynomial_eval_ne_zero A hηgood, ?_⟩
  have hnorm_le :
      ‖η‖ * ‖densityDiagonal n - A‖ ≤ ‖η‖ * d := by
    apply mul_le_mul_of_nonneg_left
    · dsimp [d]
      linarith
    · exact norm_nonneg η
  have hnorm_lt : ‖η‖ * d < ε := by
    have := mul_lt_mul_of_pos_right hηnorm hd
    rwa [div_mul_cancel₀ ε hd.ne'] at this
  calc
    ‖B - A‖ = ‖η‖ * ‖densityDiagonal n - A‖ := by
      simp only [B, add_sub_cancel_left, norm_smul]
    _ ≤ ‖η‖ * d := hnorm_le
    _ < ε := hnorm_lt

/-- A concrete sequence of simple-spectrum approximants to `A`. -/
def simpleSpectrumApproximation (A : SquareMatrix n) [Nonempty n] (k : ℕ) :
    SquareMatrix n :=
  Classical.choose (exists_hasDistinctEigenvalues_norm_sub_lt A
    (show 0 < 1 / (k + 1 : ℝ) by positivity))

/-- Every member of `simpleSpectrumApproximation A` has pairwise-distinct
characteristic roots. -/
theorem simpleSpectrumApproximation_hasDistinctEigenvalues
    (A : SquareMatrix n) [Nonempty n] (k : ℕ) :
    HasDistinctEigenvalues (simpleSpectrumApproximation A k) :=
  (Classical.choose_spec (exists_hasDistinctEigenvalues_norm_sub_lt A
    (show 0 < 1 / (k + 1 : ℝ) by positivity))).1

/-- Quantitative error bound for the concrete simple-spectrum approximants. -/
theorem norm_simpleSpectrumApproximation_sub_lt
    (A : SquareMatrix n) [Nonempty n] (k : ℕ) :
    ‖simpleSpectrumApproximation A k - A‖ < 1 / (k + 1 : ℝ) :=
  (Classical.choose_spec (exists_hasDistinctEigenvalues_norm_sub_lt A
    (show 0 < 1 / (k + 1 : ℝ) by positivity))).2

/-- The concrete simple-spectrum approximants converge to `A` in the induced
Euclidean operator norm. -/
theorem tendsto_simpleSpectrumApproximation
    (A : SquareMatrix n) [Nonempty n] :
    Filter.Tendsto (simpleSpectrumApproximation A) Filter.atTop (nhds A) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k ↦ norm_nonneg _)
    (fun k ↦ (norm_simpleSpectrumApproximation_sub_lt A k).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end CrouzeixConjecture
