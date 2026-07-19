module

public import CrouzeixConjecture.Positivity
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `k`th weighted Gramian summand `q⁻ᵏ C^{*k} C^k`. -/
def gramianTerm (q : ℝ) (C : SquareMatrix n) (k : ℕ) : SquareMatrix n :=
  (q⁻¹ ^ k) • ((C ^ k)ᴴ * C ^ k)

@[simp]
theorem gramianTerm_zero (q : ℝ) (C : SquareMatrix n) :
    gramianTerm q C 0 = 1 := by
  simp [gramianTerm]

/-- Each weighted Gramian summand is positive semidefinite when the weight is positive. -/
theorem gramianTerm_posSemidef {q : ℝ} (hq : 0 < q) (C : SquareMatrix n) (k : ℕ) :
    (gramianTerm q C k).PosSemidef := by
  exact (Matrix.posSemidef_conjTranspose_mul_self (C ^ k)).smul
    (pow_nonneg (inv_nonneg.mpr hq.le) k)

/-- Multiplying a Gramian summand on both sides advances its index. -/
theorem gramianTerm_succ {q : ℝ} (C : SquareMatrix n) (k : ℕ) :
    q⁻¹ • (Cᴴ * gramianTerm q C k * C) = gramianTerm q C (k + 1) := by
  simp [gramianTerm, pow_succ, mul_assoc, smul_smul, mul_comm]

/-- Geometric weights make the Gramian series converge whenever the powers of `C` are uniformly
bounded, exactly as used in manuscript lines 186–192. -/
theorem summable_gramianTerm {q M : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    Summable (gramianTerm q C) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (inv_nonneg.mpr (le_trans zero_le_one hq.le))
      (inv_lt_one_of_one_lt₀ hq)).mul_left (M * M))
  intro k
  rw [gramianTerm, norm_smul, Real.norm_eq_abs, abs_pow, abs_inv,
    abs_of_pos (lt_trans zero_lt_one hq)]
  have hk : ‖(C ^ k)ᴴ * C ^ k‖ ≤ M * M := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    exact mul_le_mul (hbound k) (hbound k) (norm_nonneg _) hM
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hk
    (pow_nonneg (inv_nonneg.mpr (le_trans zero_le_one hq.le)) k)

/-- The weighted Gramian matrix. -/
def gramian (q : ℝ) (C : SquareMatrix n) : SquareMatrix n :=
  ∑' k : ℕ, gramianTerm q C k

/-- A norm-convergent sum of positive semidefinite complex matrices is positive semidefinite. -/
theorem posSemidef_tsum [Nonempty n] {ι : Type*} (f : ι → SquareMatrix n)
    (hs : Summable f) (hpos : ∀ i, (f i).PosSemidef) :
    (∑' i, f i).PosSemidef := by
  have hHermitian : (∑' i, f i).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_tsum]
    exact tsum_congr fun k ↦
      (hpos k).isHermitian
  change IsPositiveMatrix (∑' i, f i)
  rw [isPositiveMatrix_iff_euclideanOperator_isPositive]
  rw [ContinuousLinearMap.isPositive_iff]
  have hSymmetric : (euclideanOperator (∑' i, f i)).IsSymmetric := by
    change (∑' i, f i).toEuclideanLin.IsSymmetric
    exact Matrix.isHermitian_iff_isSymmetric.mp hHermitian
  refine ⟨hSymmetric, fun x ↦ ?_⟩
  change 0 ≤ ⟪(euclideanOperator (∑' i, f i)).toLinearMap x, x⟫_ℂ
  rw [hSymmetric x x]
  have hsum :
      HasSum (fun i ↦ ⟪x, euclideanOperator (f i) x⟫_ℂ)
        (⟪x, euclideanOperator (∑' i, f i) x⟫_ℂ) := by
    simpa using hs.hasSum.mapL (euclideanQuadraticFormCLM x)
  change 0 ≤ ⟪x, euclideanOperator (∑' i, f i) x⟫_ℂ
  rw [← hsum.tsum_eq]
  exact tsum_nonneg fun i ↦
    ((isPositiveMatrix_iff_euclideanOperator_isPositive (f i)).mp (hpos i)).inner_nonneg_right x

/-- Removing one summand from a convergent sum of positive semidefinite matrices leaves a
positive semidefinite remainder. -/
theorem posSemidef_tsum_sub_single [Nonempty n] {ι : Type*} [DecidableEq ι]
    (f : ι → SquareMatrix n) (hs : Summable f) (hpos : ∀ i, (f i).PosSemidef) (j : ι) :
    ((∑' i, f i) - f j).PosSemidef := by
  let rest : Set ι := {i | i ∉ ({j} : Finset ι)}
  have hsrest : Summable (fun i : rest ↦ f i) := hs.subtype rest
  have hrest : (∑' i : rest, f i).PosSemidef :=
    posSemidef_tsum (fun i : rest ↦ f i) hsrest fun i ↦ hpos i
  have hsplit := hs.sum_add_tsum_subtype_compl ({j} : Finset ι)
  have heq : (∑' i, f i) - f j = ∑' i : rest, f i := by
    rw [← hsplit]
    simp [rest]
  rwa [heq]

/-- The norm-convergent Gramian is positive semidefinite. -/
theorem gramian_posSemidef [Nonempty n] {q M : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    (gramian q C).PosSemidef := by
  apply posSemidef_tsum (gramianTerm q C) (summable_gramianTerm hq hM C hbound)
  exact gramianTerm_posSemidef (lt_trans zero_lt_one hq) C

/-- The summand in `gramian 2 C - gramian 4 C`. -/
def gramianDifferenceTerm (C : SquareMatrix n) (k : ℕ) : SquareMatrix n :=
  gramianTerm 2 C k - gramianTerm 4 C k

@[simp]
theorem gramianDifferenceTerm_zero (C : SquareMatrix n) :
    gramianDifferenceTerm C 0 = 0 := by
  simp [gramianDifferenceTerm]

/-- Every coefficient `2⁻ᵏ - 4⁻ᵏ` in the difference Gramian is nonnegative. -/
theorem gramianDifferenceTerm_posSemidef (C : SquareMatrix n) (k : ℕ) :
    (gramianDifferenceTerm C k).PosSemidef := by
  rw [gramianDifferenceTerm, gramianTerm, gramianTerm, ← sub_smul]
  exact (Matrix.posSemidef_conjTranspose_mul_self (C ^ k)).smul
    (sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num : 0 ≤ (4 : ℝ)⁻¹)
      (by norm_num : (4 : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹) k))

/-- The difference of the two convergent Gramians is the sum of the difference terms. -/
theorem gramian_two_sub_gramian_four_eq_tsum {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    gramian 2 C - gramian 4 C = ∑' k : ℕ, gramianDifferenceTerm C k := by
  have h2 : Summable (gramianTerm 2 C) :=
    summable_gramianTerm (by norm_num) hM C hbound
  have h4 : Summable (gramianTerm 4 C) :=
    summable_gramianTerm (by norm_num) hM C hbound
  simpa [gramian, gramianDifferenceTerm] using (h2.hasSum.sub h4.hasSum).tsum_eq.symm

/-- The difference Gramian in manuscript equation (8) is positive semidefinite. -/
theorem gramian_two_sub_gramian_four_posSemidef [Nonempty n] {M : ℝ} (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    (gramian 2 C - gramian 4 C).PosSemidef := by
  rw [gramian_two_sub_gramian_four_eq_tsum hM C hbound]
  apply posSemidef_tsum (gramianDifferenceTerm C)
    ((summable_gramianTerm (q := 2) (by norm_num) hM C hbound).sub
      (summable_gramianTerm (q := 4) (by norm_num) hM C hbound))
  exact gramianDifferenceTerm_posSemidef C

/-- The first nonzero summand of the difference Gramian is `Cᴴ C / 4`, and the remaining
series is still positive semidefinite. -/
theorem gramian_two_sub_gramian_four_sub_first_posSemidef [Nonempty n] {M : ℝ}
    (hM : 0 ≤ M) (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    (gramian 2 C - gramian 4 C - (4 : ℝ)⁻¹ • (Cᴴ * C)).PosSemidef := by
  have hs : Summable (gramianDifferenceTerm C) :=
    (summable_gramianTerm (q := 2) (by norm_num) hM C hbound).sub
      (summable_gramianTerm (q := 4) (by norm_num) hM C hbound)
  have hrest := posSemidef_tsum_sub_single (gramianDifferenceTerm C) hs
    (gramianDifferenceTerm_posSemidef C) 1
  rw [← gramian_two_sub_gramian_four_eq_tsum hM C hbound] at hrest
  have hfirst : gramianDifferenceTerm C 1 = (4 : ℝ)⁻¹ • (Cᴴ * C) := by
    norm_num [gramianDifferenceTerm, gramianTerm, ← sub_smul]
  rwa [hfirst] at hrest

/-- The norm-convergent Gramian satisfies its Stein identity. -/
theorem gramian_stein_identity {q M : ℝ} (hq : 1 < q) (hM : 0 ≤ M)
    (C : SquareMatrix n) (hbound : ∀ k : ℕ, ‖C ^ k‖ ≤ M) :
    gramian q C = 1 + q⁻¹ • (Cᴴ * gramian q C * C) := by
  have hs : Summable (gramianTerm q C) := summable_gramianTerm hq hM C hbound
  calc
    gramian q C = gramianTerm q C 0 + ∑' k : ℕ, gramianTerm q C (k + 1) :=
      hs.tsum_eq_zero_add
    _ = 1 + q⁻¹ • (Cᴴ * gramian q C * C) := by
      rw [gramianTerm_zero]
      congr 1
      calc
        ∑' k : ℕ, gramianTerm q C (k + 1) =
            ∑' k : ℕ, q⁻¹ • (Cᴴ * gramianTerm q C k * C) := by
              exact tsum_congr fun k ↦ (gramianTerm_succ C k).symm
        _ = q⁻¹ • (Cᴴ * (∑' k : ℕ, gramianTerm q C k) * C) := by
          rw [← hs.tsum_mul_left Cᴴ, ← (hs.mul_left Cᴴ).tsum_mul_right C,
            ← (hs.mul_left Cᴴ |>.mul_right C).tsum_const_smul q⁻¹]
        _ = q⁻¹ • (Cᴴ * gramian q C * C) := by rfl

end CrouzeixConjecture
