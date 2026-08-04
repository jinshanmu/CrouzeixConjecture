module

public import CrouzeixConjecture.QRangeDisks
public import CrouzeixConjecture.QSimilarityStretch

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pythagoras for a rank-one stretch, in the form used by the sharp
product calculation. -/
theorem norm_stretchSimilarity_apply_sq
    {kappa : ℝ} (hkappa : 0 ≤ kappa) {v : EuclideanVector n} (hv : ‖v‖ = 1)
    (u : EuclideanVector n) :
    ‖euclideanOperator (stretchSimilarity kappa v) u‖ ^ 2 =
      kappa ^ 2 * ‖⟪v, u⟫_ℂ‖ ^ 2 +
        ‖u - ⟪v, u⟫_ℂ • v‖ ^ 2 := by
  let c : ℂ := ⟪v, u⟫_ℂ
  let w : EuclideanVector n := u - c • v
  have hvw : ⟪v, w⟫_ℂ = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have hkw : ⟪(kappa : ℂ) • (c • v), w⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_left, hvw]
    simp
  have hdecomp : euclideanOperator (stretchSimilarity kappa v) u =
      (kappa : ℂ) • (c • v) + w := by
    rw [euclideanOperator_stretchSimilarity_apply]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    ((kappa : ℂ) • (c • v)) w hkw
  rw [← hdecomp, norm_smul, norm_smul, hv, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkappa] at hpyth
  dsimp [c, w] at hpyth ⊢
  nlinarith

omit [DecidableEq n] in
/-- Squared norm of the component orthogonal to a unit vector. -/
theorem norm_sub_inner_smul_sq {v u : EuclideanVector n}
    (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖u - ⟪v, u⟫_ℂ • v‖ ^ 2 = 1 - ‖⟪v, u⟫_ℂ‖ ^ 2 := by
  let c : ℂ := ⟪v, u⟫_ℂ
  let w : EuclideanVector n := u - c • v
  have hvw : ⟪v, w⟫_ℂ = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have horth : ⟪c • v, w⟫_ℂ = 0 := by
    rw [inner_smul_left, hvw, mul_zero]
  have hdecomp : u = c • v + w := by simp [w]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • v) w horth
  rw [← hdecomp, norm_smul, hv, mul_one, hu] at hpyth
  dsimp [c, w] at hpyth ⊢
  nlinarith

/-- The inverse stretch obeys the analogous Pythagorean identity. -/
theorem norm_stretchInverseCandidate_apply_sq
    {kappa : ℝ} (hkappa : 0 ≤ kappa) {v : EuclideanVector n} (hv : ‖v‖ = 1)
    (u : EuclideanVector n) :
    ‖euclideanOperator (stretchInverseCandidate kappa v) u‖ ^ 2 =
      kappa⁻¹ ^ 2 * ‖⟪v, u⟫_ℂ‖ ^ 2 +
        ‖u - ⟪v, u⟫_ℂ • v‖ ^ 2 := by
  simpa only [stretchInverseCandidate, stretchSimilarity, Complex.ofReal_inv] using
    (norm_stretchSimilarity_apply_sq (inv_nonneg.mpr hkappa) hv u)

/-- Sharp norm-product estimate for a rank-one stretch. -/
theorem norm_stretch_product_le_half_add_inv [Nonempty n]
    {kappa : ℝ} (hkappa : 1 ≤ kappa) {v u : EuclideanVector n}
    (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    ‖euclideanOperator (stretchSimilarity kappa v) u‖ *
        ‖euclideanOperator (stretchInverseCandidate kappa v) u‖ ≤
      (kappa + kappa⁻¹) / 2 := by
  have hkappa0 : 0 < kappa := zero_lt_one.trans_le hkappa
  let t : ℝ := ‖⟪v, u⟫_ℂ‖ ^ 2
  let b : ℝ := ‖euclideanOperator (stretchSimilarity kappa v) u‖
  let a : ℝ := ‖euclideanOperator (stretchInverseCandidate kappa v) u‖
  have hrem : ‖u - ⟪v, u⟫_ℂ • v‖ ^ 2 = 1 - t := by
    simpa only [t] using norm_sub_inner_smul_sq hv hu
  have hbSq : b ^ 2 = kappa ^ 2 * t + (1 - t) := by
    simpa only [b, t, hrem] using
      (norm_stretchSimilarity_apply_sq hkappa0.le hv u)
  have haSq : a ^ 2 = kappa⁻¹ ^ 2 * t + (1 - t) := by
    simpa only [a, t, hrem] using
      (norm_stretchInverseCandidate_apply_sq hkappa0.le hv u)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    have := sq_nonneg ‖u - ⟪v, u⟫_ℂ • v‖
    rw [hrem] at this
    linarith
  have htQuarter : t * (1 - t) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (2 * t - 1)]
  have hkappaNe : kappa ≠ 0 := hkappa0.ne'
  have hproductIdentity :
      (kappa ^ 2 * t + (1 - t)) * (kappa⁻¹ ^ 2 * t + (1 - t)) =
        1 + (kappa - kappa⁻¹) ^ 2 * (t * (1 - t)) := by
    field_simp [hkappaNe]
    ring
  have hcoefficient : 0 ≤ (kappa - kappa⁻¹) ^ 2 := sq_nonneg _
  have hsquareBound : (b * a) ^ 2 ≤ ((kappa + kappa⁻¹) / 2) ^ 2 := by
    calc
      (b * a) ^ 2 = b ^ 2 * a ^ 2 := by ring
      _ = (kappa ^ 2 * t + (1 - t)) * (kappa⁻¹ ^ 2 * t + (1 - t)) := by
        rw [hbSq, haSq]
      _ = 1 + (kappa - kappa⁻¹) ^ 2 * (t * (1 - t)) := hproductIdentity
      _ ≤ 1 + (kappa - kappa⁻¹) ^ 2 * ((1 : ℝ) / 4) := by
        gcongr
      _ = ((kappa + kappa⁻¹) / 2) ^ 2 := by
        field_simp [hkappaNe]
        ring
  have hab0 : 0 ≤ b * a := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrhs0 : 0 ≤ (kappa + kappa⁻¹) / 2 := by positivity
  dsimp [b, a]
  nlinarith

/-- The two reciprocal stretches pair exactly as the identity. -/
theorem inner_stretchSimilarity_stretchInverseCandidate
    {kappa : ℝ} (hkappa : 0 < kappa) {v : EuclideanVector n} (hv : ‖v‖ = 1)
    (u : EuclideanVector n) :
    ⟪euclideanOperator (stretchSimilarity kappa v) u,
      euclideanOperator (stretchInverseCandidate kappa v) u⟫_ℂ = ⟪u, u⟫_ℂ := by
  let S := stretchSimilarity kappa v
  let T := stretchInverseCandidate kappa v
  have hHerm : Matrix.IsHermitian S := (stretchSimilarity_posDef hkappa hv).isHermitian
  have hAdj : ContinuousLinearMap.adjoint (euclideanOperator S) = euclideanOperator S := by
    rw [← euclideanOperator_conjTranspose, hHerm.eq]
  rw [← (euclideanOperator S).adjoint_inner_right, hAdj]
  have hST : S * T = 1 := stretchSimilarity_mul_inverseCandidate hkappa.ne' hv
  have hSTOp : euclideanOperator S * euclideanOperator T = 1 := by
    rw [← map_mul, hST, map_one]
  change ⟪u, (euclideanOperator S * euclideanOperator T) u⟫_ℂ = ⟪u, u⟫_ℂ
  rw [hSTOp]
  rfl

/-- The parameter identity in the exact form used by the rank-one stretch proof. -/
theorem qKappa_half_add_inv {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (qKappa r + (qKappa r)⁻¹) / 2 = r⁻¹ := by
  have hk0 : 0 < qKappa r := qKappa_pos hr0
  have hparam := qKappa_parameter_identity hr0 hr1
  field_simp [hr0.ne', hk0.ne'] at hparam ⊢
  nlinarith

/-- Every ordinary numerical-range point of a rank-one `qKappa` stretch belongs to the
corresponding scaled `q`-numerical range. -/
theorem numericalRange_stretchSimilarity_subset_scaledQNumericalRange [Nontrivial n]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (A : SquareMatrix n)
    {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    numericalRange
        (stretchSimilarity (qKappa r) v * A * (stretchSimilarity (qKappa r) v)⁻¹) ⊆
      scaledQNumericalRange (r : ℂ) A := by
  intro z hz
  obtain ⟨u, hu, hzu⟩ := hz
  let kappa : ℝ := qKappa r
  let S : SquareMatrix n := stretchSimilarity kappa v
  let T : SquareMatrix n := stretchInverseCandidate kappa v
  have hkappa0 : 0 < kappa := qKappa_pos hr0
  have hkappa1 : 1 ≤ kappa := one_le_qKappa hr0 hr1
  have hInv : S⁻¹ = T := stretchSimilarity_inv hkappa0.ne' hv
  have hpair : ⟪euclideanOperator S u, euclideanOperator T u⟫_ℂ = 1 := by
    calc
      ⟪euclideanOperator S u, euclideanOperator T u⟫_ℂ = ⟪u, u⟫_ℂ :=
        inner_stretchSimilarity_stretchInverseCandidate hkappa0 hv u
      _ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  let a : ℝ := ‖euclideanOperator T u‖
  let b : ℝ := ‖euclideanOperator S u‖
  have haNonneg : 0 ≤ a := norm_nonneg _
  have hbNonneg : 0 ≤ b := norm_nonneg _
  have habLower : 1 ≤ a * b := by
    have hCS : ‖⟪euclideanOperator S u, euclideanOperator T u⟫_ℂ‖ ≤ b * a := by
      exact norm_inner_le_norm (euclideanOperator S u) (euclideanOperator T u)
    rw [hpair, norm_one] at hCS
    simpa only [mul_comm] using hCS
  have habUpper : a * b ≤ r⁻¹ := by
    calc
      a * b = b * a := mul_comm _ _
      _ ≤ (kappa + kappa⁻¹) / 2 := by
        exact norm_stretch_product_le_half_add_inv hkappa1 hv hu
      _ = r⁻¹ := qKappa_half_add_inv hr0 hr1
  have ha0 : 0 < a := by nlinarith
  have hb0 : 0 < b := by nlinarith
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  let s : ℝ := (a * b)⁻¹
  have hs0 : 0 < s := inv_pos.mpr hab0
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (inv_le_one₀ hab0).mpr habLower
  have hrs : r ≤ s := by
    dsimp [s]
    rw [← mul_one (a * b)⁻¹, le_inv_mul_iff₀ hab0]
    have : a * b ≤ 1 / r := by simpa only [one_div] using habUpper
    exact (le_div_iff₀ hr0).mp this
  let x : EuclideanVector n := (a : ℂ)⁻¹ • euclideanOperator T u
  let y : EuclideanVector n := (b : ℂ)⁻¹ • euclideanOperator S u
  have hx : ‖x‖ = 1 := by
    rw [show x = (a : ℂ)⁻¹ • euclideanOperator T u by rfl, norm_smul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    exact inv_mul_cancel₀ ha0.ne'
  have hy : ‖y‖ = 1 := by
    rw [show y = (b : ℂ)⁻¹ • euclideanOperator S u by rfl, norm_smul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
    exact inv_mul_cancel₀ hb0.ne'
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hcoeff : conj ((b : ℂ)⁻¹) * (a : ℂ)⁻¹ = (s : ℂ) := by
    rw [map_inv₀, Complex.conj_ofReal]
    dsimp [s]
    push_cast
    field_simp [haC, hbC]
  have hyx : ⟪y, x⟫_ℂ = (s : ℂ) := by
    rw [show y = (b : ℂ)⁻¹ • euclideanOperator S u by rfl,
      show x = (a : ℂ)⁻¹ • euclideanOperator T u by rfl,
      inner_smul_left, inner_smul_right, hpair, mul_one, hcoeff]
  have hHerm : Matrix.IsHermitian S := (stretchSimilarity_posDef hkappa0 hv).isHermitian
  have hAdj : ContinuousLinearMap.adjoint (euclideanOperator S) = euclideanOperator S := by
    rw [← euclideanOperator_conjTranspose, hHerm.eq]
  have hzu' :
      ⟪u, euclideanOperator S (euclideanOperator A (euclideanOperator T u))⟫_ℂ = z := by
    rw [show S⁻¹ = T from hInv] at hzu
    change ⟪u, euclideanOperator (S * A * T) u⟫_ℂ = z at hzu
    rw [map_mul, map_mul] at hzu
    exact hzu
  have hcore :
      ⟪euclideanOperator S u, euclideanOperator A (euclideanOperator T u)⟫_ℂ = z := by
    rw [← (euclideanOperator S).adjoint_inner_right, hAdj]
    exact hzu'
  have hnormalized : ⟪y, euclideanOperator A x⟫_ℂ = (s : ℂ) * z := by
    rw [show y = (b : ℂ)⁻¹ • euclideanOperator S u by rfl,
      show x = (a : ℂ)⁻¹ • euclideanOperator T u by rfl,
      map_smul, inner_smul_left, inner_smul_right, hcore, ← mul_assoc, hcoeff]
  apply scaledQNumericalRange_antitone hr0 hrs hs1 A
  rw [mem_scaledQNumericalRange_iff]
  refine ⟨x, y, hx, hy, hyx, ?_⟩
  rw [hnormalized, ← mul_assoc, inv_mul_cancel₀]
  · exact one_mul z
  · exact_mod_cast hs0.ne'

/-- Phase-invariant form of the rank-one stretch inclusion. -/
theorem numericalRange_stretchSimilarity_subset_scaledQNumericalRange_complex
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    (A : SquareMatrix n) {v : EuclideanVector n} (hv : ‖v‖ = 1) :
    numericalRange
        (stretchSimilarity (qKappa ‖q‖) v * A *
          (stretchSimilarity (qKappa ‖q‖) v)⁻¹) ⊆
      scaledQNumericalRange q A := by
  rw [scaledQNumericalRange_eq_norm hq0 A]
  exact numericalRange_stretchSimilarity_subset_scaledQNumericalRange
    (norm_pos_iff.mpr hq0) hq1 A hv

end CrouzeixConjecture
