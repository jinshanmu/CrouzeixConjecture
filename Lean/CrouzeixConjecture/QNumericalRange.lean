module

public import CrouzeixConjecture.FinalTheorems
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unit vector pairs satisfying the constraint `y^* x = q`.  Mathlib's complex inner
product is conjugate-linear in the first variable, so `⟪y,x⟫_ℂ` has exactly the manuscript's
coordinate convention. -/
def qUnitPairs (q : ℂ) : Set (EuclideanVector n × EuclideanVector n) :=
  (Metric.sphere (0 : EuclideanVector n) 1 ×ˢ
      Metric.sphere (0 : EuclideanVector n) 1) ∩
    {xy | ⟪xy.2, xy.1⟫_ℂ = q}

/-- The scalar attached to a constrained pair in the scaled `q`-numerical range. -/
def scaledQValue (q : ℂ) (A : SquareMatrix n)
    (xy : EuclideanVector n × EuclideanVector n) : ℂ :=
  q⁻¹ * ⟪xy.2, euclideanOperator A xy.1⟫_ℂ

/-- The manuscript's scaled `q`-numerical range `Ω_q(A) = q⁻¹ W_q(A)`. -/
def scaledQNumericalRange (q : ℂ) (A : SquareMatrix n) : Set ℂ :=
  scaledQValue q A '' qUnitPairs q

/-- The auxiliary parameter `τ(r) = √(1-r²)` from the manuscript. -/
def qTau (r : ℝ) : ℝ :=
  √(1 - r ^ 2)

/-- The rank-one-stretch parameter `κ(r) = (1+√(1-r²))/r`. -/
def qKappa (r : ℝ) : ℝ :=
  (1 + qTau r) / r

theorem qTau_nonneg (r : ℝ) : 0 ≤ qTau r :=
  Real.sqrt_nonneg _

theorem qTau_sq {r : ℝ} (hr : r ≤ 1) (hr0 : 0 ≤ r) :
    qTau r ^ 2 = 1 - r ^ 2 := by
  rw [qTau, Real.sq_sqrt]
  nlinarith

theorem qKappa_pos {r : ℝ} (hr : 0 < r) : 0 < qKappa r := by
  rw [qKappa]
  exact div_pos (by linarith [qTau_nonneg r]) hr

theorem one_le_qKappa {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    1 ≤ qKappa r := by
  rw [qKappa, le_div_iff₀ hr0]
  have := qTau_nonneg r
  linarith

/-- The parameter identity `r = 2κ/(κ²+1)`. -/
theorem qKappa_parameter_identity {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    r = 2 * qKappa r / (qKappa r ^ 2 + 1) := by
  have htauSq := qTau_sq hr1 hr0.le
  have hden : r ≠ 0 := ne_of_gt hr0
  have hkden : qKappa r ^ 2 + 1 ≠ 0 := by positivity
  rw [qKappa]
  field_simp
  nlinarith

/-- The identity used to display the transferred sharp constant. -/
theorem two_div_qKappa {r : ℝ} (hr0 : 0 < r) :
    2 / qKappa r = 2 * r / (1 + √(1 - r ^ 2)) := by
  rw [qKappa, qTau]
  have hden : r ≠ 0 := ne_of_gt hr0
  have hsqrt : 1 + √(1 - r ^ 2) ≠ 0 := by positivity
  field_simp

omit [DecidableEq n] in
theorem mem_qUnitPairs_iff {q : ℂ} {xy : EuclideanVector n × EuclideanVector n} :
    xy ∈ qUnitPairs (n := n) q ↔
      ‖xy.1‖ = 1 ∧ ‖xy.2‖ = 1 ∧ ⟪xy.2, xy.1⟫_ℂ = q := by
  simp only [qUnitPairs, mem_inter_iff, mem_prod, mem_sphere_zero_iff_norm,
    mem_setOf_eq]
  tauto

theorem mem_scaledQNumericalRange_iff {q : ℂ} {A : SquareMatrix n} {z : ℂ} :
    z ∈ scaledQNumericalRange q A ↔
      ∃ x y : EuclideanVector n,
        ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ⟪y, x⟫_ℂ = q ∧
          q⁻¹ * ⟪y, euclideanOperator A x⟫_ℂ = z := by
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    exact ⟨x, y, (mem_qUnitPairs_iff.mp hxy).1,
      (mem_qUnitPairs_iff.mp hxy).2.1,
      (mem_qUnitPairs_iff.mp hxy).2.2, rfl⟩
  · rintro ⟨x, y, hx, hy, hxy, rfl⟩
    exact ⟨(x, y), mem_qUnitPairs_iff.mpr ⟨hx, hy, hxy⟩, rfl⟩

omit [DecidableEq n] in
theorem isClosed_qUnitPairs (q : ℂ) : IsClosed (qUnitPairs (n := n) q) := by
  have hinner : Continuous
      (fun xy : EuclideanVector n × EuclideanVector n ↦ ⟪xy.2, xy.1⟫_ℂ) :=
    continuous_snd.inner continuous_fst
  exact
    ((Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : EuclideanVector n) 1)).prod
      (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : EuclideanVector n) 1))).inter
      (isClosed_singleton.preimage hinner)

omit [DecidableEq n] in
theorem isCompact_qUnitPairs (q : ℂ) : IsCompact (qUnitPairs (n := n) q) := by
  have hinner : Continuous
      (fun xy : EuclideanVector n × EuclideanVector n ↦ ⟪xy.2, xy.1⟫_ℂ) :=
    continuous_snd.inner continuous_fst
  exact ((isCompact_sphere (0 : EuclideanVector n) 1).prod
      (isCompact_sphere (0 : EuclideanVector n) 1)).inter_right
    (isClosed_singleton.preimage hinner)

theorem continuous_scaledQValue (q : ℂ) (A : SquareMatrix n) :
    Continuous (scaledQValue q A) := by
  exact continuous_const.mul
    (continuous_snd.inner ((euclideanOperator A).continuous.comp continuous_fst))

/-- The scaled `q`-numerical range is compact, including the formally harmless `q = 0`
case of the definition.  Main statements separately require `q ≠ 0`. -/
theorem isCompact_scaledQNumericalRange (q : ℂ) (A : SquareMatrix n) :
    IsCompact (scaledQNumericalRange q A) := by
  exact (isCompact_qUnitPairs q).image (continuous_scaledQValue q A)

/-- For a matrix space of complex dimension at least two, every parameter in the closed unit
disk has constrained unit pairs. -/
theorem qUnitPairs_nonempty [Nontrivial n] {q : ℂ} (hq : ‖q‖ ≤ 1) :
    (qUnitPairs (n := n) q).Nonempty := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let x : EuclideanVector n := EuclideanSpace.single i 1
  let z : EuclideanVector n := EuclideanSpace.single j 1
  let tau : ℝ := √(1 - ‖q‖ ^ 2)
  let y : EuclideanVector n := conj q • x + (tau : ℂ) • z
  have hx : ‖x‖ = 1 := by simp [x]
  have hz : ‖z‖ = 1 := by simp [z]
  have hqSq : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
  have htau0 : 0 ≤ tau := Real.sqrt_nonneg _
  have htauSq : tau ^ 2 = 1 - ‖q‖ ^ 2 := by
    exact Real.sq_sqrt (sub_nonneg.mpr hqSq)
  have hxz : ⟪x, z⟫_ℂ = 0 := by
    simp [x, z, EuclideanSpace.inner_single_left, hij]
  have hzx : ⟪z, x⟫_ℂ = 0 := by
    simp [x, z, EuclideanSpace.inner_single_left, hij.symm]
  have horth : ⟪conj q • x, (tau : ℂ) • z⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, hxz]
    simp
  have hnormFirst : ‖conj q • x‖ = ‖q‖ := by
    simp [norm_smul, hx]
  have hnormSecond : ‖(tau : ℂ) • z‖ = tau := by
    rw [norm_smul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg htau0]
  have hySq : ‖y‖ ^ 2 = 1 := by
    calc
      ‖y‖ ^ 2 = ‖conj q • x‖ ^ 2 + ‖(tau : ℂ) • z‖ ^ 2 := by
        simpa [y, pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      _ = ‖q‖ ^ 2 + tau ^ 2 := by rw [hnormFirst, hnormSecond]
      _ = 1 := by rw [htauSq]; ring
  have hy : ‖y‖ = 1 := by nlinarith [norm_nonneg y]
  have hyx : ⟪y, x⟫_ℂ = q := by
    rw [show y = conj q • x + (tau : ℂ) • z by rfl,
      inner_add_left, inner_smul_left, inner_smul_left,
      inner_self_eq_norm_sq_to_K, hx, hzx]
    simp
  exact ⟨(x, y), mem_qUnitPairs_iff.mpr ⟨hx, hy, hyx⟩⟩

theorem scaledQNumericalRange_nonempty [Nontrivial n]
    {q : ℂ} (hq : ‖q‖ ≤ 1) (A : SquareMatrix n) :
    (scaledQNumericalRange q A).Nonempty := by
  obtain ⟨xy, hxy⟩ := qUnitPairs_nonempty (n := n) hq
  exact ⟨scaledQValue q A xy, xy, hxy, rfl⟩

/-- At `q = 1`, the scaled range is the ordinary numerical range. -/
theorem scaledQNumericalRange_one (A : SquareMatrix n) :
    scaledQNumericalRange 1 A = numericalRange A := by
  ext z
  constructor
  · rw [mem_scaledQNumericalRange_iff]
    rintro ⟨x, y, hx, hy, hxy, hz⟩
    have hnormsq : ‖y - x‖ ^ 2 = 0 := by
      rw [@norm_sub_sq ℂ, hy, hx, hxy]
      norm_num
    have hyx : y = x := by
      have hnorm : ‖y - x‖ = 0 := sq_eq_zero_iff.mp hnormsq
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    subst y
    refine ⟨x, hx, ?_⟩
    simpa using hz
  · rintro ⟨x, hx, rfl⟩
    rw [mem_scaledQNumericalRange_iff]
    refine ⟨x, x, hx, hx, ?_, ?_⟩
    · rw [inner_self_eq_norm_sq_to_K, hx]
      norm_num
    · simp

/-- Multiplication of the constrained second vector by the phase of `q` removes that phase
without changing the scaled value.  Thus the scaled range depends only on `‖q‖`. -/
theorem scaledQNumericalRange_eq_norm {q : ℂ} (hq : q ≠ 0) (A : SquareMatrix n) :
    scaledQNumericalRange q A = scaledQNumericalRange (‖q‖ : ℂ) A := by
  have hr : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hq)
  have hnormSq : (‖q‖ : ℂ) ^ 2 = conj q * q := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  let omega : ℂ := q / (‖q‖ : ℂ)
  have homegaNorm : ‖omega‖ = 1 := by
    dsimp [omega]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg q), div_self (norm_ne_zero_iff.mpr hq)]
  have homegaMul : omega * (‖q‖ : ℂ) = q := by
    dsimp [omega]
    rw [div_mul_cancel₀ q hr]
  have hconjOmegaMul : conj omega * q = (‖q‖ : ℂ) := by
    dsimp [omega]
    rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
      ← hnormSq, pow_two, mul_div_cancel_left₀ _ hr]
  have hforwardCoeff : (‖q‖ : ℂ)⁻¹ * conj omega = q⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by
      rw [mul_assoc, hconjOmegaMul, inv_mul_cancel₀ hr])
  have hreverseCoeff : q⁻¹ * omega = (‖q‖ : ℂ)⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by
      rw [mul_assoc, homegaMul, inv_mul_cancel₀ hq])
  ext z
  constructor
  · rw [mem_scaledQNumericalRange_iff]
    rintro ⟨x, y, hx, hy, hyx, hvalue⟩
    rw [mem_scaledQNumericalRange_iff]
    refine ⟨x, omega • y, hx, ?_, ?_, ?_⟩
    · simp [norm_smul, homegaNorm, hy]
    · rw [inner_smul_left, hyx, hconjOmegaMul]
    · rw [inner_smul_left, ← mul_assoc, hforwardCoeff]
      exact hvalue
  · rw [mem_scaledQNumericalRange_iff]
    rintro ⟨x, y, hx, hy, hyx, hvalue⟩
    rw [mem_scaledQNumericalRange_iff]
    refine ⟨x, conj omega • y, hx, ?_, ?_, ?_⟩
    · simp [norm_smul, homegaNorm, hy]
    · rw [inner_smul_left, Complex.conj_conj, hyx, homegaMul]
    · rw [inner_smul_left, Complex.conj_conj, ← mul_assoc, hreverseCoeff]
      exact hvalue

/-- Maximum polynomial modulus on the scaled `q`-numerical range. -/
def maxPolynomialModulusOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (p : Polynomial ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖p.eval z‖) '' scaledQNumericalRange q A)

theorem exists_maxPolynomialModulusOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (p : Polynomial ℂ)
    (hne : (scaledQNumericalRange q A).Nonempty) :
    ∃ z ∈ scaledQNumericalRange q A,
      ‖p.eval z‖ = maxPolynomialModulusOnScaledQNumericalRange q A p := by
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_scaledQNumericalRange q A).exists_isMaxOn hne
      p.continuous.norm.continuousOn
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖p.eval w‖) '' scaledQNumericalRange q A)
        ‖p.eval z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

theorem norm_polynomial_eval_le_maxOnScaledQNumericalRange
    (q : ℂ) (A : SquareMatrix n) (p : Polynomial ℂ)
    (hne : (scaledQNumericalRange q A).Nonempty)
    {z : ℂ} (hz : z ∈ scaledQNumericalRange q A) :
    ‖p.eval z‖ ≤ maxPolynomialModulusOnScaledQNumericalRange q A p := by
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_scaledQNumericalRange q A).exists_isMaxOn hne
      p.continuous.norm.continuousOn
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖p.eval y‖) '' scaledQNumericalRange q A)
        ‖p.eval w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxPolynomialModulusOnScaledQNumericalRange, hgreatest.csSup_eq]
  exact hmax hz

end CrouzeixConjecture
