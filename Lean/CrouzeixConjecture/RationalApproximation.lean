module

public import CrouzeixConjecture.RationalCorollary
public import CrouzeixConjecture.NumericalRangeConvexity
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace CrouzeixConjecture

/-- The finite geometric polynomial in the affine variable `1 - c * (a - X)`.
It is the elementary replacement for the unavailable general Runge theorem. -/
def affineGeometricPolynomial (c a : ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range N,
    (Polynomial.C 1 - Polynomial.C c * (Polynomial.C a - Polynomial.X)) ^ i

/-- Polynomial approximant to `z ↦ (z - a)⁻¹` obtained from a geometric series. -/
def linearReciprocalPolynomial (c a : ℂ) (N : ℕ) : Polynomial ℂ :=
  Polynomial.C (-c) * affineGeometricPolynomial c a N

theorem eval_affineGeometricPolynomial (c a z : ℂ) (N : ℕ) :
    Polynomial.eval z (affineGeometricPolynomial c a N) =
      ∑ i ∈ Finset.range N, (1 - c * (a - z)) ^ i := by
  change (Polynomial.evalRingHom z)
      (∑ i ∈ Finset.range N,
        (Polynomial.C 1 - Polynomial.C c * (Polynomial.C a - Polynomial.X)) ^ i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem eval_linearReciprocalPolynomial (c a z : ℂ) (N : ℕ) :
    Polynomial.eval z (linearReciprocalPolynomial c a N) =
      -c * ∑ i ∈ Finset.range N, (1 - c * (a - z)) ^ i := by
  simp [linearReciprocalPolynomial, eval_affineGeometricPolynomial]

/-- Exact remainder formula for the affine geometric approximant. -/
theorem linearReciprocalPolynomial_error {c a z : ℂ} (hc : c ≠ 0) (hza : z ≠ a)
    (N : ℕ) :
    Polynomial.eval z (linearReciprocalPolynomial c a N) - (z - a)⁻¹ =
      c * (1 - c * (a - z)) ^ N / (c * (a - z)) := by
  rw [eval_linearReciprocalPolynomial]
  have haz : a - z ≠ 0 := sub_ne_zero.mpr hza.symm
  have hw : c * (a - z) ≠ 0 := mul_ne_zero hc haz
  have hinv : (z - a)⁻¹ = -c / (c * (a - z)) := by
    rw [show z - a = -(a - z) by ring, inv_neg]
    apply (eq_div_iff hw).2
    calc
      -(a - z)⁻¹ * (c * (a - z)) =
          -c * ((a - z)⁻¹ * (a - z)) := by ring
      _ = -c := by rw [inv_mul_cancel₀ haz, mul_one]
  rw [hinv]
  have hgeom :
      (∑ i ∈ Finset.range N, (1 - c * (a - z)) ^ i) * (c * (a - z)) =
        1 - (1 - c * (a - z)) ^ N := by
    convert geom_sum_mul_neg (1 - c * (a - z)) N using 1
    all_goals ring
  apply (eq_div_iff hw).2
  calc
    (-c * (∑ i ∈ Finset.range N, (1 - c * (a - z)) ^ i) -
          -c / (c * (a - z))) * (c * (a - z)) =
        -c * ((∑ i ∈ Finset.range N, (1 - c * (a - z)) ^ i) *
          (c * (a - z))) + c := by
      rw [sub_mul, div_mul_cancel₀ _ hw]
      ring
    _ = -c * (1 - (1 - c * (a - z)) ^ N) + c := by rw [hgeom]
    _ = c * (1 - c * (a - z)) ^ N := by ring

/-- A uniform affine contraction gives an explicit geometric error bound. -/
theorem norm_linearReciprocalPolynomial_error_le
    {K : Set ℂ} {c a : ℂ} {rho : ℝ}
    (hc : c ≠ 0) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ∀ z ∈ K, ‖1 - c * (a - z)‖ ≤ rho)
    (N : ℕ) {z : ℂ} (hz : z ∈ K) :
    ‖Polynomial.eval z (linearReciprocalPolynomial c a N) - (z - a)⁻¹‖ ≤
      ‖c‖ * rho ^ N / (1 - rho) := by
  have hza : z ≠ a := by
    intro h
    subst z
    have := hcontract a hz
    simp at this
    exact (not_le_of_gt hrho1) this
  rw [linearReciprocalPolynomial_error hc hza, norm_div, norm_mul, norm_pow]
  have hnum : ‖c‖ * ‖1 - c * (a - z)‖ ^ N ≤ ‖c‖ * rho ^ N := by
    gcongr
    exact hcontract z hz
  have hden : 1 - rho ≤ ‖c * (a - z)‖ := by
    calc
      1 - rho ≤ 1 - ‖1 - c * (a - z)‖ := by
        exact sub_le_sub_left (hcontract z hz) 1
      _ ≤ ‖1 - (1 - c * (a - z))‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (1 - c * (a - z))
      _ = ‖c * (a - z)‖ := by ring_nf
  exact div_le_div₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hrho0 _)) hnum
    (sub_pos.mpr hrho1) hden

/-- Under a uniform affine contraction, the explicit polynomials converge uniformly to the
reciprocal of the corresponding linear factor. -/
theorem tendstoUniformlyOn_eval_linearReciprocalPolynomial
    {K : Set ℂ} {c a : ℂ} {rho : ℝ}
    (hc : c ≠ 0) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ∀ z ∈ K, ‖1 - c * (a - z)‖ ≤ rho) :
    TendstoUniformlyOn
      (fun N z ↦ Polynomial.eval z (linearReciprocalPolynomial c a N))
      (fun z ↦ (z - a)⁻¹) atTop K := by
  refine Metric.tendstoUniformlyOn_iff.mpr fun epsilon hepsilon ↦ ?_
  have hlimit :
      Tendsto (fun N : ℕ ↦ ‖c‖ * rho ^ N / (1 - rho)) atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hrho0 hrho1).const_mul ‖c‖).div_const
        (1 - rho)
  filter_upwards [hlimit.eventually (Metric.ball_mem_nhds 0 hepsilon)] with N hN z hz
  have hbound : ‖c‖ * rho ^ N / (1 - rho) < epsilon := by
    have hnonneg : 0 ≤ ‖c‖ * rho ^ N / (1 - rho) :=
      div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hrho0 _))
        (sub_pos.mpr hrho1).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hN
    exact hN
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_linearReciprocalPolynomial_error_le hc hrho0 hrho1 hcontract N hz).trans_lt hbound

/-- A point outside a nonempty compact convex set has an affine rescaling for which the whole
set lies in a strict geometric-series disk.  This is the convex-separation ingredient behind the
polynomial approximation of a pole. -/
theorem exists_affineGeometric_contraction_of_compact_convex
    {K : Set ℂ} {a : ℂ}
    (hKcompact : IsCompact K) (hKne : K.Nonempty) (hKconvex : Convex ℝ K)
    (ha : a ∉ K) :
    ∃ (c : ℂ) (rho : ℝ),
      c ≠ 0 ∧ 0 ≤ rho ∧ rho < 1 ∧ ∀ z ∈ K, ‖1 - c * (a - z)‖ ≤ rho := by
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    RCLike.geometric_hahn_banach_compact_closed (𝕜 := ℂ)
      hKconvex hKcompact (convex_singleton a) isClosed_singleton
      (disjoint_singleton_right.mpr ha)
  have hfa : v < (f a).re := hfv a (mem_singleton a)
  let delta : ℝ := v - u
  have hdelta : 0 < delta := sub_pos.mpr huv
  have hflinear (x : ℂ) : f x = x * f 1 := by
    calc
      f x = f (x • (1 : ℂ)) := by simp
      _ = x • f 1 := by rw [map_smul]
      _ = x * f 1 := by simp [smul_eq_mul]
  have hpositive (z : ℂ) (hz : z ∈ K) : delta < (f (a - z)).re := by
    rw [map_sub]
    change delta < (f a).re - (f z).re
    have hzupper := hfu z hz
    exact sub_lt_sub hfa hzupper
  have hfcontinuous : Continuous (fun z : ℂ ↦ f (a - z)) := by fun_prop
  have himageCompact : IsCompact ((fun z : ℂ ↦ f (a - z)) '' K) :=
    hKcompact.image_of_continuousOn hfcontinuous.continuousOn
  obtain ⟨M, hM, hnormM⟩ := himageCompact.isBounded.exists_pos_norm_lt
  have hbound (z : ℂ) (hz : z ∈ K) : ‖f (a - z)‖ < M :=
    hnormM (f (a - z)) (mem_image_of_mem _ hz)
  let t : ℝ := delta / M ^ 2
  have ht : 0 < t := div_pos hdelta (sq_pos_of_pos hM)
  let c : ℂ := (t : ℂ) * f 1
  have hc : c ≠ 0 := by
    have hf1 : f 1 ≠ 0 := by
      obtain ⟨z, hz⟩ := hKne
      intro hf1zero
      have hfzero : f (a - z) = 0 := by
        rw [hflinear, hf1zero, mul_zero]
      have hp := hpositive z hz
      rw [hfzero, Complex.zero_re] at hp
      linarith
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') hf1
  have hcoefficient (z : ℂ) : c * (a - z) = (t : ℂ) * f (a - z) := by
    rw [hflinear]
    dsimp [c]
    ring
  have hstrict (z : ℂ) (hz : z ∈ K) : ‖1 - c * (a - z)‖ < 1 := by
    let w : ℂ := f (a - z)
    have hwre : delta < w.re := hpositive z hz
    have hwnorm : ‖w‖ < M := hbound z hz
    have hwnormsq : ‖w‖ ^ 2 < M ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) hM.le).mpr hwnorm
    have htM : t * M ^ 2 = delta := by
      dsimp [t]
      field_simp
    have htw : 0 < t * (w.re - delta) := mul_pos ht (sub_pos.mpr hwre)
    have htnorm : 0 ≤ t ^ 2 * (M ^ 2 - ‖w‖ ^ 2) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hwnormsq.le)
    rw [hcoefficient]
    change ‖1 - (t : ℂ) * w‖ < 1
    rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one]
    rw [one_pow, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, add_zero, Complex.sub_im, Complex.one_im, zero_sub]
    have hwnormcoord : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith
  have hobjective : Continuous (fun z : ℂ ↦ ‖1 - c * (a - z)‖) := by fun_prop
  obtain ⟨zmax, hzmax, hmax⟩ :=
    hKcompact.exists_isMaxOn hKne hobjective.continuousOn
  refine ⟨c, ‖1 - c * (a - zmax)‖, hc, norm_nonneg _, hstrict zmax hzmax, ?_⟩
  intro z hz
  exact hmax hz

/-- A reciprocal with its pole outside a nonempty compact convex set is a uniform limit of the
explicit geometric polynomials above. -/
theorem exists_polynomial_tendstoUniformlyOn_linear_reciprocal
    {K : Set ℂ} {a : ℂ}
    (hKcompact : IsCompact K) (hKne : K.Nonempty) (hKconvex : Convex ℝ K)
    (ha : a ∉ K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
        (fun z ↦ (z - a)⁻¹) atTop K := by
  obtain ⟨c, rho, hc, hrho0, hrho1, hcontract⟩ :=
    exists_affineGeometric_contraction_of_compact_convex hKcompact hKne hKconvex ha
  exact ⟨fun N ↦ linearReciprocalPolynomial c a N,
    tendstoUniformlyOn_eval_linearReciprocalPolynomial hc hrho0 hrho1 hcontract⟩

/-- Epsilon form of uniform polynomial approximation for a single pole. -/
theorem exists_polynomial_uniformly_approximates_linear_reciprocal
    {K : Set ℂ} {a : ℂ}
    (hKcompact : IsCompact K) (hKne : K.Nonempty) (hKconvex : Convex ℝ K)
    (ha : a ∉ K) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : Polynomial ℂ, ∀ z ∈ K, ‖Polynomial.eval z q - (z - a)⁻¹‖ < epsilon := by
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_linear_reciprocal hKcompact hKne hKconvex ha
  rw [Metric.tendstoUniformlyOn_iff] at hq
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq epsilon hepsilon)
  exact ⟨q N, fun z hz ↦ by
    simpa [dist_eq_norm, norm_sub_rev] using hN N le_rfl z hz⟩

/-- A finite product of reciprocal linear factors is continuous away from its listed poles. -/
theorem continuousOn_prod_linear_reciprocal
    {K : Set ℂ} (poles : List ℂ) (hfree : ∀ a ∈ poles, a ∉ K) :
    ContinuousOn (fun z : ℂ ↦ (poles.map fun a ↦ (z - a)⁻¹).prod) K := by
  induction poles with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact continuousOn_const
  | cons a poles ih =>
      have ha : a ∉ K := hfree a (by simp)
      have htail : ∀ b ∈ poles, b ∉ K := by
        intro b hb
        exact hfree b (by simp [hb])
      simp only [List.map_cons, List.prod_cons]
      exact (ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
        (fun z hz ↦ sub_ne_zero.mpr fun hza ↦ by
          have hza' : z = a := by simpa only [id_eq] using hza
          exact ha (hza' ▸ hz))).mul (ih htail)

/-- A finite product of linear reciprocals with all poles outside a nonempty compact convex set is
a uniform limit of polynomials.  Repeated entries in the list encode pole multiplicity. -/
theorem exists_polynomial_tendstoUniformlyOn_prod_linear_reciprocal
    {K : Set ℂ} (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKconvex : Convex ℝ K) :
    ∀ (poles : List ℂ), (∀ a ∈ poles, a ∉ K) →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
          (fun z ↦ (poles.map fun a ↦ (z - a)⁻¹).prod) atTop K := by
  intro poles
  induction poles with
  | nil =>
      intro
      refine ⟨fun _ ↦ 1, ?_⟩
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1)).tendstoUniformlyOn_const K
  | cons a poles ih =>
      intro hpoles
      have ha : a ∉ K := hpoles a (by simp)
      have htail : ∀ b ∈ poles, b ∉ K := by
        intro b hb
        exact hpoles b (by simp [hb])
      obtain ⟨qa, hqa⟩ :=
        exists_polynomial_tendstoUniformlyOn_linear_reciprocal hKcompact hKne hKconvex ha
      obtain ⟨qt, hqt⟩ := ih htail
      refine ⟨fun N ↦ qa N * qt N, ?_⟩
      have hca : ContinuousOn (fun z : ℂ ↦ (z - a)⁻¹) K :=
        ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
          (fun z hz ↦ sub_ne_zero.mpr fun hza ↦ ha (hza ▸ hz))
      have hct : ContinuousOn (fun z : ℂ ↦
          (poles.map fun b ↦ (z - b)⁻¹).prod) K :=
        continuousOn_prod_linear_reciprocal poles htail
      have hproduct :
          TendstoLocallyUniformlyOn
            ((fun N z ↦ Polynomial.eval z (qa N)) *
              (fun N z ↦ Polynomial.eval z (qt N)))
            ((fun z ↦ (z - a)⁻¹) *
              (fun z ↦ (poles.map fun b ↦ (z - b)⁻¹).prod)) atTop K :=
        hqa.tendstoLocallyUniformlyOn.mul₀ hqt.tendstoLocallyUniformlyOn hca hct
      apply
        (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKcompact).mp
      simpa [Polynomial.eval_mul] using hproduct

/-- The reciprocal of a nonzero complex polynomial with no zero on a nonempty compact convex set
is a uniform limit of polynomials.  The proof factors the denominator over `ℂ` and applies the
single-pole construction with multiplicity. -/
theorem exists_polynomial_tendstoUniformlyOn_polynomial_inverse
    {K : Set ℂ} (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKconvex : Convex ℝ K) (d : Polynomial ℂ)
    (hfree : ∀ z ∈ K, Polynomial.eval z d ≠ 0) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
        (fun z ↦ (Polynomial.eval z d)⁻¹) atTop K := by
  have hrootfree : ∀ a ∈ d.roots.toList, a ∉ K := by
    intro a ha haK
    have haroot : a ∈ d.roots := by simpa using ha
    exact hfree a haK (by simpa [Polynomial.IsRoot] using d.isRoot_of_mem_roots haroot)
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_prod_linear_reciprocal
      hKcompact hKne hKconvex d.roots.toList hrootfree
  let leadingInv : ℂ := d.leadingCoeff⁻¹
  refine ⟨fun N ↦ Polynomial.C leadingInv * q N, ?_⟩
  have hscaled := (uniformContinuous_const_smul leadingInv).comp_tendstoUniformlyOn hq
  have htarget (z : ℂ) :
      leadingInv * (d.roots.toList.map fun a ↦ (z - a)⁻¹).prod =
        (Polynomial.eval z d)⁻¹ := by
    rw [(IsAlgClosed.splits d).eval_eq_prod_roots z]
    simp [leadingInv, mul_comm]
  have hscaled' := hscaled.congr_right (fun z _ ↦ htarget z)
  simpa [Function.comp_def, Polynomial.eval_mul, smul_eq_mul] using hscaled'

/-- Full scalar Runge step needed by the manuscript's rational corollary: every reduced rational
function pole-free on a nonempty compact convex set is a uniform limit of complex polynomials.
No general Runge or Mergelyan theorem is assumed; this follows from finite denominator
factorization and the explicit geometric construction. -/
theorem exists_polynomial_tendstoUniformlyOn_rationalScalarEval
    {K : Set ℂ} (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKconvex : Convex ℝ K) (r : RatFunc ℂ) (hfree : RationalPoleFreeOn r K) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
        (rationalScalarEval r) atTop K := by
  have hdenfree : ∀ z ∈ K, Polynomial.eval z r.denom ≠ 0 :=
    (rationalPoleFreeOn_iff r K).mp hfree
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_polynomial_inverse
      hKcompact hKne hKconvex r.denom hdenfree
  refine ⟨fun N ↦ r.num * q N, ?_⟩
  have hnum :
      TendstoUniformlyOn
        (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.num)
        (fun z ↦ Polynomial.eval z r.num) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ _ _ ↦ by simpa using hepsilon
  have hnumContinuous : ContinuousOn (fun z ↦ Polynomial.eval z r.num) K :=
    r.num.continuous.continuousOn
  have hdenContinuous : ContinuousOn (fun z ↦ (Polynomial.eval z r.denom)⁻¹) K :=
    ContinuousOn.inv₀ r.denom.continuous.continuousOn hdenfree
  have hproduct :
      TendstoLocallyUniformlyOn
        ((fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.num) *
          (fun N z ↦ Polynomial.eval z (q N)))
        ((fun z ↦ Polynomial.eval z r.num) *
          (fun z ↦ (Polynomial.eval z r.denom)⁻¹)) atTop K :=
    hnum.tendstoLocallyUniformlyOn.mul₀ hq.tendstoLocallyUniformlyOn
      hnumContinuous hdenContinuous
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKcompact).mp
  simpa [Polynomial.eval_mul, rationalScalarEval, div_eq_mul_inv] using hproduct

/-- Epsilon form of the complete scalar rational-approximation theorem. -/
theorem exists_polynomial_uniformly_approximates_rationalScalarEval
    {K : Set ℂ} (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hKconvex : Convex ℝ K) (r : RatFunc ℂ) (hfree : RationalPoleFreeOn r K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : Polynomial ℂ,
      ∀ z ∈ K, ‖Polynomial.eval z q - rationalScalarEval r z‖ < epsilon := by
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_rationalScalarEval
      hKcompact hKne hKconvex r hfree
  rw [Metric.tendstoUniformlyOn_iff] at hq
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq epsilon hepsilon)
  exact ⟨q N, fun z hz ↦ by
    simpa [dist_eq_norm, norm_sub_rev] using hN N le_rfl z hz⟩

section MatrixConsequences

open scoped Matrix Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Once the polynomial Crouzeix estimate is known, uniform scalar convergence on the numerical
range implies convergence of the corresponding matrix polynomial evaluations. -/
theorem tendsto_polynomialEval_of_tendstoUniformlyOn_numericalRange
    (hMain : MainTheoremStatement (n := n)) (A : SquareMatrix n)
    (q : ℕ → Polynomial ℂ) (p : Polynomial ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
      (fun z ↦ Polynomial.eval z p) atTop (numericalRange A)) :
    Tendsto (fun N ↦ polynomialEval (q N) A) atTop (nhds (polynomialEval p A)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  rw [Metric.tendstoUniformlyOn_iff] at hq
  have hepsilonHalf : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq (epsilon / 2) hepsilonHalf)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨z, hz, hzmax⟩ :=
    exists_maxPolynomialModulusOnNumericalRange A (q k - p)
  have hscalar : ‖Polynomial.eval z (q k - p)‖ < epsilon / 2 := by
    have hdist := hN k hk z hz
    rw [dist_eq_norm] at hdist
    rw [Polynomial.eval_sub, norm_sub_rev]
    exact hdist
  have hbound := hMain A (q k - p)
  dsimp [PolynomialCrouzeixBound] at hbound
  rw [← hzmax] at hbound
  rw [dist_eq_norm]
  have hevalSub :
      polynomialEval (q k) A - polynomialEval p A = polynomialEval (q k - p) A := by
    simp [polynomialEval]
  rw [hevalSub]
  linarith

/-- Uniform approximation of a pole-free rational function on the numerical range supplies the
matrix-evaluation convergence required in the manuscript's rational limiting argument, assuming
the already-proved polynomial main theorem. -/
theorem tendsto_rationalMatrixEval_of_tendstoUniformlyOn_numericalRange
    (hMain : MainTheoremStatement (n := n)) (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A))
    (q : ℕ → Polynomial ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
      (rationalScalarEval r) atTop (numericalRange A)) :
    Tendsto (fun N ↦ polynomialEval (q N) A) atTop
      (nhds (rationalMatrixEval r A)) := by
  have hdenfree : ∀ z ∈ numericalRange A, Polynomial.eval z r.denom ≠ 0 :=
    (rationalPoleFreeOn_iff r (numericalRange A)).mp hfree
  have hden :
      TendstoUniformlyOn
        (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom)
        (fun z ↦ Polynomial.eval z r.denom) atTop (numericalRange A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ _ _ ↦ by simpa using hepsilon
  have hrContinuous : ContinuousOn (rationalScalarEval r) (numericalRange A) :=
    continuousOn_rationalScalarEval r (numericalRange A) hfree
  have hdenContinuous : ContinuousOn (fun z ↦ Polynomial.eval z r.denom) (numericalRange A) :=
    r.denom.continuous.continuousOn
  have hproductLocal :
      TendstoLocallyUniformlyOn
        ((fun N z ↦ Polynomial.eval z (q N)) *
          (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom))
        ((rationalScalarEval r) *
          (fun z ↦ Polynomial.eval z r.denom)) atTop (numericalRange A) :=
    hq.tendstoLocallyUniformlyOn.mul₀ hden.tendstoLocallyUniformlyOn
      hrContinuous hdenContinuous
  have hproduct :
      TendstoUniformlyOn
        (fun N z ↦ Polynomial.eval z (q N * r.denom))
        (fun z ↦ Polynomial.eval z r.num) atTop (numericalRange A) := by
    have hproductUniform :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_numericalRange A)).mp hproductLocal
    have hright :
        TendstoUniformlyOn
          ((fun N z ↦ Polynomial.eval z (q N)) *
            (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom))
          (fun z ↦ Polynomial.eval z r.num) atTop (numericalRange A) :=
      hproductUniform.congr_right (fun z hz ↦ by
        simp only [Pi.mul_apply, rationalScalarEval]
        exact div_mul_cancel₀ _ (hdenfree z hz))
    simpa [Polynomial.eval_mul] using hright
  have hmatrixProduct :=
    tendsto_polynomialEval_of_tendstoUniformlyOn_numericalRange
      hMain A (fun N ↦ q N * r.denom) r.num hproduct
  have hdenUnit : IsUnit (polynomialEval r.denom A) :=
    polynomialEval_denom_isUnit_of_rationalPoleFreeOn_numericalRange r A hfree
  have hmulInv := hmatrixProduct.mul_const (polynomialEval r.denom A)⁻¹
  have hdenDet : IsUnit (polynomialEval r.denom A).det :=
    (polynomialEval r.denom A).isUnit_iff_isUnit_det.mp hdenUnit
  have hcancel (X : SquareMatrix n) :
      X * polynomialEval r.denom A * (polynomialEval r.denom A)⁻¹ = X :=
    (polynomialEval r.denom A).mul_nonsing_inv_cancel_right X hdenDet
  change Tendsto
    (fun k ↦ polynomialEval (q k * r.denom) A * (polynomialEval r.denom A)⁻¹)
    atTop
    (nhds (polynomialEval r.num A * (polynomialEval r.denom A)⁻¹)) at hmulInv
  have hsource :
      (fun k ↦ polynomialEval (q k * r.denom) A *
        (polynomialEval r.denom A)⁻¹) =
      (fun k ↦ polynomialEval (q k) A) := by
    funext k
    rw [show polynomialEval (q k * r.denom) A =
        polynomialEval (q k) A * polynomialEval r.denom A by
      simp [polynomialEval]]
    exact hcancel (polynomialEval (q k) A)
  rw [hsource] at hmulInv
  simpa only [rationalMatrixEval] using hmulInv

/-- Every rational value on the numerical range is bounded by the attained rational maximum. -/
theorem norm_rationalScalarEval_le_maxRationalModulusOnNumericalRange
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A))
    {z : ℂ} (hz : z ∈ numericalRange A) :
    ‖rationalScalarEval r z‖ ≤ maxRationalModulusOnNumericalRange A r := by
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_numericalRange A).exists_isMaxOn (numericalRange_nonempty A)
      ((continuousOn_rationalScalarEval r (numericalRange A) hfree).norm)
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖rationalScalarEval r y‖) '' numericalRange A)
        ‖rationalScalarEval r w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxRationalModulusOnNumericalRange, hgreatest.csSup_eq]
  exact hmax hz

/-- Uniform scalar polynomial approximation on the numerical range implies convergence of the
displayed polynomial maxima to the displayed rational maximum. -/
theorem tendsto_maxPolynomialModulusOnNumericalRange_of_tendstoUniformlyOn_rationalScalarEval
    (A : SquareMatrix n) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (numericalRange A))
    (q : ℕ → Polynomial ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
      (rationalScalarEval r) atTop (numericalRange A)) :
    Tendsto (fun N ↦ maxPolynomialModulusOnNumericalRange A (q N)) atTop
      (nhds (maxRationalModulusOnNumericalRange A r)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  rw [Metric.tendstoUniformlyOn_iff] at hq
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hq epsilon hepsilon)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨zq, hzq, hzqmax⟩ :=
    exists_maxPolynomialModulusOnNumericalRange A (q k)
  obtain ⟨zr, hzr, hzrmax⟩ :=
    exists_maxRationalModulusOnNumericalRange A r hfree
  have hqclose := hN k hk zq hzq
  have hrclose := hN k hk zr hzr
  rw [dist_eq_norm] at hqclose hrclose
  have hqnorm :
      ‖Polynomial.eval zq (q k)‖ < ‖rationalScalarEval r zq‖ + epsilon := by
    have hdiff := norm_sub_norm_le (Polynomial.eval zq (q k)) (rationalScalarEval r zq)
    rw [norm_sub_rev] at hqclose
    linarith
  have hrnorm :
      ‖rationalScalarEval r zr‖ < ‖Polynomial.eval zr (q k)‖ + epsilon := by
    have hdiff := norm_sub_norm_le (rationalScalarEval r zr) (Polynomial.eval zr (q k))
    linarith
  have hupper :
      maxPolynomialModulusOnNumericalRange A (q k) <
        maxRationalModulusOnNumericalRange A r + epsilon := by
    rw [← hzqmax]
    exact hqnorm.trans_le (by
      simpa [add_comm] using add_le_add_right
        (norm_rationalScalarEval_le_maxRationalModulusOnNumericalRange
          A r hfree hzq) epsilon)
  have hlower :
      maxRationalModulusOnNumericalRange A r <
        maxPolynomialModulusOnNumericalRange A (q k) + epsilon := by
    rw [← hzrmax]
    exact hrnorm.trans_le (by
      simpa [add_comm] using add_le_add_right
        (norm_polynomial_eval_le_maxOnNumericalRange A (q k) hzr) epsilon)
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- On a convex numerical range, the elementary factor-by-factor construction supplies both
convergences required by the separate rational limiting corollary. -/
theorem exists_rationalPolynomialApproximation_on_numericalRange
    (hMain : MainTheoremStatement (n := n)) (A : SquareMatrix n) (r : RatFunc ℂ)
    (hconvex : Convex ℝ (numericalRange A))
    (hfree : RationalPoleFreeOn r (numericalRange A)) :
    ∃ q : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
          (rationalScalarEval r) atTop (numericalRange A) ∧
      Tendsto (fun N ↦ polynomialEval (q N) A) atTop
          (nhds (rationalMatrixEval r A)) ∧
      Tendsto (fun N ↦ maxPolynomialModulusOnNumericalRange A (q N)) atTop
          (nhds (maxRationalModulusOnNumericalRange A r)) := by
  obtain ⟨q, hq⟩ :=
    exists_polynomial_tendstoUniformlyOn_rationalScalarEval
      (isCompact_numericalRange A) (numericalRange_nonempty A) hconvex r hfree
  exact ⟨q, hq,
    tendsto_rationalMatrixEval_of_tendstoUniformlyOn_numericalRange
      hMain A r hfree q hq,
    tendsto_maxPolynomialModulusOnNumericalRange_of_tendstoUniformlyOn_rationalScalarEval
      A r hfree q hq⟩

/-- The manuscript's rational constant-two bound follows from the polynomial theorem and
convexity of the numerical range, using the proved factor-by-factor approximation. -/
theorem rationalCrouzeixBound_of_mainTheorem_of_convex_numericalRange
    (hMain : MainTheoremStatement (n := n)) (A : SquareMatrix n) (r : RatFunc ℂ)
    (hconvex : Convex ℝ (numericalRange A)) :
    RationalCrouzeixBound A r := by
  intro hfree
  obtain ⟨q, _, hmatrix, hmax⟩ :=
    exists_rationalPolynomialApproximation_on_numericalRange
      hMain A r hconvex hfree
  exact rationalCrouzeixBound_of_polynomial_approximation
    hMain A r q hmatrix hmax

/-- Quantified separate rational spectral-set corollary, reduced only to the polynomial theorem
and the independently formalized Toeplitz--Hausdorff convexity statement. -/
theorem rationalSpectralSetCorollary_of_mainTheorem_of_numericalRange_convex
    (hMain : MainTheoremStatement (n := n))
    (hconvex : ∀ A : SquareMatrix n, Convex ℝ (numericalRange A)) :
    RationalSpectralSetCorollaryStatement (n := n) := by
  intro A r
  exact rationalCrouzeixBound_of_mainTheorem_of_convex_numericalRange
    hMain A r (hconvex A)

/-- The manuscript's separate rational spectral-set conclusion, with Toeplitz--Hausdorff now
discharged internally. -/
theorem rationalSpectralSetCorollary_of_mainTheorem
    (hMain : MainTheoremStatement (n := n)) :
    RationalSpectralSetCorollaryStatement (n := n) :=
  rationalSpectralSetCorollary_of_mainTheorem_of_numericalRange_convex
    hMain numericalRange_convex

end MatrixConsequences

end CrouzeixConjecture
