module

public import CrouzeixConjecture.HilbertSpace
public import CrouzeixConjecture.RationalApproximation
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

noncomputable section

open Filter Set
open scoped InnerProductSpace Topology

namespace CrouzeixConjecture

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Toeplitz--Hausdorff for a bounded operator, reduced to the already formalized
finite-dimensional theorem by compressing to the span of two witnesses. -/
theorem operatorNumericalRange_convex [Nontrivial H] (A : H →L[ℂ] H) :
    Convex ℝ (operatorNumericalRange A) := by
  rintro z ⟨x, hx, hzx⟩ w ⟨y, hy, hzy⟩ a b ha hb hab
  let M : Submodule ℂ H := Submodule.span ℂ ({x, y} : Set H)
  letI : FiniteDimensional ℂ M := by
    dsimp [M]
    exact FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton y).insert x)
  let xm : M := ⟨x, Submodule.subset_span (by simp)⟩
  let ym : M := ⟨y, Submodule.subset_span (by simp)⟩
  have hxm : ‖xm‖ = 1 := hx
  have hxm_ne : xm ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hxm]
    exact one_ne_zero
  letI : Nontrivial M := ⟨⟨xm, 0, hxm_ne⟩⟩
  let T : M →L[ℂ] M := operatorCompression A M
  have hzT : z ∈ operatorNumericalRange T := by
    refine ⟨xm, hxm, ?_⟩
    calc
      inner ℂ xm (T xm) = inner ℂ (xm : H) (A (xm : H)) := by
        exact M.inner_orthogonalProjection_eq_of_mem_left xm (A (xm : H))
      _ = z := hzx
  have hwT : w ∈ operatorNumericalRange T := by
    refine ⟨ym, hy, ?_⟩
    calc
      inner ℂ ym (T ym) = inner ℂ (ym : H) (A (ym : H)) := by
        exact M.inner_orthogonalProjection_eq_of_mem_left ym (A (ym : H))
      _ = w := hzy
  exact operatorNumericalRange_compression_subset A M
    (finiteDimensionalOperatorNumericalRange_convex T hzT hwT ha hb hab)

/-- The closed operator numerical range used by the Hilbert-space spectral-set statement. -/
def closedOperatorNumericalRange (A : H →L[ℂ] H) : Set ℂ :=
  closure (operatorNumericalRange A)

theorem operatorNumericalRange_isBounded (A : H →L[ℂ] H) :
    Bornology.IsBounded (operatorNumericalRange A) := by
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ‖A‖))
  intro z hz
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_mem_operatorNumericalRange_le A hz

theorem closedOperatorNumericalRange_nonempty [Nontrivial H] (A : H →L[ℂ] H) :
    (closedOperatorNumericalRange A).Nonempty :=
  (operatorNumericalRange_nonempty A).closure

theorem closedOperatorNumericalRange_isCompact (A : H →L[ℂ] H) :
    IsCompact (closedOperatorNumericalRange A) :=
  (operatorNumericalRange_isBounded A).isCompact_closure

theorem closedOperatorNumericalRange_convex [Nontrivial H] (A : H →L[ℂ] H) :
    Convex ℝ (closedOperatorNumericalRange A) :=
  (operatorNumericalRange_convex A).closure

section RationalApproximation

variable [CompleteSpace H] [Nontrivial H]

/-- A uniform scalar bound on the closed numerical range controls the corresponding operator
polynomial. -/
theorem norm_operatorPolynomialEval_le_of_forall_closedNumericalRange
    (A : H →L[ℂ] H) (p : Polynomial ℂ) (C : ℝ)
    (hC : ∀ z ∈ closedOperatorNumericalRange A, ‖Polynomial.eval z p‖ ≤ C) :
    ‖operatorPolynomialEval p A‖ ≤ 2 * C := by
  have hsup : supPolynomialModulusOnOperatorNumericalRange A p ≤ C := by
    apply csSup_le ((operatorNumericalRange_nonempty A).image _)
    rintro _ ⟨z, hz, rfl⟩
    exact hC z (subset_closure hz)
  exact (hilbertSpacePolynomialCrouzeix A p).trans (by gcongr)

/-- Uniform scalar convergence on the closed numerical range makes the corresponding operator
polynomial evaluations a Cauchy sequence. -/
theorem cauchySeq_operatorPolynomialEval_of_tendstoUniformlyOn
    (A : H →L[ℂ] H) (q : ℕ → Polynomial ℂ) (f : ℂ → ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N)) f atTop
      (closedOperatorNumericalRange A)) :
    CauchySeq (fun N ↦ operatorPolynomialEval (q N) A) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  have huniform := Metric.uniformCauchySeqOn_iff.mp hq.uniformCauchySeqOn
  obtain ⟨N, hN⟩ := huniform (epsilon / 4) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  rw [dist_eq_norm]
  have hevalSub :
      operatorPolynomialEval (q m) A - operatorPolynomialEval (q n) A =
        operatorPolynomialEval (q m - q n) A := by
    simp [operatorPolynomialEval]
  rw [hevalSub]
  have hbound := norm_operatorPolynomialEval_le_of_forall_closedNumericalRange
    A (q m - q n) (epsilon / 4) (fun z hz ↦ by
      have hz' := hN m hm n hn z hz
      simpa [Polynomial.eval_sub, dist_eq_norm] using hz'.le)
  linarith

/-- A fixed choice of the scalar polynomial approximation proved in `RationalApproximation`. -/
def operatorRationalApproximants (A : H →L[ℂ] H) (r : RatFunc ℂ) :
    ℕ → Polynomial ℂ := by
  classical
  exact dite (RationalPoleFreeOn r (closedOperatorNumericalRange A))
    (fun hfree ↦ Classical.choose
      (exists_polynomial_tendstoUniformlyOn_rationalScalarEval
        (closedOperatorNumericalRange_isCompact A)
        (closedOperatorNumericalRange_nonempty A)
        (closedOperatorNumericalRange_convex A) r hfree))
    (fun _ ↦ fun _ ↦ 0)

omit [CompleteSpace H] in
theorem operatorRationalApproximants_tendstoUniformlyOn
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    TendstoUniformlyOn
      (fun N z ↦ Polynomial.eval z (operatorRationalApproximants A r N))
      (rationalScalarEval r) atTop (closedOperatorNumericalRange A) := by
  simpa [operatorRationalApproximants, hfree] using
    Classical.choose_spec
      (exists_polynomial_tendstoUniformlyOn_rationalScalarEval
        (closedOperatorNumericalRange_isCompact A)
        (closedOperatorNumericalRange_nonempty A)
        (closedOperatorNumericalRange_convex A) r hfree)

/-- Approximation-based rational functional calculus on a Hilbert space.  For a pole-free
rational function the chosen operator-polynomial sequence is Cauchy, so this `limUnder` is its
unique operator-norm limit. -/
def operatorRationalEval (r : RatFunc ℂ) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  limUnder atTop (fun N ↦ operatorPolynomialEval (operatorRationalApproximants A r N) A)

theorem operatorRationalApproximants_tendsto
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    Tendsto (fun N ↦ operatorPolynomialEval (operatorRationalApproximants A r N) A)
      atTop (nhds (operatorRationalEval r A)) := by
  have hcauchy := cauchySeq_operatorPolynomialEval_of_tendstoUniformlyOn A
    (operatorRationalApproximants A r) (rationalScalarEval r)
    (operatorRationalApproximants_tendstoUniformlyOn A r hfree)
  exact hcauchy.tendsto_limUnder

/-- Two polynomial sequences with the same uniform scalar limit have operator evaluations whose
difference tends to zero. -/
theorem tendsto_operatorPolynomialEval_sub_zero_of_same_uniform_limit
    (A : H →L[ℂ] H) (q s : ℕ → Polynomial ℂ) (f : ℂ → ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N)) f atTop
      (closedOperatorNumericalRange A))
    (hs : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (s N)) f atTop
      (closedOperatorNumericalRange A)) :
    Tendsto (fun N ↦ operatorPolynomialEval (q N) A - operatorPolynomialEval (s N) A)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  rw [Metric.tendstoUniformlyOn_iff] at hq hs
  have heighth : 0 < epsilon / 8 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hq (epsilon / 8) heighth).and (hs (epsilon / 8) heighth))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hqN := (hN n hn).1
  have hsN := (hN n hn).2
  rw [dist_zero_right]
  have hevalSub :
      operatorPolynomialEval (q n) A - operatorPolynomialEval (s n) A =
        operatorPolynomialEval (q n - s n) A := by
    simp [operatorPolynomialEval]
  rw [hevalSub]
  have hbound := norm_operatorPolynomialEval_le_of_forall_closedNumericalRange
    A (q n - s n) (epsilon / 4) (fun z hz ↦ by
      have hqz := hqN z hz
      have hsz := hsN z hz
      exact (calc
        ‖Polynomial.eval z (q n - s n)‖ =
            dist (Polynomial.eval z (q n)) (Polynomial.eval z (s n)) := by
              rw [Polynomial.eval_sub, dist_eq_norm]
        _ ≤ dist (Polynomial.eval z (q n)) (f z) +
            dist (f z) (Polynomial.eval z (s n)) := dist_triangle _ _ _
        _ < epsilon / 8 + epsilon / 8 := by
          exact add_lt_add (by simpa [dist_comm] using hqz) hsz
        _ = epsilon / 4 := by ring).le)
  linarith

/-- Uniform convergence on the closed numerical range to a polynomial passes through the
operator polynomial calculus. -/
theorem tendsto_operatorPolynomialEval_of_tendstoUniformlyOn_polynomial
    (A : H →L[ℂ] H) (q : ℕ → Polynomial ℂ) (p : Polynomial ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
      (fun z ↦ Polynomial.eval z p) atTop (closedOperatorNumericalRange A)) :
    Tendsto (fun N ↦ operatorPolynomialEval (q N) A) atTop
      (nhds (operatorPolynomialEval p A)) := by
  have hp : TendstoUniformlyOn
      (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z p) (fun z ↦ Polynomial.eval z p) atTop
      (closedOperatorNumericalRange A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ _ _ ↦ by simpa using hepsilon
  have hdiff := tendsto_operatorPolynomialEval_sub_zero_of_same_uniform_limit A q
    (fun _ ↦ p) (fun z ↦ Polynomial.eval z p) hq hp
  have hconst : Tendsto (fun _ : ℕ ↦ operatorPolynomialEval p A) atTop
      (nhds (operatorPolynomialEval p A)) := tendsto_const_nhds
  convert hdiff.add hconst using 1 <;> simp

/-- The approximation-based value is independent of the chosen uniformly convergent polynomial
sequence. -/
theorem tendsto_operatorPolynomialEval_of_rational_approximation
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A))
    (q : ℕ → Polynomial ℂ)
    (hq : TendstoUniformlyOn (fun N z ↦ Polynomial.eval z (q N))
      (rationalScalarEval r) atTop (closedOperatorNumericalRange A)) :
    Tendsto (fun N ↦ operatorPolynomialEval (q N) A) atTop
      (nhds (operatorRationalEval r A)) := by
  have hdiff := tendsto_operatorPolynomialEval_sub_zero_of_same_uniform_limit A q
    (operatorRationalApproximants A r) (rationalScalarEval r) hq
    (operatorRationalApproximants_tendstoUniformlyOn A r hfree)
  have hchosen := operatorRationalApproximants_tendsto A r hfree
  convert hdiff.add hchosen using 1 <;> simp

/-- Supremum of a rational function's modulus on the closed operator numerical range. -/
def supRationalModulusOnClosedOperatorNumericalRange
    (A : H →L[ℂ] H) (r : RatFunc ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖rationalScalarEval r z‖) '' closedOperatorNumericalRange A)

omit [CompleteSpace H] [Nontrivial H] in
theorem bddAbove_rationalModulusOnClosedOperatorNumericalRange
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    BddAbove ((fun z : ℂ ↦ ‖rationalScalarEval r z‖) '' closedOperatorNumericalRange A) :=
  (closedOperatorNumericalRange_isCompact A).bddAbove_image
    ((continuousOn_rationalScalarEval r (closedOperatorNumericalRange A) hfree).norm)

omit [CompleteSpace H] [Nontrivial H] in
theorem norm_rationalScalarEval_le_sup_closedOperatorNumericalRange
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A))
    {z : ℂ} (hz : z ∈ closedOperatorNumericalRange A) :
    ‖rationalScalarEval r z‖ ≤ supRationalModulusOnClosedOperatorNumericalRange A r :=
  le_csSup (bddAbove_rationalModulusOnClosedOperatorNumericalRange A r hfree)
    ⟨z, hz, rfl⟩

omit [CompleteSpace H] in
theorem supRationalModulusOnClosedOperatorNumericalRange_nonneg
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    0 ≤ supRationalModulusOnClosedOperatorNumericalRange A r := by
  obtain ⟨z, hz⟩ := closedOperatorNumericalRange_nonempty A
  exact (norm_nonneg (rationalScalarEval r z)).trans
    (norm_rationalScalarEval_le_sup_closedOperatorNumericalRange A r hfree hz)

/-- The constant-two rational estimate on a nonzero complex Hilbert space. -/
theorem hilbertSpaceRationalCrouzeix
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    ‖operatorRationalEval r A‖ ≤
      2 * supRationalModulusOnClosedOperatorNumericalRange A r := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hscalar := operatorRationalApproximants_tendstoUniformlyOn A r hfree
  rw [Metric.tendstoUniformlyOn_iff] at hscalar
  have hoperator := operatorRationalApproximants_tendsto A r hfree
  apply le_of_tendsto hoperator.norm
  filter_upwards [hscalar (epsilon / 8) (by positivity)] with N hN
  have hbound := norm_operatorPolynomialEval_le_of_forall_closedNumericalRange A
    (operatorRationalApproximants A r N)
    (supRationalModulusOnClosedOperatorNumericalRange A r + epsilon / 8)
    (fun z hz ↦ by
      have hzsup := norm_rationalScalarEval_le_sup_closedOperatorNumericalRange A r hfree hz
      have hzclose := hN z hz
      calc
        ‖Polynomial.eval z (operatorRationalApproximants A r N)‖ ≤
            ‖rationalScalarEval r z‖ +
              ‖Polynomial.eval z (operatorRationalApproximants A r N) -
                rationalScalarEval r z‖ :=
          norm_le_norm_add_norm_sub' _ _
        _ ≤ supRationalModulusOnClosedOperatorNumericalRange A r + epsilon / 8 := by
          gcongr
          simpa [dist_eq_norm, norm_sub_rev] using hzclose.le)
  linarith

/-- The spectrum of a bounded operator lies in its closed numerical range.  The proof uses the
same polynomial approximation mechanism as the rational bound: outside the closed numerical
range, polynomial approximants to `z ↦ (z - a)⁻¹` converge at the operator and provide a
two-sided inverse for `A - aI`. -/
theorem spectrum_subset_closedOperatorNumericalRange (A : H →L[ℂ] H) :
    spectrum ℂ A ⊆ closedOperatorNumericalRange A := by
  intro a haSpectrum
  by_contra haRange
  obtain ⟨q, hq⟩ := exists_polynomial_tendstoUniformlyOn_linear_reciprocal
    (closedOperatorNumericalRange_isCompact A)
    (closedOperatorNumericalRange_nonempty A)
    (closedOperatorNumericalRange_convex A) haRange
  let R : H →L[ℂ] H :=
    limUnder atTop (fun N ↦ operatorPolynomialEval (q N) A)
  have hqOperator :
      Tendsto (fun N ↦ operatorPolynomialEval (q N) A) atTop (nhds R) := by
    exact (cauchySeq_operatorPolynomialEval_of_tendstoUniformlyOn A q
      (fun z ↦ (z - a)⁻¹) hq).tendsto_limUnder
  let d : Polynomial ℂ := Polynomial.X - Polynomial.C a
  have hlinear : TendstoUniformlyOn
      (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z d) (fun z ↦ z - a) atTop
      (closedOperatorNumericalRange A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ z _ ↦ by
      simp [d, hepsilon]
  have hreciprocalContinuous :
      ContinuousOn (fun z : ℂ ↦ (z - a)⁻¹) (closedOperatorNumericalRange A) :=
    ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
      (fun z hz ↦ sub_ne_zero.mpr fun hza ↦ haRange (hza ▸ hz))
  have hlinearContinuous :
      ContinuousOn (fun z : ℂ ↦ z - a) (closedOperatorNumericalRange A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hproductLocal :
      TendstoLocallyUniformlyOn
        ((fun N z ↦ Polynomial.eval z (q N)) *
          (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z d))
        ((fun z ↦ (z - a)⁻¹) * (fun z ↦ z - a)) atTop
        (closedOperatorNumericalRange A) :=
    hq.tendstoLocallyUniformlyOn.mul₀ hlinear.tendstoLocallyUniformlyOn
      hreciprocalContinuous hlinearContinuous
  have hproductUniform :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (closedOperatorNumericalRange_isCompact A)).mp hproductLocal
  have hproduct : TendstoUniformlyOn
      (fun N z ↦ Polynomial.eval z (q N * d)) (fun z ↦ Polynomial.eval z 1) atTop
      (closedOperatorNumericalRange A) := by
    have hright := hproductUniform.congr_right (fun z hz ↦ by
      simp only [Pi.mul_apply]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr fun hza ↦ haRange (hza ▸ hz)))
    simpa [Polynomial.eval_mul] using hright
  have hproductOperator :=
    tendsto_operatorPolynomialEval_of_tendstoUniformlyOn_polynomial A
      (fun N ↦ q N * d) 1 hproduct
  let D : H →L[ℂ] H := operatorPolynomialEval d A
  have hrightLimit :
      Tendsto (fun N ↦ operatorPolynomialEval (q N * d) A) atTop
        (nhds (R * D)) := by
    convert hqOperator.mul_const D using 1
    all_goals simp [D, operatorPolynomialEval]
  have hleftLimit :
      Tendsto (fun N ↦ operatorPolynomialEval (q N * d) A) atTop
        (nhds (D * R)) := by
    convert hqOperator.const_mul D using 1
    funext N
    change Polynomial.aeval A (q N * d) =
      Polynomial.aeval A d * Polynomial.aeval A (q N)
    rw [show q N * d = d * q N by exact mul_comm _ _, map_mul]
  have hRright : R * D = 1 := by
    have hlimits := tendsto_nhds_unique hrightLimit hproductOperator
    simpa [operatorPolynomialEval] using hlimits
  have hRleft : D * R = 1 := by
    have hlimits := tendsto_nhds_unique hleftLimit hproductOperator
    simpa [operatorPolynomialEval] using hlimits
  let u : (H →L[ℂ] H)ˣ :=
    { val := D
      inv := R
      val_inv := hRleft
      inv_val := hRright }
  have hDunit : IsUnit D := ⟨u, rfl⟩
  have hscalarSubUnit : IsUnit (algebraMap ℂ (H →L[ℂ] H) a - A) := by
    simpa [D, d, operatorPolynomialEval] using hDunit.neg
  exact (spectrum.notMem_iff.mpr hscalarSubUnit) haSpectrum

/-- Pole-freeness on the closed numerical range makes the reduced denominator invertible in the
bounded-operator algebra. -/
theorem operatorPolynomialEval_denom_isUnit_of_rationalPoleFreeOn
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    IsUnit (operatorPolynomialEval r.denom A) := by
  rw [← spectrum.zero_notMem_iff ℂ]
  rw [operatorPolynomialEval, spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hzero⟩
  exact (rationalPoleFreeOn_iff r (closedOperatorNumericalRange A)).mp hfree z
    (spectrum_subset_closedOperatorNumericalRange A hz) hzero

/-- The approximation-based value is the standard reduced numerator-times-inverse-denominator
rational functional calculus. -/
theorem operatorRationalEval_eq_num_mul_inverse_denom
    (A : H →L[ℂ] H) (r : RatFunc ℂ)
    (hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A)) :
    operatorRationalEval r A =
      operatorPolynomialEval r.num A * Ring.inverse (operatorPolynomialEval r.denom A) := by
  have hq := operatorRationalApproximants_tendstoUniformlyOn A r hfree
  have hdenom : TendstoUniformlyOn
      (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom)
      (fun z ↦ Polynomial.eval z r.denom) atTop (closedOperatorNumericalRange A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ _ _ ↦ by simpa using hepsilon
  have hproductLocal : TendstoLocallyUniformlyOn
      ((fun N z ↦ Polynomial.eval z (operatorRationalApproximants A r N)) *
        (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom))
      ((rationalScalarEval r) * (fun z ↦ Polynomial.eval z r.denom)) atTop
      (closedOperatorNumericalRange A) :=
    hq.tendstoLocallyUniformlyOn.mul₀ hdenom.tendstoLocallyUniformlyOn
      (continuousOn_rationalScalarEval r (closedOperatorNumericalRange A) hfree)
      r.denom.continuous.continuousOn
  have hproductUniform :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (closedOperatorNumericalRange_isCompact A)).mp hproductLocal
  have hproduct : TendstoUniformlyOn
      (fun N z ↦ Polynomial.eval z (operatorRationalApproximants A r N * r.denom))
      (fun z ↦ Polynomial.eval z r.num) atTop (closedOperatorNumericalRange A) := by
    have hright : TendstoUniformlyOn
        ((fun N z ↦ Polynomial.eval z (operatorRationalApproximants A r N)) *
          (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z r.denom))
        (fun z ↦ Polynomial.eval z r.num) atTop (closedOperatorNumericalRange A) :=
      hproductUniform.congr_right (fun z hz ↦ by
        simp only [Pi.mul_apply]
        rw [rationalScalarEval]
        exact div_mul_cancel₀ _
          ((rationalPoleFreeOn_iff r (closedOperatorNumericalRange A)).mp hfree z hz))
    simpa [Polynomial.eval_mul] using hright
  have hproductOperator :=
    tendsto_operatorPolynomialEval_of_tendstoUniformlyOn_polynomial A
      (fun N ↦ operatorRationalApproximants A r N * r.denom) r.num hproduct
  have hrightLimit :
      Tendsto
        (fun N ↦ operatorPolynomialEval (operatorRationalApproximants A r N * r.denom) A)
        atTop
        (nhds (operatorRationalEval r A * operatorPolynomialEval r.denom A)) := by
    convert (operatorRationalApproximants_tendsto A r hfree).mul_const
      (operatorPolynomialEval r.denom A) using 1
    funext N
    simp [operatorPolynomialEval]
  have hmul :
      operatorRationalEval r A * operatorPolynomialEval r.denom A =
        operatorPolynomialEval r.num A :=
    tendsto_nhds_unique hrightLimit hproductOperator
  exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _
    (operatorPolynomialEval_denom_isUnit_of_rationalPoleFreeOn A r hfree)).2 hmul

/-- Quantified form of the Hilbert-space rational spectral-set conclusion. -/
def HilbertRationalSpectralSetStatement : Prop :=
  (∀ A : H →L[ℂ] H, spectrum ℂ A ⊆ closedOperatorNumericalRange A) ∧
    ∀ (A : H →L[ℂ] H) (r : RatFunc ℂ),
      RationalPoleFreeOn r (closedOperatorNumericalRange A) →
        ‖operatorPolynomialEval r.num A *
            Ring.inverse (operatorPolynomialEval r.denom A)‖ ≤
          2 * supRationalModulusOnClosedOperatorNumericalRange A r

theorem hilbertSpaceRationalSpectralSet : HilbertRationalSpectralSetStatement (H := H) :=
  ⟨spectrum_subset_closedOperatorNumericalRange, fun A r hfree ↦ by
    rw [← operatorRationalEval_eq_num_mul_inverse_denom A r hfree]
    exact hilbertSpaceRationalCrouzeix A r hfree⟩

/-- The manuscript's complete Hilbert-space spectral-set consequence for one
bounded operator: compactness, spectral containment, and the rational constant-two bound. -/
def ClosedOperatorNumericalRangeIsTwoSpectralSet (A : H →L[ℂ] H) : Prop :=
  IsCompact (closedOperatorNumericalRange A) ∧
    spectrum ℂ A ⊆ closedOperatorNumericalRange A ∧
      ∀ (r : RatFunc ℂ),
        RationalPoleFreeOn r (closedOperatorNumericalRange A) →
          ‖operatorPolynomialEval r.num A *
              Ring.inverse (operatorPolynomialEval r.denom A)‖ ≤
            2 * supRationalModulusOnClosedOperatorNumericalRange A r

/-- The closed numerical range of every bounded operator on a nonzero complex
Hilbert space is a `2`-spectral set. -/
theorem closedOperatorNumericalRange_isTwoSpectralSet (A : H →L[ℂ] H) :
    ClosedOperatorNumericalRangeIsTwoSpectralSet A :=
  ⟨closedOperatorNumericalRange_isCompact A,
    spectrum_subset_closedOperatorNumericalRange A,
    fun r hfree ↦ by
      rw [← operatorRationalEval_eq_num_mul_inverse_denom A r hfree]
      exact hilbertSpaceRationalCrouzeix A r hfree⟩

/-- The approximation-based rational calculus agrees with the polynomial calculus on embedded
polynomials. -/
theorem operatorRationalEval_algebraMap_polynomial
    (A : H →L[ℂ] H) (p : Polynomial ℂ) :
    operatorRationalEval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) A =
      operatorPolynomialEval p A := by
  let r : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) p
  have hfree : RationalPoleFreeOn r (closedOperatorNumericalRange A) := by
    rw [rationalPoleFreeOn_iff]
    intro z hz
    simp [r]
  have hscalar (z : ℂ) : rationalScalarEval r z = Polynomial.eval z p := by
    simp [r, rationalScalarEval]
  have huniform : TendstoUniformlyOn
      (fun _ : ℕ ↦ fun z ↦ Polynomial.eval z p) (rationalScalarEval r) atTop
      (closedOperatorNumericalRange A) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall fun _ z _ ↦ by simp [hscalar z, hepsilon]
  have hlim := tendsto_operatorPolynomialEval_of_rational_approximation A r hfree
    (fun _ ↦ p) huniform
  have hconst : Tendsto (fun _ : ℕ ↦ operatorPolynomialEval p A) atTop
      (nhds (operatorPolynomialEval p A)) := tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

end RationalApproximation

end CrouzeixConjecture
