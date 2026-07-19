module

public import CrouzeixConjecture.DoubleLayerBoundary
public import CrouzeixConjecture.CompletionDiagonalization
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ComplexOrder Interval Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- If `z` is not on the real segment from `c` to `w`, the quotient comparing the
two translated points avoids the closed negative real axis. -/
theorem sub_div_sub_mem_slitPlane_of_not_mem_segment
    {c w z : ℂ} (hz : z ∉ segment ℝ c w) :
    (z - w) / (z - c) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_not_le_zero]
  intro hquotient
  have hzc : z - c ≠ 0 := by
    intro h
    apply hz
    have : z = c := sub_eq_zero.mp h
    simpa only [this] using left_mem_segment ℝ c w
  let a : ℝ := ‖-((z - w) / (z - c))‖
  have ha : 0 ≤ a := norm_nonneg _
  have hreal : -((z - w) / (z - c)) = (a : ℂ) := by
    exact Complex.eq_coe_norm_of_nonneg (neg_nonneg.mpr hquotient)
  have hratio : (z - w) / (z - c) = -(a : ℂ) := by
    have := congrArg Neg.neg hreal
    simpa only [neg_neg] using this
  have hmul : z - w = -(a : ℂ) * (z - c) :=
    (div_eq_iff hzc).mp hratio
  have hw : w = z + (a : ℂ) * (z - c) := by
    calc
      w = z - (z - w) := by ring
      _ = z - (-(a : ℂ) * (z - c)) := by rw [hmul]
      _ = z + (a : ℂ) * (z - c) := by ring
  apply hz
  refine ⟨a / (1 + a), 1 / (1 + a), by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · simp only [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr
      (by positivity : (1 + a : ℝ) ≠ 0)]
    rw [hw]
    ring

/-- Pointwise divided-difference decomposition used in the polynomial Cauchy formula. -/
theorem polynomialEval_mul_div_sub_eq
    (q : Polynomial ℂ) {z w v : ℂ} (hzw : z ≠ w) :
    Polynomial.eval z q * (v / (z - w)) =
      Polynomial.eval w q * (v / (z - w)) +
        Polynomial.eval z (q /ₘ (Polynomial.X - Polynomial.C w)) * v := by
  have hpoly := Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic q w
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hpoly
  have heval := congrArg (Polynomial.eval z) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at heval
  have hrewrite : Polynomial.eval z q = Polynomial.eval w q +
      (z - w) * Polynomial.eval z
        (q /ₘ (Polynomial.X - Polynomial.C w)) := by
    rw [heval]
    ring
  rw [hrewrite]
  field_simp [sub_ne_zero.mpr hzw]

/-- The scalar resolvent of a simply diagonalized matrix is the conjugate of the
entrywise diagonal resolvent. -/
theorem doubleLayerResolvent_eq_innerConjugation_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) {sigma : ℂ}
    (hne : ∀ i, sigma ≠ hB.eigenvalues i) :
    doubleLayerResolvent B sigma =
      innerConjugation hB.changeBasis
        (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) := by
  let e := innerConjugation hB.changeBasis
  let diagonalEigenvalues := Matrix.diagonal hB.eigenvalues
  have hscalar : e (sigma • (1 : SquareMatrix n)) = sigma • 1 := by
    exact map_smul e sigma (1 : SquareMatrix n) |>.trans (by rw [map_one])
  have hdiagonal : sigma • (1 : SquareMatrix n) - diagonalEigenvalues =
      Matrix.diagonal (fun i ↦ sigma - hB.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalEigenvalues]
    · simp [diagonalEigenvalues, Matrix.diagonal, hij]
  have hleft :
      Matrix.diagonal (fun i ↦ (sigma - hB.eigenvalues i)⁻¹) *
          (sigma • (1 : SquareMatrix n) - diagonalEigenvalues) = 1 := by
    rw [hdiagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, Matrix.diagonal,
        sub_ne_zero.mpr (hne i)]
    · simp [Matrix.mul_apply, Matrix.diagonal, hij]
  unfold doubleLayerResolvent
  change (sigma • (1 : SquareMatrix n) - B)⁻¹ =
    e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹)
  conv_lhs => rw [show B = e diagonalEigenvalues by
    simpa [e, diagonalEigenvalues] using hB.eq_conjugate]
  apply Matrix.inv_eq_left_inv
  change e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) *
      (sigma • (1 : SquareMatrix n) - e diagonalEigenvalues) = 1
  calc
    e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) *
          (sigma • (1 : SquareMatrix n) - e diagonalEigenvalues) =
        e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) *
          (e (sigma • (1 : SquareMatrix n)) - e diagonalEigenvalues) := by
      rw [hscalar]
    _ = e (Matrix.diagonal (fun i ↦ (sigma - hB.eigenvalues i)⁻¹) *
          (sigma • (1 : SquareMatrix n) - diagonalEigenvalues)) := by
      rw [map_mul, map_sub]
    _ = 1 := by rw [hleft, map_one]

/-- Conjugation by a unit as a continuous complex-linear map on the finite-dimensional
matrix space. -/
def innerConjugationCLM
    {n : Type*} [Fintype n] [DecidableEq n]
    (u : (SquareMatrix n)ˣ) : SquareMatrix n →L[ℂ] SquareMatrix n :=
  ⟨(innerConjugation u).toLinearMap,
    (innerConjugation u).toLinearMap.continuous_of_finiteDimensional⟩

/-- Evaluation of a fixed matrix entry as a continuous complex-linear functional. -/
def matrixEntryCLM
    {n : Type*} [Fintype n] [DecidableEq n]
    (i j : n) : SquareMatrix n →L[ℂ] ℂ :=
  ⟨{ toFun := fun A ↦ A i j
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl },
    LinearMap.continuous_of_finiteDimensional _⟩

/-- Pointwise diagonal form of the polynomial Cauchy-resolvent integrand. -/
theorem polynomialResolventIntegrand_eq_innerConjugation_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : SquareMatrix n} (hB : SimpleDiagonalization B)
    (q : Polynomial ℂ) {sigma tangent : ℂ}
    (hne : ∀ i, sigma ≠ hB.eigenvalues i) :
    Polynomial.eval sigma q •
        (tangent • doubleLayerResolvent B sigma) =
      innerConjugation hB.changeBasis
        (Matrix.diagonal fun i ↦
          Polynomial.eval sigma q *
            (tangent / (sigma - hB.eigenvalues i))) := by
  rw [doubleLayerResolvent_eq_innerConjugation_diagonal hB hne]
  let e := innerConjugation hB.changeBasis
  change Polynomial.eval sigma q •
      (tangent • e (Matrix.diagonal fun i ↦
        (sigma - hB.eigenvalues i)⁻¹)) = _
  rw [smul_smul]
  calc
    (Polynomial.eval sigma q * tangent) •
          e (Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) =
        e ((Polynomial.eval sigma q * tangent) •
          Matrix.diagonal fun i ↦ (sigma - hB.eigenvalues i)⁻¹) := by
      exact (map_smul e _ _).symm
    _ = e (Matrix.diagonal fun i ↦ Polynomial.eval sigma q *
          (tangent / (sigma - hB.eigenvalues i))) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [div_eq_mul_inv]
        ring
      · simp [Matrix.diagonal, hij]

/-- The parameter length of one positively oriented traversal. -/
def contourPeriod : ℝ := 2 * Real.pi

theorem contourPeriod_pos : 0 < contourPeriod := by
  unfold contourPeriod
  positivity

theorem contourPeriod_nonneg : 0 ≤ contourPeriod := contourPeriod_pos.le

theorem cauchyNormalization_mul_period_I :
    (-Complex.I * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)) *
      ((contourPeriod : ℂ) * Complex.I) = 1 := by
  unfold contourPeriod
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The compact parameter interval for one boundary traversal. -/
abbrev ContourParameter := Set.Icc (0 : ℝ) contourPeriod

/-- Lebesgue measure restricted to one traversal and pulled back to the interval subtype. -/
def contourParameterMeasure : Measure ContourParameter :=
  Measure.comap Subtype.val (volume.restrict (Set.Icc (0 : ℝ) contourPeriod))

noncomputable instance contourParameterMeasure_isFinite :
    IsFiniteMeasure contourParameterMeasure := by
  unfold contourParameterMeasure
  infer_instance

/-- Integration over the compact parameter subtype agrees with the usual oriented interval
integral from `0` to `2π`. -/
theorem integral_contourParameter_eq_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) :
    (∫ t : ContourParameter, f t.1 ∂contourParameterMeasure) =
      ∫ t in (0 : ℝ)..contourPeriod, f t := by
  rw [contourParameterMeasure,
    integral_subtype_comap measurableSet_Icc]
  calc
    (∫ t in Set.Icc (0 : ℝ) contourPeriod, f t
        ∂volume.restrict (Set.Icc (0 : ℝ) contourPeriod)) =
        ∫ t in Set.Icc (0 : ℝ) contourPeriod, f t ∂volume := by
      rw [Measure.restrict_restrict measurableSet_Icc, Set.inter_self]
    _ = ∫ t in Set.Ioc (0 : ℝ) contourPeriod, f t ∂volume :=
      integral_Icc_eq_integral_Ioc
    _ = ∫ t in (0 : ℝ)..contourPeriod, f t :=
      (intervalIntegral.integral_of_le contourPeriod_nonneg).symm

/-- A positive `C¹` periodic radial function.  The explicit continuous derivative is retained
because it is exactly what the arclength speed and the direct Cauchy proof consume. -/
structure PositivePeriodicRadialData where
  radius : ℝ → ℝ
  radiusDeriv : ℝ → ℝ
  radius_pos : ∀ t, 0 < radius t
  radius_hasDerivAt : ∀ t, HasDerivAt radius (radiusDeriv t) t
  radiusDeriv_continuous : Continuous radiusDeriv
  radius_periodic : Function.Periodic radius contourPeriod

namespace PositivePeriodicRadialData

theorem radius_continuous (R : PositivePeriodicRadialData) : Continuous R.radius := by
  exact continuous_iff_continuousAt.2 fun t ↦ (R.radius_hasDerivAt t).continuousAt

/-- The radial contour centered at `c`. -/
def point (R : PositivePeriodicRadialData) (c : ℂ) (t : ℝ) : ℂ :=
  c + (R.radius t : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

/-- The explicit tangent of the radial contour. -/
def tangent (R : PositivePeriodicRadialData) (t : ℝ) : ℂ :=
  ((R.radiusDeriv t : ℂ) + Complex.I * (R.radius t : ℂ)) *
    Complex.exp ((t : ℂ) * Complex.I)

theorem point_hasDerivAt (R : PositivePeriodicRadialData) (c : ℂ) (t : ℝ) :
    HasDerivAt (R.point c) (R.tangent t) t := by
  have hradius : HasDerivAt (fun s : ℝ ↦ (R.radius s : ℂ))
      (R.radiusDeriv t : ℂ) t :=
    (R.radius_hasDerivAt t).ofReal_comp
  have hphase : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * Complex.I)
      Complex.I t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      Complex.ofRealCLM.hasDerivAt.mul_const Complex.I
  have hexp := hphase.cexp
  convert (hradius.mul hexp).const_add c using 1
  unfold tangent
  ring

theorem point_continuous (R : PositivePeriodicRadialData) (c : ℂ) :
    Continuous (R.point c) :=
  continuous_iff_continuousAt.2 fun t ↦ (R.point_hasDerivAt c t).continuousAt

theorem tangent_continuous (R : PositivePeriodicRadialData) :
    Continuous R.tangent := by
  apply Continuous.mul
  · exact (Complex.continuous_ofReal.comp R.radiusDeriv_continuous).add
      (continuous_const.mul (Complex.continuous_ofReal.comp R.radius_continuous))
  · exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)

theorem point_periodic_endpoint (R : PositivePeriodicRadialData) (c : ℂ) :
    R.point c contourPeriod = R.point c 0 := by
  have hradius : R.radius contourPeriod = R.radius 0 := by
    simpa using R.radius_periodic 0
  have hphase : Complex.exp ((contourPeriod : ℂ) * Complex.I) = 1 := by
    simpa [contourPeriod, mul_assoc] using Complex.exp_two_pi_mul_I
  rw [point, point, hradius]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, hphase]

theorem compact_range_on_contourPeriod (R : PositivePeriodicRadialData) (c : ℂ) :
    IsCompact (R.point c '' Set.Icc (0 : ℝ) contourPeriod) :=
  isCompact_Icc.image (R.point_continuous c)

/-- An open convex domain whose boundary traversal is the radial contour.  The condition retained
here is precisely the one used by the direct Cauchy proof: the center is inside, while every
point of the traversal is outside the open domain. -/
structure RadialConvexDomain (R : PositivePeriodicRadialData) (c : ℂ) (Omega : Set ℂ) : Prop where
  isOpen_domain : IsOpen Omega
  convex_domain : Convex ℝ Omega
  center_mem : c ∈ Omega
  point_not_mem : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod, R.point c t ∉ Omega

namespace RadialConvexDomain

theorem point_ne_interior (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) contourPeriod) {w : ℂ} (hw : w ∈ Omega) :
    R.point c t ≠ w := by
  intro h
  exact D.point_not_mem t ht (h ▸ hw)

theorem comparisonRatio_mem_slitPlane (R : PositivePeriodicRadialData)
    (c : ℂ) {Omega : Set ℂ} (D : RadialConvexDomain R c Omega)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) contourPeriod)
    {w : ℂ} (hw : w ∈ Omega) :
    (R.point c t - w) / (R.point c t - c) ∈ Complex.slitPlane := by
  apply sub_div_sub_mem_slitPlane_of_not_mem_segment
  intro hsegment
  exact D.point_not_mem t ht
    (D.convex_domain.segment_subset D.center_mem hw hsegment)

/-- The logarithm of the comparison quotient has derivative equal to the difference of the
two winding integrands.  Convexity is exactly what keeps the quotient in the slit plane. -/
theorem log_comparisonRatio_hasDerivAt (R : PositivePeriodicRadialData)
    (c : ℂ) {Omega : Set ℂ} (D : RadialConvexDomain R c Omega)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) contourPeriod)
    {w : ℂ} (hw : w ∈ Omega) :
    HasDerivAt
      (fun s : ℝ ↦ Complex.log
        ((R.point c s - w) / (R.point c s - c)))
      (R.tangent t / (R.point c t - w) -
        R.tangent t / (R.point c t - c)) t := by
  have hwne : R.point c t - w ≠ 0 := sub_ne_zero.mpr
    (RadialConvexDomain.point_ne_interior R c D ht hw)
  have hcne : R.point c t - c ≠ 0 :=
    sub_ne_zero.mpr
      (RadialConvexDomain.point_ne_interior R c D ht D.center_mem)
  have hratio := ((R.point_hasDerivAt c t).sub_const w).fun_div
    ((R.point_hasDerivAt c t).sub_const c) hcne
  have hlog := hratio.clog_real
    (RadialConvexDomain.comparisonRatio_mem_slitPlane R c D ht hw)
  convert hlog using 1
  field_simp [hwne, hcne]

end RadialConvexDomain

/-- A supported radial contour with the manuscript's positive-orientation identity
`gamma' = i * normal * speed`. -/
structure OrientedRadialConvexBoundary
    (R : PositivePeriodicRadialData) (c : ℂ) (Omega : Set ℂ) where
  domain : RadialConvexDomain R c Omega
  normal : C(ℝ, ℂ)
  speed : C(ℝ, ℝ)
  speed_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod, 0 ≤ speed t
  supported : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
    OutwardBoundarySupport Omega (R.point c t) (normal t)
  tangent_eq : ∀ t ∈ Set.Icc (0 : ℝ) contourPeriod,
    R.tangent t = Complex.I * normal t * speed t

namespace OrientedRadialConvexBoundary

/-- The radial contour, outward normal, and speed restricted to the compact parameter subtype. -/
def parametricBoundary
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega) :
    ParametricConvexBoundary (i := ContourParameter) Omega where
  point :=
    ⟨fun x ↦ R.point c x.1,
      (R.point_continuous c).comp continuous_subtype_val⟩
  normal :=
    ⟨fun x ↦ G.normal x.1,
      G.normal.continuous.comp continuous_subtype_val⟩
  speed :=
    ⟨fun x ↦ G.speed x.1,
      G.speed.continuous.comp continuous_subtype_val⟩
  speed_nonneg x := G.speed_nonneg x.1 x.2
  supported x := G.supported x.1 x.2

@[simp]
theorem parametricBoundary_point
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega) (x : ContourParameter) :
    (G.parametricBoundary R c).point x = R.point c x.1 := rfl

@[simp]
theorem parametricBoundary_normal
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega) (x : ContourParameter) :
    (G.parametricBoundary R c).normal x = G.normal x.1 := rfl

@[simp]
theorem parametricBoundary_speed
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega) (x : ContourParameter) :
    (G.parametricBoundary R c).speed x = G.speed x.1 := rfl

/-- Positive orientation converts the normal-times-arclength analytic density into the
standard `d sigma /(2πi)` Cauchy integrand. -/
theorem parametricBoundaryFirstPart_eq_cauchyIntegrand
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (B : SquareMatrix n) (x : ContourParameter) :
    parametricBoundaryFirstPart (G.parametricBoundary R c) B x =
      (-Complex.I * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)) •
        (R.tangent x.1 •
          parametricBoundaryResolvent (G.parametricBoundary R c) B x) := by
  have htangent := G.tangent_eq x.1 x.2
  ext i j
  simp [parametricBoundaryFirstPart, Complex.real_smul, htangent]
  ring_nf
  rw [Complex.I_sq]
  ring

end OrientedRadialConvexBoundary

theorem point_sub_center_ne_zero (R : PositivePeriodicRadialData)
    (c : ℂ) (t : ℝ) : R.point c t - c ≠ 0 := by
  rw [point, add_sub_cancel_left]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (R.radius_pos t).ne')
    (Complex.exp_ne_zero _)

/-- Algebraic logarithmic-derivative identity for the radial winding calculation. -/
theorem tangent_div_point_sub_center (R : PositivePeriodicRadialData)
    (c : ℂ) (t : ℝ) :
    R.tangent t / (R.point c t - c) =
      ((R.radiusDeriv t / R.radius t : ℝ) : ℂ) + Complex.I := by
  have hradius : (R.radius t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (R.radius_pos t).ne'
  have hexp : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hcancel : (R.radius t : ℂ) *
      ((R.radiusDeriv t / R.radius t : ℝ) : ℂ) =
      (R.radiusDeriv t : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [(R.radius_pos t).ne']
  rw [point, add_sub_cancel_left, tangent]
  field_simp [hradius, hexp]
  rw [mul_add, hcancel]
  ring

theorem intervalIntegrable_radiusDeriv_div_radius
    (R : PositivePeriodicRadialData) :
    IntervalIntegrable (fun t ↦ R.radiusDeriv t / R.radius t)
      volume 0 contourPeriod := by
  apply Continuous.intervalIntegrable
  exact R.radiusDeriv_continuous.div R.radius_continuous
    (fun t ↦ (R.radius_pos t).ne')

/-- The real logarithmic derivative has zero integral over one period. -/
theorem integral_radiusDeriv_div_radius_eq_zero
    (R : PositivePeriodicRadialData) :
    (∫ t in (0 : ℝ)..contourPeriod,
      R.radiusDeriv t / R.radius t) = 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
      HasDerivAt (fun s ↦ Real.log (R.radius s))
        (R.radiusDeriv t / R.radius t) t := by
    intro t _
    exact (R.radius_hasDerivAt t).log (R.radius_pos t).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    R.intervalIntegrable_radiusDeriv_div_radius]
  have hperiod : R.radius contourPeriod = R.radius 0 := by
    simpa using R.radius_periodic 0
  rw [hperiod]
  simp

/-- The positively oriented radial contour winds once around its center. -/
theorem integral_tangent_div_point_sub_center
    (R : PositivePeriodicRadialData) (c : ℂ) :
    (∫ t in (0 : ℝ)..contourPeriod,
      R.tangent t / (R.point c t - c)) =
      (contourPeriod : ℂ) * Complex.I := by
  have hreal : IntervalIntegrable
      (fun t ↦ ((R.radiusDeriv t / R.radius t : ℝ) : ℂ))
      volume 0 contourPeriod := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp
      (R.radiusDeriv_continuous.div R.radius_continuous
        (fun t ↦ (R.radius_pos t).ne'))
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ Complex.I)
      volume 0 contourPeriod := intervalIntegrable_const
  rw [intervalIntegral.integral_congr
    (fun t _ ↦ R.tangent_div_point_sub_center c t)]
  rw [intervalIntegral.integral_add hreal hconst,
    intervalIntegral.integral_ofReal,
    R.integral_radiusDeriv_div_radius_eq_zero,
    Complex.ofReal_zero, intervalIntegral.integral_const]
  simp

theorem intervalIntegrable_polynomialEval_mul_tangent
    (R : PositivePeriodicRadialData) (c : ℂ) (q : Polynomial ℂ) :
    IntervalIntegrable
      (fun t ↦ Polynomial.eval (R.point c t) q * R.tangent t)
      volume 0 contourPeriod := by
  apply Continuous.intervalIntegrable
  exact (q.continuous.comp (R.point_continuous c)).mul R.tangent_continuous

/-- The integral of a polynomial one-form over the closed radial contour is zero. -/
theorem integral_polynomialEval_mul_tangent_eq_zero
    (R : PositivePeriodicRadialData) (c : ℂ) (q : Polynomial ℂ) :
    (∫ t in (0 : ℝ)..contourPeriod,
      Polynomial.eval (R.point c t) q * R.tangent t) = 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, add_mul]
      rw [intervalIntegral.integral_add
        (R.intervalIntegrable_polynomialEval_mul_tangent c p)
        (R.intervalIntegrable_polynomialEval_mul_tangent c q), hp, hq, add_zero]
  | monomial n a =>
      have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
          HasDerivAt
            (fun s : ℝ ↦
              (a / ((n + 1 : ℕ) : ℂ)) * (R.point c s) ^ (n + 1))
            (Polynomial.eval (R.point c t) (Polynomial.monomial n a) *
              R.tangent t) t := by
        intro t _
        have hpow := ((R.point_hasDerivAt c t).fun_pow (n + 1)).const_mul
          (a / ((n + 1 : ℕ) : ℂ))
        convert hpow using 1
        simp only [Polynomial.eval_monomial, Nat.add_sub_cancel, Nat.cast_add,
          Nat.cast_one]
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (R.intervalIntegrable_polynomialEval_mul_tangent c
          (Polynomial.monomial n a))]
      rw [R.point_periodic_endpoint c]
      simp

namespace RadialConvexDomain

theorem intervalIntegrable_tangent_div_point_sub
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega) {w : ℂ} (hw : w ∈ Omega) :
    IntervalIntegrable
      (fun t ↦ R.tangent t / (R.point c t - w))
      volume 0 contourPeriod := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div R.tangent_continuous.continuousOn
    ((R.point_continuous c).continuousOn.sub continuousOn_const)
  intro t ht
  apply sub_ne_zero.mpr
  exact RadialConvexDomain.point_ne_interior R c D
    (by simpa only [uIcc_of_le contourPeriod_nonneg] using ht) hw

/-- The winding integral is constant throughout the open convex domain.  This proof uses the
principal logarithm only on a quotient that convexity keeps away from its branch cut. -/
theorem integral_tangent_div_point_sub_eq_center
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega) {w : ℂ} (hw : w ∈ Omega) :
    (∫ t in (0 : ℝ)..contourPeriod,
      R.tangent t / (R.point c t - w)) =
      ∫ t in (0 : ℝ)..contourPeriod,
        R.tangent t / (R.point c t - c) := by
  have hwint := D.intervalIntegrable_tangent_div_point_sub R c hw
  have hcint := D.intervalIntegrable_tangent_div_point_sub R c D.center_mem
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
      HasDerivAt
        (fun s : ℝ ↦ Complex.log
          ((R.point c s - w) / (R.point c s - c)))
        (R.tangent t / (R.point c t - w) -
          R.tangent t / (R.point c t - c)) t := by
    intro t ht
    exact RadialConvexDomain.log_comparisonRatio_hasDerivAt R c D
      (by simpa only [uIcc_of_le contourPeriod_nonneg] using ht) hw
  have hzero :
      (∫ t in (0 : ℝ)..contourPeriod,
        (R.tangent t / (R.point c t - w) -
          R.tangent t / (R.point c t - c))) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hwint.sub hcint)]
    rw [R.point_periodic_endpoint c]
    simp
  rw [intervalIntegral.integral_sub hwint hcint] at hzero
  exact sub_eq_zero.mp hzero

/-- Every point of the bounded open convex domain has winding number one with respect to the
positively oriented radial contour. -/
theorem integral_tangent_div_point_sub
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega) {w : ℂ} (hw : w ∈ Omega) :
    (∫ t in (0 : ℝ)..contourPeriod,
      R.tangent t / (R.point c t - w)) =
      (contourPeriod : ℂ) * Complex.I := by
  rw [D.integral_tangent_div_point_sub_eq_center R c hw]
  exact R.integral_tangent_div_point_sub_center c

/-- Scalar polynomial Cauchy formula on the radial boundary. -/
theorem integral_polynomial_cauchy
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega) {w : ℂ} (hw : w ∈ Omega)
    (q : Polynomial ℂ) :
    (∫ t in (0 : ℝ)..contourPeriod,
      Polynomial.eval (R.point c t) q *
        (R.tangent t / (R.point c t - w))) =
      Polynomial.eval w q * ((contourPeriod : ℂ) * Complex.I) := by
  have hwind := D.intervalIntegrable_tangent_div_point_sub R c hw
  have hquotient := R.intervalIntegrable_polynomialEval_mul_tangent c
    (q /ₘ (Polynomial.X - Polynomial.C w))
  rw [intervalIntegral.integral_congr (fun t ht ↦
    polynomialEval_mul_div_sub_eq q
      (RadialConvexDomain.point_ne_interior R c D
        (by
          simpa only [uIcc_of_le contourPeriod_nonneg] using ht)
        hw))]
  rw [intervalIntegral.integral_add
    (hwind.const_mul (Polynomial.eval w q)) hquotient]
  rw [intervalIntegral.integral_const_mul,
    D.integral_tangent_div_point_sub R c hw,
    R.integral_polynomialEval_mul_tangent_eq_zero c
      (q /ₘ (Polynomial.X - Polynomial.C w)), add_zero]

/-- Matrix polynomial Cauchy formula for the manuscript's simple-spectrum stage, proved by
the explicit simple diagonalization and the scalar formula above. -/
theorem integral_polynomial_cauchy_resolvent_of_simpleDiagonalization
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (D : RadialConvexDomain R c Omega)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) (q : Polynomial ℂ) :
    (∫ t in (0 : ℝ)..contourPeriod,
      Polynomial.eval (R.point c t) q •
        (R.tangent t • doubleLayerResolvent B (R.point c t))) =
      ((contourPeriod : ℂ) * Complex.I) • polynomialEval q B := by
  let e := innerConjugation hB.changeBasis
  let eCLM := innerConjugationCLM hB.changeBasis
  let F : ℝ → SquareMatrix n := fun t ↦
    Matrix.diagonal fun i ↦
      Polynomial.eval (R.point c t) q *
        (R.tangent t / (R.point c t - hB.eigenvalues i))
  have hlambda (i : n) : hB.eigenvalues i ∈ Omega :=
    hWB (matrixSpectrum_subset_numericalRange B
      (hB.eigenvalue_mem_matrixSpectrum i))
  have hscalarContinuous (i : n) : ContinuousOn
      (fun t : ℝ ↦ Polynomial.eval (R.point c t) q *
        (R.tangent t / (R.point c t - hB.eigenvalues i)))
      (Set.Icc (0 : ℝ) contourPeriod) := by
    apply ContinuousOn.mul
    · exact (q.continuous.comp (R.point_continuous c)).continuousOn
    · apply ContinuousOn.div R.tangent_continuous.continuousOn
        ((R.point_continuous c).continuousOn.sub continuousOn_const)
      intro t ht
      exact sub_ne_zero.mpr
        (RadialConvexDomain.point_ne_interior R c D ht (hlambda i))
  have hFcontinuous : ContinuousOn F (Set.Icc (0 : ℝ) contourPeriod) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa [F, Matrix.diagonal] using hscalarContinuous i
    · simpa [F, Matrix.diagonal, hij] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℂ))
          (Set.Icc (0 : ℝ) contourPeriod))
  have hFint : IntervalIntegrable F volume 0 contourPeriod :=
    hFcontinuous.intervalIntegrable_of_Icc contourPeriod_nonneg
  have hFintegral :
      (∫ t in (0 : ℝ)..contourPeriod, F t) =
        Matrix.diagonal (fun i ↦ Polynomial.eval (hB.eigenvalues i) q *
          ((contourPeriod : ℂ) * Complex.I)) := by
    ext i j
    change matrixEntryCLM i j (∫ t in (0 : ℝ)..contourPeriod, F t) = _
    rw [← (matrixEntryCLM i j).intervalIntegral_comp_comm hFint]
    by_cases hij : i = j
    · subst j
      simpa [F, matrixEntryCLM, Matrix.diagonal] using
        D.integral_polynomial_cauchy R c (hlambda i) q
    · simp [F, matrixEntryCLM, Matrix.diagonal, hij]
  have hintegrand : ∀ t ∈ Set.uIcc (0 : ℝ) contourPeriod,
      Polynomial.eval (R.point c t) q •
          (R.tangent t • doubleLayerResolvent B (R.point c t)) =
        eCLM (F t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) contourPeriod := by
      simpa only [uIcc_of_le contourPeriod_nonneg] using ht
    simpa [eCLM, innerConjugationCLM, F, e] using
      polynomialResolventIntegrand_eq_innerConjugation_diagonal hB q
        (fun i ↦ RadialConvexDomain.point_ne_interior R c D htIcc (hlambda i))
  have hpoly : polynomialEval q B =
      e (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) q) := by
    calc
      polynomialEval q B = polynomialEval q
          (e (Matrix.diagonal hB.eigenvalues)) :=
        congrArg (polynomialEval q) hB.eq_conjugate
      _ = e (polynomialEval q (Matrix.diagonal hB.eigenvalues)) :=
        Polynomial.aeval_algHom_apply e (Matrix.diagonal hB.eigenvalues) q
      _ = e (Matrix.diagonal fun i ↦
          Polynomial.eval (hB.eigenvalues i) q) := by
        rw [polynomialEval_diagonal]
  rw [intervalIntegral.integral_congr hintegrand,
    eCLM.intervalIntegral_comp_comm hFint]
  change e (∫ t in (0 : ℝ)..contourPeriod, F t) = _
  rw [hFintegral]
  calc
    e (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) q *
          ((contourPeriod : ℂ) * Complex.I)) =
        e (((contourPeriod : ℂ) * Complex.I) •
          Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) q) := by
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp
        ring
      · simp [Matrix.diagonal, hij]
    _ = ((contourPeriod : ℂ) * Complex.I) •
        e (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) q) :=
      map_smul e _ _
    _ = ((contourPeriod : ℂ) * Complex.I) • polynomialEval q B := by
      rw [hpoly]

end RadialConvexDomain

namespace OrientedRadialConvexBoundary

/-- The oriented radial boundary satisfies the exact matrix-valued polynomial Cauchy
formula for every simple-spectrum matrix whose numerical range lies in the domain. -/
theorem hasParametricPolynomialCauchyFormula_of_simpleDiagonalization
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    HasParametricPolynomialCauchyFormula
      (G.parametricBoundary R c) contourParameterMeasure B := by
  intro q
  let k : ℂ := -Complex.I * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)
  let f : ℝ → SquareMatrix n := fun t ↦
    k • (Polynomial.eval (R.point c t) q •
      (R.tangent t • doubleLayerResolvent B (R.point c t)))
  have hbase :=
    RadialConvexDomain.integral_polynomial_cauchy_resolvent_of_simpleDiagonalization
      R c G.domain B hB hWB q
  calc
    (∫ x, Polynomial.eval ((G.parametricBoundary R c).point x) q •
        parametricBoundaryFirstPart (G.parametricBoundary R c) B x
        ∂contourParameterMeasure) =
        ∫ x : ContourParameter, f x.1 ∂contourParameterMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change Polynomial.eval (R.point c x.1) q •
          parametricBoundaryFirstPart (G.parametricBoundary R c) B x = f x.1
        rw [G.parametricBoundaryFirstPart_eq_cauchyIntegrand R c B x]
        ext i j
        simp [f, k, parametricBoundaryResolvent, smul_smul]
        ring
    _ = ∫ t in (0 : ℝ)..contourPeriod, f t :=
      integral_contourParameter_eq_intervalIntegral f
    _ = k • (∫ t in (0 : ℝ)..contourPeriod,
        Polynomial.eval (R.point c t) q •
          (R.tangent t • doubleLayerResolvent B (R.point c t))) := by
      exact intervalIntegral.integral_smul k _
    _ = k • (((contourPeriod : ℂ) * Complex.I) • polynomialEval q B) := by
      rw [hbase]
    _ = polynomialEval q B := by
      rw [smul_smul, cauchyNormalization_mul_period_I, one_smul]

/-- The geometric oriented radial boundary therefore supplies the complete double-layer
provider required by the simple-spectrum perturbation argument. -/
theorem hasDoubleLayerCompletionProvider_of_simpleDiagonalization
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    HasDoubleLayerCompletionProvider B (closure Omega) := by
  exact hasDoubleLayerCompletionProvider_of_parametricBoundary
    (G.parametricBoundary R c) B hWB
    (G.hasParametricPolynomialCauchyFormula_of_simpleDiagonalization
      R c B hB hWB)

end OrientedRadialConvexBoundary

end PositivePeriodicRadialData

end CrouzeixConjecture
