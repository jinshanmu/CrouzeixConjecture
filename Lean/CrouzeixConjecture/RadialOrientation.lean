module

public import Mathlib.Analysis.InnerProductSpace.TwoDim

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace CrouzeixConjecture

attribute [local instance] Complex.finrank_real_complex_fact

/-- The real inner product on `ℂ` uses the convention that it is the real part of
`w * conj z`.  Keeping this bridge explicit prevents an accidental reversal of the
complex inner-product convention in the boundary-orientation argument. -/
theorem complexRealInner_eq_re_mul_conj (z w : ℂ) :
    ⟪z, w⟫_ℝ = (w * star z).re :=
  Complex.inner z w

/-- Multiplication of the first vector by `I` converts the real inner product into
the standard oriented area form. -/
theorem complexRealInner_I_mul_left (z w : ℂ) :
    ⟪Complex.I * z, w⟫_ℝ = Complex.orientation.areaForm z w := by
  simpa only [Complex.rightAngleRotation] using
    Complex.orientation.inner_rightAngleRotation_left z w

/-- Multiplication of the second vector by `I` gives the negative oriented area. -/
theorem complexRealInner_I_mul_right (z w : ℂ) :
    ⟪z, Complex.I * w⟫_ℝ = -Complex.orientation.areaForm z w := by
  simpa only [Complex.rightAngleRotation] using
    Complex.orientation.inner_rightAngleRotation_right z w

/-- Simultaneous multiplication by `I` preserves the real inner product. -/
theorem complexRealInner_I_mul_I_mul (z w : ℂ) :
    ⟪Complex.I * z, Complex.I * w⟫_ℝ = ⟪z, w⟫_ℝ := by
  simpa only [Complex.rightAngleRotation] using
    Complex.orientation.inner_comp_rightAngleRotation z w

/-- Rotating the second vector by `I` converts oriented area back to the real inner
product. -/
theorem complexAreaForm_I_mul_right (z w : ℂ) :
    Complex.orientation.areaForm z (Complex.I * w) = ⟪z, w⟫_ℝ := by
  simpa only [Complex.rightAngleRotation] using
    Complex.orientation.areaForm_rightAngleRotation_right z w

/-- A unit complex number has squared norm one. -/
theorem complexNormSq_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq z = 1 := by
  rw [Complex.normSq_eq_norm_sq, hz]
  simp

/-- Division by a unit normal reads the oriented coefficient in the imaginary part. -/
theorem im_div_eq_complexAreaForm_of_norm_eq_one {n v : ℂ} (hn : ‖n‖ = 1) :
    (v / n).im = Complex.orientation.areaForm n v := by
  rw [Complex.div_im, complexNormSq_eq_one_of_norm_eq_one hn]
  simp only [div_one, Complex.areaForm, Complex.mul_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- In the oriented orthonormal frame `(n, I * n)`, a vector orthogonal to the unit
normal `n` has only its oriented component.  The coefficient is deliberately stated
as `(v / n).im`, matching the scalar quotient used by radial parametrizations. -/
theorem eq_I_mul_mul_im_div_of_norm_eq_one_of_realInner_eq_zero
    {n v : ℂ} (hn : ‖n‖ = 1) (horth : ⟪n, v⟫_ℝ = 0) :
    v = Complex.I * n * ((v / n).im : ℂ) := by
  have hnormSq : Complex.normSq n = 1 :=
    complexNormSq_eq_one_of_norm_eq_one hn
  have hre : (v * star n).re = 0 := by
    simpa only [complexRealInner_eq_re_mul_conj] using horth
  have him :
      (v * star n).im = Complex.orientation.areaForm n v := by
    simp only [Complex.areaForm, mul_comm, starRingEnd_apply]
  have hproduct :
      v * star n =
        Complex.I * (Complex.orientation.areaForm n v : ℂ) := by
    calc
      v * star n =
          (((v * star n).re : ℝ) : ℂ) +
            (((v * star n).im : ℝ) : ℂ) * Complex.I :=
        (Complex.re_add_im (v * star n)).symm
      _ = (Complex.orientation.areaForm n v : ℂ) * Complex.I := by
        rw [hre, him]
        simp
      _ = Complex.I * (Complex.orientation.areaForm n v : ℂ) := by ring
  calc
    v = v * (Complex.normSq n : ℂ) := by rw [hnormSq]; simp
    _ = v * (star n * n) := by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
    _ = (v * star n) * n := by ring
    _ = (Complex.I * (Complex.orientation.areaForm n v : ℂ)) * n := by
      rw [hproduct]
    _ = Complex.I * n * (Complex.orientation.areaForm n v : ℂ) := by ring
    _ = Complex.I * n * ((v / n).im : ℂ) := by
      rw [im_div_eq_complexAreaForm_of_norm_eq_one hn]

/-- The oriented component of a radial tangent is positive.  Algebraically, if
`v = (a + I * rho) * u`, then orthogonality to `n` and the positivity of the radial
component `⟪n,u⟫` force the oriented area `areaForm n v` to be positive. -/
theorem complexAreaForm_radialTangent_pos
    {a rho : ℝ} {u n v : ℂ}
    (hv : v = ((a : ℂ) + Complex.I * (rho : ℂ)) * u)
    (hu : ‖u‖ = 1) (hrho : 0 < rho)
    (hn : ‖n‖ = 1) (horth : ⟪n, v⟫_ℝ = 0)
    (hforward : 0 < ⟪n, u⟫_ℝ) :
    0 < Complex.orientation.areaForm n v := by
  have hv' : v = a • u + rho • (Complex.I * u) := by
    rw [hv]
    simp only [Complex.real_smul]
    ring
  have horth' :
      a * ⟪n, u⟫_ℝ - rho * Complex.orientation.areaForm n u = 0 := by
    have h := horth
    rw [hv', inner_add_right, real_inner_smul_right,
      real_inner_smul_right, complexRealInner_I_mul_right] at h
    simpa only [mul_neg, sub_eq_add_neg] using h
  have harea :
      Complex.orientation.areaForm n v =
        a * Complex.orientation.areaForm n u + rho * ⟪n, u⟫_ℝ := by
    rw [hv']
    simp only [map_add, map_smul, smul_eq_mul,
      complexAreaForm_I_mul_right]
  have hunit :
      ⟪n, u⟫_ℝ ^ 2 + Complex.orientation.areaForm n u ^ 2 = 1 := by
    simpa only [hn, hu, one_pow, one_mul] using
      Complex.orientation.inner_sq_add_areaForm_sq n u
  have hproduct :
      Complex.orientation.areaForm n v * ⟪n, u⟫_ℝ = rho := by
    calc
      Complex.orientation.areaForm n v * ⟪n, u⟫_ℝ =
          (a * Complex.orientation.areaForm n u + rho * ⟪n, u⟫_ℝ) *
            ⟪n, u⟫_ℝ := by rw [harea]
      _ = rho *
            (⟪n, u⟫_ℝ ^ 2 + Complex.orientation.areaForm n u ^ 2) +
          Complex.orientation.areaForm n u *
            (a * ⟪n, u⟫_ℝ - rho * Complex.orientation.areaForm n u) := by
        ring
      _ = rho := by rw [hunit, horth']; ring
  have hquotient :
      Complex.orientation.areaForm n v = rho / ⟪n, u⟫_ℝ :=
    (eq_div_iff hforward.ne').2 hproduct
  rw [hquotient]
  exact div_pos hrho hforward

/-- The imaginary coefficient in the unit-normal frame is positive for a positively
oriented radial tangent. -/
theorem im_div_radialTangent_pos
    {a rho : ℝ} {u n v : ℂ}
    (hv : v = ((a : ℂ) + Complex.I * (rho : ℂ)) * u)
    (hu : ‖u‖ = 1) (hrho : 0 < rho)
    (hn : ‖n‖ = 1) (horth : ⟪n, v⟫_ℝ = 0)
    (hforward : 0 < ⟪n, u⟫_ℝ) :
    0 < (v / n).im := by
  rw [im_div_eq_complexAreaForm_of_norm_eq_one hn]
  exact complexAreaForm_radialTangent_pos hv hu hrho hn horth hforward

/-- A radial tangent satisfying the outward-normal and orthogonality conditions has
the positive orientation and arclength coefficient:
`v = I * n * ‖v‖`. -/
theorem radialTangent_eq_I_mul_normal_mul_norm
    {a rho : ℝ} {u n v : ℂ}
    (hv : v = ((a : ℂ) + Complex.I * (rho : ℂ)) * u)
    (hu : ‖u‖ = 1) (hrho : 0 < rho)
    (hn : ‖n‖ = 1) (horth : ⟪n, v⟫_ℝ = 0)
    (hforward : 0 < ⟪n, u⟫_ℝ) :
    v = Complex.I * n * (‖v‖ : ℂ) := by
  have hdecomposition :
      v = Complex.I * n * ((v / n).im : ℂ) :=
    eq_I_mul_mul_im_div_of_norm_eq_one_of_realInner_eq_zero hn horth
  have hcoefficient : 0 < (v / n).im :=
    im_div_radialTangent_pos hv hu hrho hn horth hforward
  have hnorm : ‖v‖ = (v / n).im := by
    calc
      ‖v‖ = ‖Complex.I * n * ((v / n).im : ℂ)‖ :=
        congrArg norm hdecomposition
      _ = (v / n).im := by
        simp only [norm_mul, Complex.norm_I, hn, one_mul,
          Complex.norm_of_nonneg hcoefficient.le]
  calc
    v = Complex.I * n * ((v / n).im : ℂ) := hdecomposition
    _ = Complex.I * n * (‖v‖ : ℂ) := by rw [hnorm]

end CrouzeixConjecture
