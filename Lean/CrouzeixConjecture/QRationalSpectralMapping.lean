module

public import CrouzeixConjecture.QTransferAlgebra

@[expose] public section

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A polynomial with no zero on the spectrum evaluates to an invertible
matrix. -/
theorem polynomialEval_isUnit_of_forall_ne_zero_on_spectrum
    [Nonempty n] (p : Polynomial ℂ) (A : SquareMatrix n)
    (hp : ∀ z ∈ matrixSpectrum A, Polynomial.eval z p ≠ 0) :
    IsUnit (polynomialEval p A) := by
  rw [← spectrum.zero_notMem_iff ℂ]
  rw [polynomialEval, spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hzero⟩
  exact hp z hz hzero

/-- Spectral mapping for the reduced rational matrix calculus, in the
direction needed by the transfer argument.  Pole-freeness is required on a
set containing the original matrix spectrum. -/
theorem matrixSpectrum_rationalMatrixEval_subset_image
    [Nonempty n] (f : RatFunc ℂ) (A : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s) :
    matrixSpectrum (rationalMatrixEval f A) ⊆
      rationalScalarEval f '' matrixSpectrum A := by
  intro w hw
  by_contra hnotImage
  let p : Polynomial ℂ := Polynomial.C w * f.denom - f.num
  have hfdenPoint :
      ∀ z ∈ matrixSpectrum A, Polynomial.eval z f.denom ≠ 0 := by
    intro z hz
    exact (rationalPoleFreeOn_iff f s).mp hfree z (hspectrum hz)
  have hpPoint : ∀ z ∈ matrixSpectrum A, Polynomial.eval z p ≠ 0 := by
    intro z hz hpzero
    apply hnotImage
    refine ⟨z, hz, ?_⟩
    have hden := hfdenPoint z hz
    have heq : w * Polynomial.eval z f.denom = Polynomial.eval z f.num := by
      apply sub_eq_zero.mp
      simpa [p] using hpzero
    rw [rationalScalarEval]
    apply (div_eq_iff hden).mpr
    exact heq.symm
  have hpUnit : IsUnit (polynomialEval p A) :=
    polynomialEval_isUnit_of_forall_ne_zero_on_spectrum p A hpPoint
  have hdenUnit : IsUnit (polynomialEval f.denom A) :=
    polynomialEval_denom_isUnit_of_rationalPoleFreeOn_of_spectrum_subset
      f A s hspectrum hfree
  have hdenInvUnit : IsUnit (polynomialEval f.denom A)⁻¹ := by
    rwa [Matrix.isUnit_nonsing_inv_iff]
  have hfactor :
      (w • (1 : SquareMatrix n) - rationalMatrixEval f A) =
        polynomialEval p A * (polynomialEval f.denom A)⁻¹ := by
    have hdenDet : IsUnit (polynomialEval f.denom A).det :=
      (polynomialEval f.denom A).isUnit_iff_isUnit_det.mp hdenUnit
    rw [rationalMatrixEval]
    calc
      w • (1 : SquareMatrix n) -
          polynomialEval f.num A * (polynomialEval f.denom A)⁻¹ =
          (w • polynomialEval f.denom A - polynomialEval f.num A) *
            (polynomialEval f.denom A)⁻¹ := by
        rw [Matrix.sub_mul, Matrix.smul_mul,
          (polynomialEval f.denom A).mul_nonsing_inv hdenDet]
      _ = polynomialEval p A * (polynomialEval f.denom A)⁻¹ := by
        congr 1
        simp [p, polynomialEval, Algebra.smul_def]
  have hresolvent : IsUnit (w • (1 : SquareMatrix n) - rationalMatrixEval f A) := by
    rw [hfactor]
    exact hpUnit.mul hdenInvUnit
  exact (spectrum.mem_iff.mp hw) (by
    simpa only [Algebra.algebraMap_eq_smul_one] using hresolvent)

/-- Scaling the rational matrix value scales the scalar rational spectral
image. -/
theorem matrixSpectrum_smul_rationalMatrixEval_subset_image
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (A : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s) :
    matrixSpectrum (c • rationalMatrixEval f A) ⊆
      (fun z ↦ c * rationalScalarEval f z) '' matrixSpectrum A := by
  have hmap := matrixSpectrum_rationalMatrixEval_subset_image f A s hspectrum hfree
  rw [show c • rationalMatrixEval f A =
      polynomialEval (Polynomial.C c * Polynomial.X) (rationalMatrixEval f A) by
    simp [polynomialEval, Algebra.smul_def],
    matrixSpectrum, polynomialEval, spectrum.map_polynomial_aeval]
  rintro w ⟨mu, hmu, rfl⟩
  obtain ⟨z, hz, hmuEq⟩ := hmap hmu
  refine ⟨z, hz, ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hmuEq]

/-- A non-strict scalar disk bound on a set containing the spectrum gives the
closed-unit-disk spectral hypothesis for the scaled rational matrix value. -/
theorem matrixSpectrum_smul_rationalMatrixEval_subset_closedUnitDisk
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (A : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s)
    (hbound : ∀ z ∈ s, ‖c * rationalScalarEval f z‖ ≤ 1) :
    matrixSpectrum (c • rationalMatrixEval f A) ⊆ closedUnitDisk := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ :=
    matrixSpectrum_smul_rationalMatrixEval_subset_image f c A s hspectrum hfree hw
  simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using
    hbound z (hspectrum hz)

/-- Strict scalar control, as produced by the `M + ε` normalization in the
manuscript, implies the closed-unit-disk spectral hypothesis used by orbit
extraction. -/
theorem matrixSpectrum_smul_rationalMatrixEval_subset_closedUnitDisk_of_norm_lt_one
    [Nonempty n] (f : RatFunc ℂ) (c : ℂ) (A : SquareMatrix n) (s : Set ℂ)
    (hspectrum : matrixSpectrum A ⊆ s)
    (hfree : RationalPoleFreeOn f s)
    (hbound : ∀ z ∈ s, ‖c * rationalScalarEval f z‖ < 1) :
    matrixSpectrum (c • rationalMatrixEval f A) ⊆ closedUnitDisk :=
  matrixSpectrum_smul_rationalMatrixEval_subset_closedUnitDisk
    f c A s hspectrum hfree fun z hz ↦ (hbound z hz).le

end CrouzeixConjecture
