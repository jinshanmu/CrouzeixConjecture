module

public import CrouzeixConjecture.QRangeConsequences
public import CrouzeixConjecture.QSimilarityGeometry
public import CrouzeixConjecture.QOrbitExtractionMatrix
public import CrouzeixConjecture.QTransferAlgebra
public import CrouzeixConjecture.QRationalSpectralMapping
public import CrouzeixConjecture.QScaledRational

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The constant transferred from an ordinary numerical-range bound `K` to
the scaled `q`-numerical range. -/
def qTransferredConstant (K : ℝ) (q : ℂ) : ℝ :=
  max 1 (K / qKappa ‖q‖)

/-- The explicit matrix Möbius composition is the rotated real Möbius
transform of the scaled rational matrix value. -/
theorem mobiusComposeMatrixEval_eq_rotatedRealMobiusEval
    (f : RatFunc ℂ) (c omega : ℂ) (a : ℝ) (A : SquareMatrix n) :
    mobiusComposeMatrixEval f (omega * c) a A =
      rotatedRealMobiusEval omega a (c • rationalMatrixEval f A) := by
  rw [mobiusComposeMatrixEval, rotatedRealMobiusEval,
    rotatedRealMobiusNumerator, rotatedRealMobiusDenominator]
  congr 2
  · simp only [smul_smul]
  · simp only [smul_smul]
    congr 2
    ring

/-- Pole-freeness restricts along set inclusion. -/
theorem rationalPoleFreeOn_mono {f : RatFunc ℂ} {s t : Set ℂ}
    (hfree : RationalPoleFreeOn f t) (hst : s ⊆ t) :
    RationalPoleFreeOn f s := by
  rw [rationalPoleFreeOn_iff] at hfree ⊢
  exact fun z hz ↦ hfree z (hst hz)

/-- A pointwise unit-disk bound controls the attained rational maximum on a
numerical range. -/
theorem maxRationalModulusOnNumericalRange_le_one
    [Nonempty n] (B : SquareMatrix n) (g : RatFunc ℂ)
    (hfree : RationalPoleFreeOn g (numericalRange B))
    (hbound : ∀ z ∈ numericalRange B, ‖rationalScalarEval g z‖ ≤ 1) :
    maxRationalModulusOnNumericalRange B g ≤ 1 := by
  obtain ⟨z, hz, hmax⟩ :=
    exists_maxRationalModulusOnNumericalRange B g hfree
  rw [← hmax]
  exact hbound z hz

/-- The `M + epsilon` estimate at the heart of rational transfer. -/
theorem rationalMatrixEval_le_qTransferredConstant_mul_max_add
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K)
    (hbase : UniversalRationalNumericalRangeBound.{u} K)
    (A : SquareMatrix n) (f : RatFunc ℂ)
    (hfree : RationalPoleFreeOn f (scaledQNumericalRange q A))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ‖rationalMatrixEval f A‖ ≤
      qTransferredConstant K q *
        (maxRationalModulusOnScaledQNumericalRange q A f + epsilon) := by
  let Omega : Set ℂ := scaledQNumericalRange q A
  let M : ℝ := maxRationalModulusOnScaledQNumericalRange q A f
  let r : ℝ := ‖q‖
  let kappa : ℝ := qKappa r
  let d : ℂ := (((M + epsilon)⁻¹ : ℝ) : ℂ)
  let F : SquareMatrix n := rationalMatrixEval f A
  let X : SquareMatrix n := d • F
  have hr0 : 0 < r := norm_pos_iff.mpr hq0
  have hr1 : r ≤ 1 := hq1
  have hkappa : 1 ≤ kappa := one_le_qKappa hr0 hr1
  have hOmegaNonempty : Omega.Nonempty := by
    exact scaledQNumericalRange_nonempty hq1 A
  obtain ⟨zmax, hzmax, hMmax⟩ :=
    exists_maxRationalModulusOnScaledQNumericalRange q A f
      hOmegaNonempty hfree
  have hM0 : 0 ≤ M := by
    dsimp [M]
    rw [← hMmax]
    exact norm_nonneg _
  have hdenPos : 0 < M + epsilon := add_pos_of_nonneg_of_pos hM0 hepsilon
  have hspectrumA : matrixSpectrum A ⊆ Omega := by
    exact matrixSpectrum_subset_scaledQNumericalRange hq0 hq1 A
  have hscalarStrict :
      ∀ z ∈ Omega, ‖d * rationalScalarEval f z‖ < 1 := by
    intro z hz
    have hzBound : ‖rationalScalarEval f z‖ ≤ M := by
      exact norm_rationalScalarEval_le_maxOnScaledQNumericalRange
        q A f hOmegaNonempty hfree hz
    have hzLt : ‖rationalScalarEval f z‖ < M + epsilon :=
      hzBound.trans_lt (lt_add_of_pos_right M hepsilon)
    rw [norm_mul]
    have hdNorm : ‖d‖ = (M + epsilon)⁻¹ := by
      dsimp [d]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hdenPos)]
    rw [hdNorm, inv_mul_lt_one₀ hdenPos]
    exact hzLt
  have hspectrumX : matrixSpectrum X ⊆ closedUnitDisk := by
    dsimp [X, F]
    exact matrixSpectrum_smul_rationalMatrixEval_subset_closedUnitDisk_of_norm_lt_one
      f d A Omega hspectrumA hfree hscalarStrict
  have hExtract : ‖X‖ ≤ max 1 (K / kappa) := by
    apply norm_le_max_one_div_of_uniform_stretch_mobius X hkappa hspectrumX
    intro v hv omega a homega ha0 ha1
    let S : SquareMatrix n := stretchSimilarity kappa v
    let B : SquareMatrix n := S * A * S⁻¹
    let ctotal : ℂ := omega * d
    let g : RatFunc ℂ := mobiusComposeRatFunc f ctotal a
    have hkappaPos : 0 < kappa := zero_lt_one.trans_le hkappa
    have hSunit : IsUnit S := by
      dsimp [S]
      exact IsUnit.of_mul_eq_one (stretchInverseCandidate kappa v)
        (stretchSimilarity_mul_inverseCandidate hkappaPos.ne' hv)
    have hcontain : numericalRange B ⊆ Omega := by
      intro z hz
      have hzReal :=
        numericalRange_stretchSimilarity_subset_scaledQNumericalRange
          hr0 hr1 A hv hz
      dsimp [B, S] at hz
      change z ∈ scaledQNumericalRange q A
      rw [scaledQNumericalRange_eq_norm hq0 A]
      exact hzReal
    have htotalStrict :
        ∀ z ∈ Omega, ‖ctotal * rationalScalarEval f z‖ < 1 := by
      intro z hz
      dsimp [ctotal]
      rw [mul_assoc, norm_mul, homega, one_mul]
      exact hscalarStrict z hz
    have hscalarDenominator :
        ∀ z ∈ Omega,
          1 - ((a : ℂ) * ctotal) * rationalScalarEval f z ≠ 0 := by
      intro z hz
      simpa only [mul_assoc] using
        one_sub_real_mul_ne_zero_of_norm_lt_one ha0 ha1
          (htotalStrict z hz)
    have hfreeGOnOmega : RationalPoleFreeOn g Omega := by
      dsimp [g]
      exact rationalPoleFreeOn_mobiusComposeRatFunc
        f ctotal a Omega hfree hscalarDenominator
    have hfreeGOnB : RationalPoleFreeOn g (numericalRange B) :=
      rationalPoleFreeOn_mono hfreeGOnOmega hcontain
    have hspectrumTotal :
        matrixSpectrum (ctotal • rationalMatrixEval f A) ⊆ closedUnitDisk :=
      matrixSpectrum_smul_rationalMatrixEval_subset_closedUnitDisk_of_norm_lt_one
        f ctotal A Omega hspectrumA hfree htotalStrict
    have hcomposeA :
        rationalMatrixEval g A = mobiusComposeMatrixEval f ctotal a A := by
      dsimp [g]
      exact rationalMatrixEval_mobiusComposeRatFunc_of_disk
        f ctotal a A Omega hspectrumA hfree htotalStrict hspectrumTotal ha0 ha1
    have hsimilarity :
        rationalMatrixEval g B = S * rationalMatrixEval g A * S⁻¹ := by
      dsimp [B]
      exact rationalMatrixEval_similarity_of_rationalPoleFreeOn
        g A S Omega hSunit hspectrumA hfreeGOnOmega
    have horbitEq :
        S * rotatedRealMobiusEval omega a X * S⁻¹ =
          rationalMatrixEval g B := by
      calc
        S * rotatedRealMobiusEval omega a X * S⁻¹ =
            S * mobiusComposeMatrixEval f ctotal a A * S⁻¹ := by
          dsimp [X, F, ctotal]
          rw [mobiusComposeMatrixEval_eq_rotatedRealMobiusEval]
        _ = S * rationalMatrixEval g A * S⁻¹ := by rw [hcomposeA]
        _ = rationalMatrixEval g B := hsimilarity.symm
    have hpointwiseG :
        ∀ z ∈ numericalRange B, ‖rationalScalarEval g z‖ ≤ 1 := by
      intro z hz
      have hzOmega : z ∈ Omega := hcontain hz
      have hfden : Polynomial.eval z f.denom ≠ 0 :=
        (rationalPoleFreeOn_iff f Omega).mp hfree z hzOmega
      have hnewden :
          1 - ((a : ℂ) * ctotal) * rationalScalarEval f z ≠ 0 :=
        hscalarDenominator z hzOmega
      have heval := rationalScalarEval_mobiusComposeRatFunc
        f ctotal z a hfden hnewden
      have hwdisk : d * rationalScalarEval f z ∈ closedUnitDisk := by
        simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using
          (hscalarStrict z hzOmega).le
      have hmobius := norm_rotatedRealMobius_le_one
        hwdisk homega ha0 ha1
      dsimp [g]
      rw [heval]
      dsimp [ctotal]
      simpa only [mul_assoc] using hmobius
    have hmaxG : maxRationalModulusOnNumericalRange B g ≤ 1 :=
      maxRationalModulusOnNumericalRange_le_one B g hfreeGOnB hpointwiseG
    calc
      ‖S * rotatedRealMobiusEval omega a X * S⁻¹‖ =
          ‖rationalMatrixEval g B‖ := by rw [horbitEq]
      _ ≤ K * maxRationalModulusOnNumericalRange B g :=
        hbase B g hfreeGOnB
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hmaxG (zero_le_one.trans hK)
      _ = K := mul_one K
  have hXnorm : ‖X‖ = (M + epsilon)⁻¹ * ‖rationalMatrixEval f A‖ := by
    dsimp [X, F]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hdenPos)]
  rw [hXnorm] at hExtract
  have hunscaled := (inv_mul_le_iff₀' hdenPos).mp hExtract
  simpa [qTransferredConstant, kappa, r, M] using hunscaled

/-- Reusable rational transfer theorem.  Any universal ordinary
numerical-range bound `K` transfers to the scaled `q`-numerical range with
constant `max 1 (K / qKappa ‖q‖)`. -/
theorem rationalScaledQNumericalRangeBound_of_universal
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K)
    (hbase : UniversalRationalNumericalRangeBound.{u} K)
    (A : SquareMatrix n) (f : RatFunc ℂ)
    (hfree : RationalPoleFreeOn f (scaledQNumericalRange q A)) :
    ‖rationalMatrixEval f A‖ ≤
      qTransferredConstant K q *
        maxRationalModulusOnScaledQNumericalRange q A f := by
  let C : ℝ := qTransferredConstant K q
  let M : ℝ := maxRationalModulusOnScaledQNumericalRange q A f
  have hC1 : 1 ≤ C := by
    exact le_max_left _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  apply le_of_forall_pos_le_add
  intro delta hdelta
  have hepsilon : 0 < delta / C := div_pos hdelta hCpos
  have happrox :=
    rationalMatrixEval_le_qTransferredConstant_mul_max_add
      hq0 hq1 hK hbase A f hfree hepsilon
  calc
    ‖rationalMatrixEval f A‖ ≤ C * (M + delta / C) := by
      simpa only [C, M] using happrox
    _ = C * M + delta := by
      field_simp [hCpos.ne']

/-- Constant-two rational scaled-`q` spectral-set bound. -/
theorem rationalScaledQNumericalRangeBound_two
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    (A : SquareMatrix n) (f : RatFunc ℂ)
    (hfree : RationalPoleFreeOn f (scaledQNumericalRange q A)) :
    ‖rationalMatrixEval f A‖ ≤
      qTransferredConstant 2 q *
        maxRationalModulusOnScaledQNumericalRange q A f := by
  exact rationalScaledQNumericalRangeBound_of_universal
    hq0 hq1 (by norm_num) universalRationalNumericalRangeBound_two A f hfree

/-- Polynomial specialization of the constant-two rational transfer bound. -/
theorem polynomialScaledQNumericalRangeBound_two
    [Nontrivial n] {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1)
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    ‖polynomialEval p A‖ ≤
      qTransferredConstant 2 q *
        maxPolynomialModulusOnScaledQNumericalRange q A p := by
  simpa using
    (rationalScaledQNumericalRangeBound_two hq0 hq1 A
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      (rationalPoleFreeOn_algebraMap_polynomial p
        (scaledQNumericalRange q A)))

end CrouzeixConjecture
