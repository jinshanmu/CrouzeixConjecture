module

public import CrouzeixConjecture.QOrbitExtraction
public import CrouzeixConjecture.QMobius
public import CrouzeixConjecture.QSimilarityStretch
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A continuous operator on finite-dimensional Euclidean space attains its norm on a
unit vector. -/
theorem exists_unit_vector_norm_euclideanOperator_eq [Nonempty n]
    (X : SquareMatrix n) :
    ∃ x : EuclideanVector n,
      ‖x‖ = 1 ∧ ‖euclideanOperator X x‖ = ‖X‖ := by
  let T := euclideanOperator X
  have hsphere : (Metric.sphere (0 : EuclideanVector n) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanVector n) 1).exists_isMaxOn hsphere
      T.continuous.norm.continuousOn
  refine ⟨x, ?_, ?_⟩
  · exact mem_sphere_zero_iff_norm.mp hx
  · have hgreatest : IsGreatest
        ((fun z : EuclideanVector n ↦ ‖T z‖) ''
          Metric.sphere (0 : EuclideanVector n) 1) ‖T x‖ := by
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hmax hz
    calc
      ‖euclideanOperator X x‖ =
          sSup ((fun z : EuclideanVector n ↦ ‖T z‖) ''
            Metric.sphere (0 : EuclideanVector n) 1) :=
        hgreatest.csSup_eq.symm
      _ = ‖T‖ := T.sSup_sphere_eq_norm
      _ = ‖X‖ := rfl

/-- The unit scalar which rotates a complex inner product onto the nonnegative real axis. -/
def extractionPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

@[simp]
theorem norm_extractionPhase (z : ℂ) : ‖extractionPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [extractionPhase, hz]
  · simp [extractionPhase, hz, norm_ne_zero_iff.mpr hz]

/-- Conjugating by `extractionPhase` turns a scalar into its real norm. -/
theorem conj_extractionPhase_mul (z : ℂ) :
    conj (extractionPhase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [extractionPhase, hz]
  · rw [extractionPhase, if_neg hz, map_div₀, Complex.conj_ofReal,
      div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    push_cast
    field_simp

/-- A nonzero Euclidean eigenvector witnesses membership in the matrix spectrum. -/
theorem mem_matrixSpectrum_of_euclideanOperator_apply_eq_smul
    (X : SquareMatrix n) {x : EuclideanVector n} {lambda : ℂ}
    (hx : x ≠ 0)
    (heigen : euclideanOperator X x = lambda • x) :
    lambda ∈ matrixSpectrum X := by
  let z : n → ℂ := WithLp.ofLp x
  have hz : z ≠ 0 := by
    simpa [z] using hx
  have heigenRaw : X.toLin' z = lambda • z := by
    have h := congrArg WithLp.ofLp heigen
    simpa [z, euclideanOperator, Matrix.ofLp_toEuclideanCLM,
      Matrix.toLin'_apply] using h
  have heigenvector : Module.End.HasEigenvector X.toLin' lambda z :=
    ⟨Module.End.mem_eigenspace_iff.mpr heigenRaw, hz⟩
  have hspectrum : lambda ∈ spectrum ℂ X.toLin' :=
    (Module.End.hasEigenvalue_of_hasEigenvector heigenvector).mem_spectrum
  rw [matrixSpectrum, ← Matrix.spectrum_toLin' X]
  exact hspectrum

/-- The Möbius denominator applied to a right singular vector, in the rotated
singular-vector coordinates used by extraction. -/
theorem euclideanOperator_rotatedRealMobiusDenominator_apply_of_image
    (X : SquareMatrix n) {x y : EuclideanVector n} {t a : ℝ} {omega : ℂ}
    (hX : euclideanOperator X x = (t : ℂ) • y) :
    euclideanOperator (rotatedRealMobiusDenominator omega a X) x =
      x - (a * t : ℂ) • (omega • y) := by
  rw [rotatedRealMobiusDenominator, map_sub, map_one, map_smul]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, hX, smul_smul]
  congr 2
  ring

/-- The corresponding Möbius numerator applied to the same vector. -/
theorem euclideanOperator_rotatedRealMobiusNumerator_apply_of_image
    (X : SquareMatrix n) {x y : EuclideanVector n} {t a : ℝ} {omega : ℂ}
    (hX : euclideanOperator X x = (t : ℂ) • y) :
    euclideanOperator (rotatedRealMobiusNumerator omega a X) x =
      (t : ℂ) • (omega • y) - (a : ℂ) • x := by
  rw [rotatedRealMobiusNumerator, map_sub, map_smul, map_smul, map_one]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, hX, smul_smul]
  congr 2
  ring

/-- Similarity-orbit extraction in the exact rank-one form used by the proof.
It is enough to control the Möbius transforms after the adapted rank-one
stretches; no other positive similarities enter the argument. -/
theorem norm_le_max_one_div_of_uniform_stretch_mobius
    [Nonempty n] (X : SquareMatrix n) {kappa K : ℝ}
    (hkappa : 1 ≤ kappa)
    (hspectrum : matrixSpectrum X ⊆ closedUnitDisk)
    (hstretch :
      ∀ (v : EuclideanVector n), ‖v‖ = 1 →
        ∀ (omega : ℂ) (a : ℝ),
          ‖omega‖ = 1 → 0 ≤ a → a < 1 →
          ‖stretchSimilarity kappa v * rotatedRealMobiusEval omega a X *
              (stretchSimilarity kappa v)⁻¹‖ ≤ K) :
    ‖X‖ ≤ max 1 (K / kappa) := by
  by_cases hsmall : ‖X‖ ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have ht : 1 < ‖X‖ := lt_of_not_ge hsmall
  have htpos : 0 < ‖X‖ := zero_lt_one.trans ht
  obtain ⟨x, hx, hXnorm⟩ := exists_unit_vector_norm_euclideanOperator_eq X
  let t : ℝ := ‖X‖
  let y : EuclideanVector n := ((t : ℂ)⁻¹) • euclideanOperator X x
  have ht' : 1 < t := ht
  have htpos' : 0 < t := htpos
  have hy : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos', hXnorm]
    exact inv_mul_cancel₀ htpos'.ne'
  have hX : euclideanOperator X x = (t : ℂ) • y := by
    dsimp [y]
    calc
      euclideanOperator X x = (1 : ℂ) • euclideanOperator X x := by simp
      _ = ((t : ℂ) * (t : ℂ)⁻¹) • euclideanOperator X x := by
        rw [mul_inv_cancel₀]
        exact_mod_cast htpos'.ne'
      _ = (t : ℂ) • ((t : ℂ)⁻¹ • euclideanOperator X x) :=
        (smul_smul _ _ _).symm
  let z : ℂ := ⟪y, x⟫_ℂ
  let omega : ℂ := extractionPhase z
  let yrot : EuclideanVector n := omega • y
  let c : ℝ := ‖z‖
  have homega : ‖omega‖ = 1 := norm_extractionPhase z
  have hyrot : ‖yrot‖ = 1 := by
    dsimp [yrot]
    rw [norm_smul, homega, hy, one_mul]
  have hyrotx : ⟪yrot, x⟫_ℂ = (c : ℂ) := by
    dsimp [yrot]
    rw [inner_smul_left]
    simpa [omega, z, c] using conj_extractionPhase_mul z
  have hc0 : 0 ≤ c := norm_nonneg z
  have hc_le : c ≤ 1 := by
    calc
      c = ‖⟪y, x⟫_ℂ‖ := rfl
      _ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
      _ = 1 := by rw [hy, hx, one_mul]
  have hc_ne : c ≠ 1 := by
    intro hc
    have hinnerOne : ⟪yrot, x⟫_ℂ = 1 := by
      rw [hyrotx, hc]
      norm_num
    have hyrotEq : yrot = x :=
      (inner_eq_one_iff_of_norm_eq_one hyrot hx).mp hinnerOne
    have homegaConjMul : conj omega * omega = 1 := by
      calc
        conj omega * omega = (Complex.normSq omega : ℂ) :=
          Complex.normSq_eq_conj_mul_self.symm
        _ = ((‖omega‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.normSq_eq_norm_sq]
        _ = 1 := by rw [homega]; norm_num
    have hyEq : y = conj omega • x := by
      calc
        y = (1 : ℂ) • y := by simp
        _ = (conj omega * omega) • y := by rw [homegaConjMul]
        _ = conj omega • (omega • y) := (smul_smul _ _ _).symm
        _ = conj omega • yrot := rfl
        _ = conj omega • x := by rw [hyrotEq]
    have hxne : x ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [hx]; norm_num)
    have heigen : euclideanOperator X x =
        ((t : ℂ) * conj omega) • x := by
      rw [hX, hyEq, smul_smul]
    have hlambda := mem_matrixSpectrum_of_euclideanOperator_apply_eq_smul
      X hxne heigen
    have hlambdaDisk := hspectrum hlambda
    have hlambdaNorm : ‖(t : ℂ) * conj omega‖ ≤ 1 := by
      simpa [closedUnitDisk, Metric.mem_closedBall, dist_zero_right] using
        hlambdaDisk
    have ht_le_one : t ≤ 1 := by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos htpos', homega] using hlambdaNorm
    exact (not_lt_of_ge ht_le_one) ht'
  have hc1 : c < 1 := lt_of_le_of_ne hc_le hc_ne
  obtain ⟨a, ha0, ha1, heq⟩ :=
    exists_extractionParameter ht' hc0 hc1
  let u : EuclideanVector n := x - (a * t : ℂ) • yrot
  let w : EuclideanVector n := (t : ℂ) • yrot - (a : ℂ) • x
  have huw : ⟪u, w⟫_ℂ = 0 := by
    exact extraction_vectors_inner_eq_zero hx hyrot hyrotx heq
  have hamplify : t * ‖u‖ ≤ ‖w‖ := by
    exact extraction_vectors_amplify hx hyrot hyrotx ht'.le ha0 ha1.le hc0 heq
  have hunit : IsUnit (rotatedRealMobiusDenominator omega a X) :=
    isUnit_rotatedRealMobiusDenominator X hspectrum homega ha0 ha1
  have hdenApply :
      euclideanOperator (rotatedRealMobiusDenominator omega a X) x = u := by
    simpa [u, yrot] using
      euclideanOperator_rotatedRealMobiusDenominator_apply_of_image X hX
  have hnumApply :
      euclideanOperator (rotatedRealMobiusNumerator omega a X) x = w := by
    simpa [w, yrot] using
      euclideanOperator_rotatedRealMobiusNumerator_apply_of_image X hX
  have hmobius : euclideanOperator (rotatedRealMobiusEval omega a X) u = w := by
    calc
      euclideanOperator (rotatedRealMobiusEval omega a X) u =
          euclideanOperator (rotatedRealMobiusEval omega a X)
            (euclideanOperator (rotatedRealMobiusDenominator omega a X) x) := by
              rw [hdenApply]
      _ = euclideanOperator (rotatedRealMobiusNumerator omega a X) x :=
        euclideanOperator_rotatedRealMobiusEval_apply_denominator X hunit x
      _ = w := hnumApply
  have hwne : w ≠ 0 := by
    intro hw
    have hvec : (t : ℂ) • yrot = (a : ℂ) • x := sub_eq_zero.mp hw
    have hnorm := congrArg norm hvec
    simp only [norm_smul, hyrot, hx, mul_one, Complex.norm_real,
      Real.norm_eq_abs] at hnorm
    rw [abs_of_pos htpos', abs_of_nonneg ha0] at hnorm
    linarith
  have hune : u ≠ 0 := by
    intro hu
    apply hwne
    simpa [hu] using hmobius.symm
  have huNormPos : 0 < ‖u‖ := norm_pos_iff.mpr hune
  have hwNormPos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  let v : EuclideanVector n := ((‖w‖ : ℂ)⁻¹) • w
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwNormPos]
    exact inv_mul_cancel₀ hwNormPos.ne'
  have hwu : ⟪w, u⟫_ℂ = 0 := by
    rw [← inner_conj_symm, huw]
    simp
  have hvu : ⟪v, u⟫_ℂ = 0 := by
    dsimp [v]
    rw [inner_smul_left, hwu]
    simp
  have hkappaPos : 0 < kappa := zero_lt_one.trans_le hkappa
  have hSinvU :
      euclideanOperator (stretchSimilarity kappa v)⁻¹ u = u := by
    rw [stretchSimilarity_inv hkappaPos.ne' hv]
    exact stretchInverseCandidate_apply_of_inner_eq_zero kappa hvu
  have hwDecomp : w = (‖w‖ : ℂ) • v := by
    simp [v, smul_smul, hwne]
  have hSw : euclideanOperator (stretchSimilarity kappa v) w =
      (kappa : ℂ) • w := by
    calc
      euclideanOperator (stretchSimilarity kappa v) w =
          euclideanOperator (stretchSimilarity kappa v) ((‖w‖ : ℂ) • v) := by
            rw [← hwDecomp]
      _ = (‖w‖ : ℂ) • euclideanOperator (stretchSimilarity kappa v) v := by
        rw [map_smul]
      _ = (‖w‖ : ℂ) • ((kappa : ℂ) • v) := by
        rw [stretchSimilarity_apply_self kappa hv]
      _ = (kappa : ℂ) • ((‖w‖ : ℂ) • v) := by
        simp only [smul_smul, mul_comm]
      _ = (kappa : ℂ) • w := by rw [← hwDecomp]
  have hconjugatedApply :
      euclideanOperator
          (stretchSimilarity kappa v * rotatedRealMobiusEval omega a X *
            (stretchSimilarity kappa v)⁻¹) u =
        (kappa : ℂ) • w := by
    simp only [map_mul, ContinuousLinearMap.mul_apply]
    rw [hSinvU, hmobius, hSw]
  have hchain : (kappa * t) * ‖u‖ ≤ K * ‖u‖ := by
    calc
      (kappa * t) * ‖u‖ = kappa * (t * ‖u‖) := by ring
      _ ≤ kappa * ‖w‖ :=
        mul_le_mul_of_nonneg_left hamplify (zero_le_one.trans hkappa)
      _ = ‖(kappa : ℂ) • w‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (zero_le_one.trans hkappa)]
      _ = ‖euclideanOperator
          (stretchSimilarity kappa v * rotatedRealMobiusEval omega a X *
            (stretchSimilarity kappa v)⁻¹) u‖ := by
        rw [hconjugatedApply]
      _ ≤ ‖stretchSimilarity kappa v * rotatedRealMobiusEval omega a X *
            (stretchSimilarity kappa v)⁻¹‖ * ‖u‖ := by
        exact (euclideanOperator
          (stretchSimilarity kappa v * rotatedRealMobiusEval omega a X *
            (stretchSimilarity kappa v)⁻¹)).le_opNorm u
      _ ≤ K * ‖u‖ :=
        mul_le_mul_of_nonneg_right
          (hstretch v hv omega a homega ha0 ha1) (norm_nonneg u)
  have hkt : kappa * t ≤ K := le_of_mul_le_mul_right hchain huNormPos
  have htk : t * kappa ≤ K := by simpa [mul_comm] using hkt
  have htK : t ≤ K / kappa := (le_div_iff₀ hkappaPos).mpr htk
  exact htK.trans (le_max_right _ _)

end CrouzeixConjecture
