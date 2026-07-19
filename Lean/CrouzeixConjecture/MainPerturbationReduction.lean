module

public import CrouzeixConjecture.Perturbation
public import CrouzeixConjecture.SimpleSpectrumBridge
public import CrouzeixConjecture.Limiting
public import CrouzeixConjecture.CompletionStatement
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The exact analytic output from the double-layer construction that the
simple-spectrum perturbation argument uses.  The hypotheses record the unit
sup-norm bound and the generated-algebra identity needed to construct the
companion term.  In particular, this proposition does not contain a norm
estimate for the evaluated matrix. -/
def HasDoubleLayerCompletionProvider (B : SquareMatrix n) (s : Set ℂ) : Prop :=
  ∀ q : Polynomial ℂ,
    (∀ z ∈ s, ‖Polynomial.eval z q‖ ≤ 1) →
    generatedAlgebra (polynomialEval q B) = generatedAlgebra B →
    ∃ H : ℂ → SquareMatrix n,
      IsPositiveRealCompletion (polynomialEval q B) H

omit [Nonempty n] in
/-- A polynomial bounded by zero on the spectrum of a simple-spectrum matrix
evaluates to zero at that matrix.  This is the honest `M_Ω = 0` branch in
manuscript lines 384--388. -/
theorem polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero
    (B : SquareMatrix n) (hB : HasDistinctEigenvalues B)
    (p : Polynomial ℂ) (s : Set ℂ)
    (hspectrum : matrixSpectrum B ⊆ s)
    (hp : ∀ z ∈ s, ‖Polynomial.eval z p‖ ≤ 0) :
    polynomialEval p B = 0 := by
  let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues B hB
  have heigenvalue (i : n) : hdiag.eigenvalues i ∈ matrixSpectrum B := by
    let D := Matrix.diagonal hdiag.eigenvalues
    have hchar : B.charpoly = D.charpoly := by
      calc
        B.charpoly = (innerConjugation hdiag.changeBasis D).charpoly :=
          congrArg Matrix.charpoly hdiag.eq_conjugate
        _ = D.charpoly := by
          change (hdiag.changeBasis.val * D * hdiag.changeBasis.inv).charpoly = D.charpoly
          simpa only [Units.inv_eq_val_inv] using
            Matrix.charpoly_units_conj hdiag.changeBasis D
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [hchar, Matrix.charpoly_diagonal]
    exact (Polynomial.isRoot_prod Finset.univ
      (fun j ↦ Polynomial.X - Polynomial.C (hdiag.eigenvalues j))
      (hdiag.eigenvalues i)).mpr ⟨i, Finset.mem_univ i, by simp⟩
  have hzero : ∀ i, Polynomial.eval (hdiag.eigenvalues i) p = 0 := by
    intro i
    apply norm_eq_zero.mp
    exact le_antisymm
      (hp (hdiag.eigenvalues i) (hspectrum (heigenvalue i)))
      (norm_nonneg _)
  let e := innerConjugation hdiag.changeBasis
  calc
    polynomialEval p B = polynomialEval p
        (e (Matrix.diagonal hdiag.eigenvalues)) := by
      exact congrArg (polynomialEval p) hdiag.eq_conjugate
    _ = e (polynomialEval p (Matrix.diagonal hdiag.eigenvalues)) := by
      exact Polynomial.aeval_algHom_apply e (Matrix.diagonal hdiag.eigenvalues) p
    _ = e (Matrix.diagonal fun i ↦ Polynomial.eval (hdiag.eigenvalues i) p) := by
      rw [polynomialEval_diagonal]
    _ = 0 := by simp [hzero]

/-- Polynomial spectral mapping turns a scalar bound on a set containing the
spectrum of `B` into the closed-unit-disk hypothesis needed by the completion
lemma. -/
theorem matrixSpectrum_polynomialEval_subset_closedUnitDisk
    (B : SquareMatrix n) (q : Polynomial ℂ) (s : Set ℂ)
    (hspectrum : matrixSpectrum B ⊆ s)
    (hq : ∀ z ∈ s, ‖Polynomial.eval z q‖ ≤ 1) :
    matrixSpectrum (polynomialEval q B) ⊆ closedUnitDisk := by
  rw [matrixSpectrum, polynomialEval, spectrum.map_polynomial_aeval]
  rintro w ⟨z, hz, rfl⟩
  simpa [closedUnitDisk, Metric.mem_closedBall, dist_eq_norm] using
    hq z (hspectrum hz)

omit [Nonempty n] in
/-- The normalized perturbation values separate the simple eigenvalues for
the concrete admissible sequence supplied by `Perturbation`. -/
theorem injective_eval_manuscriptPerturbationPolynomial_admissible
    (B : SquareMatrix n) (hB : HasDistinctEigenvalues B)
    (p : Polynomial ℂ) {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    Function.Injective (fun i ↦
      Polynomial.eval
        ((simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues i)
        (manuscriptPerturbationPolynomial R p
          (admissiblePerturbation
            (F := fun j ↦ Polynomial.eval
              ((simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues j) p)
            (simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues_injective k))) := by
  let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues B hB
  let F : n → ℂ := fun i ↦ Polynomial.eval (hdiag.eigenvalues i) p
  let η := admissiblePerturbation (F := F) hdiag.eigenvalues_injective k
  have hinjective : Function.Injective
      (fun i ↦ F i + η * hdiag.eigenvalues i) :=
    injective_admissiblePerturbation hdiag.eigenvalues_injective k
  intro i j hij
  apply hinjective
  apply mul_left_cancel₀ (manuscriptPerturbationScale_ne_zero η hR)
  simpa only [manuscriptPerturbationPolynomial,
    eval_scaledAffinePerturbationPolynomial] using hij

/-- Manuscript lines 375--423 for a fixed simple-spectrum matrix.  The set
`s` represents `closure Ω`; `M` and `R` are respectively the asserted sup
bound for `p` and radius bound for `s`.  The only double-layer input is
`HasDoubleLayerCompletionProvider`, while `hCompletion` is exactly the
previous positive-real completion lemma. -/
theorem norm_polynomialEval_le_two_mul_of_simpleSpectrum
    (B : SquareMatrix n) (hB : HasDistinctEigenvalues B)
    (p : Polynomial ℂ) (s : Set ℂ) (M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hspectrum : matrixSpectrum B ⊆ s)
    (hp : ∀ z ∈ s, ‖Polynomial.eval z p‖ ≤ M)
    (hz : ∀ z ∈ s, ‖z‖ ≤ R)
    (hDoubleLayer : HasDoubleLayerCompletionProvider B s)
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    ‖polynomialEval p B‖ ≤ 2 * M := by
  rcases hM.eq_or_lt with rfl | hMpos
  · rw [polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero B hB p s hspectrum hp]
    simp
  · let c : ℂ := ((M : ℂ))⁻¹
    let f : Polynomial ℂ := Polynomial.C c * p
    let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues B hB
    let F : n → ℂ := fun i ↦ Polynomial.eval (hdiag.eigenvalues i) f
    let η : ℕ → ℂ := admissiblePerturbation (F := F) hdiag.eigenvalues_injective
    have hf : ∀ z ∈ s, ‖Polynomial.eval z f‖ ≤ 1 := by
      intro z hzs
      rw [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
      exact (inv_mul_le_one₀ hMpos).mpr (hp z hzs)
    have hη : Tendsto η atTop (nhds 0) :=
      tendsto_admissiblePerturbation_zero hdiag.eigenvalues_injective
    have hBound : ∀ k : ℕ,
        ‖polynomialEval (manuscriptPerturbationPolynomial R f (η k)) B‖ ≤ 2 := by
      intro k
      let q := manuscriptPerturbationPolynomial R f (η k)
      have hq : ∀ z ∈ s, ‖Polynomial.eval z q‖ ≤ 1 := by
        intro z hzs
        simpa only [q, manuscriptPerturbationPolynomial,
          eval_scaledAffinePerturbationPolynomial, c, f,
          normalizedLinearPerturbation, div_eq_inv_mul] using
          norm_normalizedLinearPerturbation_le_one hR hf hz (η k) hzs
      have hsep : Function.Injective (fun i ↦
          Polynomial.eval (hdiag.eigenvalues i) q) := by
        exact injective_eval_manuscriptPerturbationPolynomial_admissible B hB f hR k
      have hsimple : HasDistinctEigenvalues (polynomialEval q B) :=
        hasDistinctEigenvalues_polynomialEval_of_simpleDiagonalization hdiag q hsep
      have halgebra : generatedAlgebra (polynomialEval q B) = generatedAlgebra B :=
        generatedAlgebra_polynomialEval_eq_of_simpleDiagonalization hdiag q hsep
      have hspectral : matrixSpectrum (polynomialEval q B) ⊆ closedUnitDisk :=
        matrixSpectrum_polynomialEval_subset_closedUnitDisk B q s hspectrum hq
      obtain ⟨H, hH⟩ := hDoubleLayer q hq halgebra
      exact hCompletion (polynomialEval q B) H hsimple hspectral hH
    have hnormalized : ‖polynomialEval f B‖ ≤ 2 := by
      exact norm_polynomialEval_le_of_tendsto_manuscriptPerturbation
        R f B hη (Filter.Eventually.of_forall hBound)
    have heval : polynomialEval f B = c • polynomialEval p B := by
      simp [f, c, polynomialEval, Algebra.smul_def]
    rw [heval, norm_smul] at hnormalized
    dsimp only [c] at hnormalized
    rw [norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hMpos] at hnormalized
    exact (div_le_iff₀ hMpos).mp (by simpa [div_eq_inv_mul] using hnormalized)

end CrouzeixConjecture
