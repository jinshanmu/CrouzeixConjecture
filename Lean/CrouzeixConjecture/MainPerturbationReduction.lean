module

public import CrouzeixConjecture.SimpleSpectrumBridge
public import CrouzeixConjecture.CompletionStatement
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The exact analytic output from the double-layer construction used for a
simple-spectrum auxiliary matrix.  Only the unit sup-norm bound is required:
the completion is relative to `B`, while its target is the possibly
non-simple matrix `q(B)`.  In particular, this proposition does not contain a
norm estimate for the evaluated matrix. -/
def HasDoubleLayerCompletionProvider (B : SquareMatrix n) (s : Set ℂ) : Prop :=
  ∀ q : Polynomial ℂ,
    (∀ z ∈ s, ‖Polynomial.eval z q‖ ≤ 1) →
    ∃ H : ℂ → SquareMatrix n,
      IsPositiveRealCompletion B (polynomialEval q B) H

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
spectrum of `B` into the closed-unit-disk hypothesis used by the double-layer
Cayley-series construction. -/
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
/-- The simplified fixed-simple-spectrum argument.  After the zero branch,
normalize `p` directly by its scalar supremum.  Polynomial functional calculus
keeps `f(B)` diagonal in the simple auxiliary matrix's eigenbasis, even when
the values of `f` at distinct eigenvalues coincide, so no secondary
`η`-perturbation or generated-algebra equality is needed. -/
theorem norm_polynomialEval_le_two_mul_of_simpleSpectrum
    (B : SquareMatrix n) (hB : HasDistinctEigenvalues B)
    (p : Polynomial ℂ) (s : Set ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hspectrum : matrixSpectrum B ⊆ s)
    (hp : ∀ z ∈ s, ‖Polynomial.eval z p‖ ≤ M)
    (hDoubleLayer : HasDoubleLayerCompletionProvider B s)
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    ‖polynomialEval p B‖ ≤ 2 * M := by
  rcases hM.eq_or_lt with rfl | hMpos
  · rw [polynomialEval_eq_zero_of_simpleSpectrum_of_bound_zero B hB p s hspectrum hp]
    simp
  · let c : ℂ := ((M : ℂ))⁻¹
    let f : Polynomial ℂ := Polynomial.C c * p
    let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues B hB
    let lambda : n → ℂ := fun i ↦ Polynomial.eval (hdiag.eigenvalues i) f
    have hf : ∀ z ∈ s, ‖Polynomial.eval z f‖ ≤ 1 := by
      intro z hzs
      rw [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
      exact (inv_mul_le_one₀ hMpos).mpr (hp z hzs)
    have heigenvalue (i : n) : hdiag.eigenvalues i ∈ matrixSpectrum B := by
      let D := Matrix.diagonal hdiag.eigenvalues
      have hchar : B.charpoly = D.charpoly := by
        calc
          B.charpoly = (innerConjugation hdiag.changeBasis D).charpoly :=
            congrArg Matrix.charpoly hdiag.eq_conjugate
          _ = D.charpoly := by
            change (hdiag.changeBasis.val * D * hdiag.changeBasis.inv).charpoly =
              D.charpoly
            simpa only [Units.inv_eq_val_inv] using
              Matrix.charpoly_units_conj hdiag.changeBasis D
      apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      rw [hchar, Matrix.charpoly_diagonal]
      exact (Polynomial.isRoot_prod Finset.univ
        (fun j ↦ Polynomial.X - Polynomial.C (hdiag.eigenvalues j))
        (hdiag.eigenvalues i)).mpr ⟨i, Finset.mem_univ i, by simp⟩
    have hlambda : ∀ i, ‖lambda i‖ ≤ 1 := by
      intro i
      exact hf (hdiag.eigenvalues i) (hspectrum (heigenvalue i))
    have htarget :
        polynomialEval f B =
          innerConjugation hdiag.changeBasis (Matrix.diagonal lambda) := by
      simpa only [lambda] using
        hdiag.polynomialEval_eq_innerConjugation_diagonal f
    obtain ⟨H, hH⟩ := hDoubleLayer f hf
    have hnormalized : ‖polynomialEval f B‖ ≤ 2 :=
      hCompletion B (polynomialEval f B) H hdiag lambda htarget hlambda hH
    have heval : polynomialEval f B = c • polynomialEval p B := by
      simp [f, c, polynomialEval, Algebra.smul_def]
    rw [heval, norm_smul] at hnormalized
    dsimp only [c] at hnormalized
    rw [norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hMpos] at hnormalized
    exact (div_le_iff₀ hMpos).mp (by simpa [div_eq_inv_mul] using hnormalized)

end CrouzeixConjecture
