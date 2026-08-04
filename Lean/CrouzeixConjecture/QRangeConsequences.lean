module

public import CrouzeixConjecture.QRangeDisks

@[expose] public section

noncomputable section

open Set
open scoped Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]

/-- Nesting for arbitrary nonzero complex parameters, obtained by combining phase
reduction with the real-parameter disk-union theorem. -/
theorem scaledQNumericalRange_antitone_norm
    {q s : ℂ} (hq0 : q ≠ 0) (hs0 : s ≠ 0)
    (hqs : ‖q‖ ≤ ‖s‖) (hs1 : ‖s‖ ≤ 1) (A : SquareMatrix n) :
    scaledQNumericalRange s A ⊆ scaledQNumericalRange q A := by
  rw [scaledQNumericalRange_eq_norm hs0 A,
    scaledQNumericalRange_eq_norm hq0 A]
  exact scaledQNumericalRange_antitone
    (norm_pos_iff.mpr hq0) hqs hs1 A

/-- The ordinary numerical range lies in every nondegenerate scaled `q`-range. -/
theorem numericalRange_subset_scaledQNumericalRange
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1) (A : SquareMatrix n) :
    numericalRange A ⊆ scaledQNumericalRange q A := by
  rw [scaledQNumericalRange_eq_norm hq0 A]
  have h := scaledQNumericalRange_antitone
    (norm_pos_iff.mpr hq0) hq1 le_rfl A
  norm_num at h
  rw [scaledQNumericalRange_one] at h
  exact h

/-- Consequently, every scaled `q`-range in the manuscript contains the matrix spectrum. -/
theorem matrixSpectrum_subset_scaledQNumericalRange
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ ≤ 1) (A : SquareMatrix n) :
    matrixSpectrum A ⊆ scaledQNumericalRange q A := by
  exact (matrixSpectrum_subset_numericalRange A).trans
    (numericalRange_subset_scaledQNumericalRange hq0 hq1 A)

end CrouzeixConjecture
