module

public import CrouzeixConjecture.NumericalRange
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CrouzeixConjecture

/-- Maximum-modulus notation for an arbitrary compact set, represented by the supremum of the
exact value set. -/
def maxPolynomialModulusOnSet (s : Set ℂ) (p : Polynomial ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖Polynomial.eval z p‖) '' s)

/-- The arbitrary-set notation specializes to the manuscript's numerical-range notation. -/
theorem maxPolynomialModulusOnSet_numericalRange
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    maxPolynomialModulusOnSet (numericalRange A) p =
      maxPolynomialModulusOnNumericalRange A p := rfl

/-- A polynomial attains its maximum modulus on a nonempty compact set. -/
theorem exists_maxPolynomialModulusOnSet {s : Set ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (p : Polynomial ℂ) :
    ∃ z ∈ s, ‖Polynomial.eval z p‖ = maxPolynomialModulusOnSet s p := by
  obtain ⟨z, hz, hmax⟩ :=
    hs.exists_isMaxOn hne p.continuous.norm.continuousOn
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖Polynomial.eval w p‖) '' s)
        ‖Polynomial.eval z p‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- Every value on a nonempty compact set is bounded by its attained maximum. -/
theorem norm_polynomial_eval_le_maxOnSet {s : Set ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (p : Polynomial ℂ)
    {z : ℂ} (hz : z ∈ s) :
    ‖Polynomial.eval z p‖ ≤ maxPolynomialModulusOnSet s p := by
  obtain ⟨w, hw, hmax⟩ := hs.exists_isMaxOn hne p.continuous.norm.continuousOn
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖Polynomial.eval y p‖) '' s)
        ‖Polynomial.eval w p‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxPolynomialModulusOnSet, hgreatest.csSup_eq]
  exact hmax hz

/-- A polynomial maximum modulus on a nonempty compact set is nonnegative. -/
theorem maxPolynomialModulusOnSet_nonneg {s : Set ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (p : Polynomial ℂ) :
    0 ≤ maxPolynomialModulusOnSet s p := by
  obtain ⟨z, hz, hmax⟩ := exists_maxPolynomialModulusOnSet hs hne p
  rw [← hmax]
  exact norm_nonneg _

/-- Enlarging a nonempty compact set cannot decrease its polynomial maximum modulus. -/
theorem maxPolynomialModulusOnSet_mono {s t : Set ℂ}
    (hs : IsCompact s) (hsne : s.Nonempty)
    (ht : IsCompact t) (htne : t.Nonempty)
    (hst : s ⊆ t) (p : Polynomial ℂ) :
    maxPolynomialModulusOnSet s p ≤ maxPolynomialModulusOnSet t p := by
  obtain ⟨z, hz, hmax⟩ := exists_maxPolynomialModulusOnSet hs hsne p
  rw [← hmax]
  exact norm_polynomial_eval_le_maxOnSet ht htne p (hst hz)

/-- Polynomial maximum moduli on compact outer approximations converge to the maximum on the
limit set when every point of the approximants is uniformly close to that set.  This is the
precise compactness-and-uniform-continuity step used in the manuscript's outer-domain limit. -/
theorem tendsto_maxPolynomialModulusOnSet_of_outerApproximation
    (p : Polynomial ℂ) {K C : Set ℂ}
    (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hCcompact : IsCompact C)
    {s : ℕ → Set ℂ}
    (hscompact : ∀ k, IsCompact (s k))
    (hKs : ∀ k, K ⊆ s k)
    (hsC : ∀ k, s k ⊆ C)
    (hKC : K ⊆ C)
    {radius : ℕ → ℝ}
    (hradius : Tendsto radius atTop (nhds 0))
    (hclose : ∀ k z, z ∈ s k → ∃ w ∈ K, ‖z - w‖ ≤ radius k) :
    Tendsto (fun k ↦ maxPolynomialModulusOnSet (s k) p) atTop
      (nhds (maxPolynomialModulusOnSet K p)) := by
  let f : ℂ → ℝ := fun z ↦ ‖Polynomial.eval z p‖
  have hfcontinuous : Continuous f := p.continuous.norm
  have hfuniform : UniformContinuousOn f C :=
    hCcompact.uniformContinuousOn_of_continuous hfcontinuous.continuousOn
  refine Metric.tendsto_atTop.2 ?_
  intro η hη
  obtain ⟨δ, hδ, huniform⟩ := Metric.uniformContinuousOn_iff.mp hfuniform η hη
  have heventually : ∀ᶠ k in atTop, radius k < δ :=
    (tendsto_order.1 hradius).2 δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, fun k hk ↦ ?_⟩
  have hskne : (s k).Nonempty := hKne.mono (hKs k)
  have hlower :
      maxPolynomialModulusOnSet K p ≤ maxPolynomialModulusOnSet (s k) p :=
    maxPolynomialModulusOnSet_mono hKcompact hKne (hscompact k) hskne (hKs k) p
  obtain ⟨z, hzs, hzmax⟩ :=
    exists_maxPolynomialModulusOnSet (hscompact k) hskne p
  obtain ⟨w, hwK, hzw⟩ := hclose k z hzs
  have hzw' : dist z w < δ := by
    rw [dist_eq_norm]
    exact hzw.trans_lt (hN k hk)
  have hvalues : dist (f z) (f w) < η :=
    huniform z (hsC k hzs) w (hKC hwK) hzw'
  have hwle : f w ≤ maxPolynomialModulusOnSet K p :=
    norm_polynomial_eval_le_maxOnSet hKcompact hKne p hwK
  have hupper :
      maxPolynomialModulusOnSet (s k) p <
        maxPolynomialModulusOnSet K p + η := by
    rw [← hzmax]
    rw [Real.dist_eq, abs_lt] at hvalues
    exact (sub_lt_iff_lt_add.mp hvalues.2).trans_le
      (by simpa [add_comm] using add_le_add_right hwle η)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end CrouzeixConjecture
