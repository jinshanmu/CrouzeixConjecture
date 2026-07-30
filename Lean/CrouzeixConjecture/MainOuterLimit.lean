module

public import CrouzeixConjecture.MainPerturbationReduction
public import CrouzeixConjecture.CompletionDiagonalization
public import CrouzeixConjecture.Limiting
public import CrouzeixConjecture.NumericalRangeConvexity
public import CrouzeixConjecture.OuterApproximationLimit
public import CrouzeixConjecture.SimpleSpectrumDensity
public import CrouzeixConjecture.SmoothConvexOuterApproximation

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The canonical simple-spectrum perturbation lies strictly inside the corresponding open
parallel body.  This is the containment required by the double-layer support argument, not merely
containment in the closed outer approximation used by the final maximum-modulus limit. -/
theorem numericalRange_simpleSpectrumApproximation_subset_parallelOuterDomain
    (A : SquareMatrix n) (k : ℕ) :
    numericalRange (simpleSpectrumApproximation A k) ⊆
      parallelOuterDomain (numericalRange A) k := by
  intro z hz
  obtain ⟨w, hw, hzw⟩ :=
    numericalRange_perturbation A (simpleSpectrumApproximation A k) hz
  rw [parallelOuterDomain, Metric.mem_thickening_iff]
  refine ⟨w, hw, ?_⟩
  rw [dist_eq_norm]
  exact hzw.trans_lt (by
    simpa only [outerApproximationRadius] using
      norm_simpleSpectrumApproximation_sub_lt A k)

/-- The manuscript's final matrix-and-domain limiting argument, with the analytic double-layer
output kept as its honest input.  Here `B k` are the simple-spectrum perturbations and `s k` are
compact outer domains containing both numerical ranges.  The Hausdorff-style `hclose` hypothesis
is exactly what is needed to pass their scalar maximum moduli to the maximum on `W(A)`. -/
theorem polynomialCrouzeixBound_of_simple_outer_approximants
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (B : ℕ → SquareMatrix n)
    (hBsimple : ∀ k, HasDistinctEigenvalues (B k))
    (hBtends : Tendsto B atTop (nhds A))
    (C : Set ℂ)
    (hCcompact : IsCompact C)
    (s : ℕ → Set ℂ)
    (hscompact : ∀ k, IsCompact (s k))
    (hWAs : ∀ k, numericalRange A ⊆ s k)
    (hWBs : ∀ k, numericalRange (B k) ⊆ s k)
    (hsC : ∀ k, s k ⊆ C)
    (hWAC : numericalRange A ⊆ C)
    (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (nhds 0))
    (hclose : ∀ k z, z ∈ s k →
      ∃ w ∈ numericalRange A, ‖z - w‖ ≤ radius k)
    (hDoubleLayer : ∀ k, HasDoubleLayerCompletionProvider (B k) (s k))
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    PolynomialCrouzeixBound A p := by
  have hsne (k : ℕ) : (s k).Nonempty :=
    (numericalRange_nonempty A).mono (hWAs k)
  have hbound (k : ℕ) :
      ‖polynomialEval p (B k)‖ ≤
        2 * maxPolynomialModulusOnSet (s k) p := by
    apply norm_polynomialEval_le_two_mul_of_simpleSpectrum
      (B k) (hBsimple k) p (s k)
      (maxPolynomialModulusOnSet (s k) p)
    · exact maxPolynomialModulusOnSet_nonneg (hscompact k) (hsne k) p
    · intro z hz
      exact hWBs k (matrixSpectrum_subset_numericalRange (B k) hz)
    · intro z hz
      exact norm_polynomial_eval_le_maxOnSet (hscompact k) (hsne k) p hz
    · exact hDoubleLayer k
    · exact hCompletion
  have hmax :
      Tendsto (fun k ↦ maxPolynomialModulusOnSet (s k) p) atTop
        (nhds (maxPolynomialModulusOnNumericalRange A p)) := by
    simpa only [maxPolynomialModulusOnSet_numericalRange] using
      tendsto_maxPolynomialModulusOnSet_of_outerApproximation
        p (isCompact_numericalRange A) (numericalRange_nonempty A)
        hCcompact hscompact hWAs hsC hWAC hradius hclose
  change ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulusOnNumericalRange A p
  exact le_of_tendsto_of_tendsto'
    (tendsto_polynomialEval p hBtends).norm (hmax.const_mul 2) hbound

/-- Specialization of the final limiting reduction to the concrete simple-spectrum sequence
constructed from the characteristic-resultant argument. -/
theorem polynomialCrouzeixBound_of_outer_approximants
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (C : Set ℂ)
    (hCcompact : IsCompact C)
    (s : ℕ → Set ℂ)
    (hscompact : ∀ k, IsCompact (s k))
    (hWAs : ∀ k, numericalRange A ⊆ s k)
    (hWBs : ∀ k, numericalRange (simpleSpectrumApproximation A k) ⊆ s k)
    (hsC : ∀ k, s k ⊆ C)
    (hWAC : numericalRange A ⊆ C)
    (radius : ℕ → ℝ)
    (hradius : Tendsto radius atTop (nhds 0))
    (hclose : ∀ k z, z ∈ s k →
      ∃ w ∈ numericalRange A, ‖z - w‖ ≤ radius k)
    (hDoubleLayer : ∀ k,
      HasDoubleLayerCompletionProvider (simpleSpectrumApproximation A k) (s k))
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    PolynomialCrouzeixBound A p := by
  exact polynomialCrouzeixBound_of_simple_outer_approximants
    A p (simpleSpectrumApproximation A)
    (simpleSpectrumApproximation_hasDistinctEigenvalues A)
    (tendsto_simpleSpectrumApproximation A)
    C hCcompact s hscompact hWAs hWBs hsC hWAC
    radius hradius hclose hDoubleLayer hCompletion

/-- The canonical parallel bodies discharge every compactness, convexity, containment, and
Hausdorff-limit obligation in the manuscript's final outer-domain step.  What remains in
`hDoubleLayer` is precisely the contour construction for those bounded open convex domains. -/
theorem polynomialCrouzeixBound_of_parallelOuterDomains
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (hconvex : Convex ℝ (numericalRange A))
    (hDoubleLayer : ∀ k,
      HasDoubleLayerCompletionProvider (simpleSpectrumApproximation A k)
        (closure (parallelOuterDomain (numericalRange A) k)))
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    PolynomialCrouzeixBound A p := by
  let K := numericalRange A
  let C := Metric.cthickening 1 K
  have hKcompact : IsCompact K := isCompact_numericalRange A
  have hKne : K.Nonempty := numericalRange_nonempty A
  have hCcompact : IsCompact C := fixedOuterNeighborhood_isCompact hKcompact
  have hscompact (k : ℕ) :
      IsCompact (closure (parallelOuterDomain K k)) :=
    (parallelOuterDomain_data hKcompact hconvex hKne k).closure_isCompact
  have hWAs (k : ℕ) : K ⊆ closure (parallelOuterDomain K k) := by
    exact (parallelOuterDomain_data hKcompact hconvex hKne k).contains.trans subset_closure
  have hWBs (k : ℕ) :
      numericalRange (simpleSpectrumApproximation A k) ⊆
        closure (parallelOuterDomain K k) := by
    exact
      (numericalRange_simpleSpectrumApproximation_subset_parallelOuterDomain A k).trans
        subset_closure
  have hsC (k : ℕ) : closure (parallelOuterDomain K k) ⊆ C :=
    parallelOuterDomain_closure_subset_fixedNeighborhood K k
  have hKC : K ⊆ C := by
    change K ⊆ Metric.cthickening 1 K
    exact Metric.self_subset_cthickening K
  exact polynomialCrouzeixBound_of_outer_approximants
    A p C hCcompact
    (fun k ↦ closure (parallelOuterDomain K k))
    hscompact hWAs hWBs hsC hKC
    outerApproximationRadius tendsto_outerApproximationRadius
    (fun k z hz ↦ parallelOuterDomain_closure_near hKcompact k hz)
    hDoubleLayer hCompletion

/-- The canonical parallel-body reduction with Toeplitz--Hausdorff discharged internally.  Its
only remaining analytic input is the manuscript's double-layer provider on those domains. -/
theorem polynomialCrouzeixBound_of_canonicalParallelOuterDomains
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (hDoubleLayer : ∀ k,
      HasDoubleLayerCompletionProvider (simpleSpectrumApproximation A k)
        (closure (parallelOuterDomain (numericalRange A) k))) :
    PolynomialCrouzeixBound A p :=
  polynomialCrouzeixBound_of_parallelOuterDomains A p
    (numericalRange_convex A) hDoubleLayer positiveRealCompletionStatement

/-- The single remaining global source obligation after all algebraic, convexity,
perturbation, and limiting arguments have been discharged: construct the manuscript's
double-layer completion on every canonical outer parallel domain. -/
def CanonicalParallelDoubleLayerStatement : Prop :=
  ∀ (A : SquareMatrix n) (k : ℕ),
    HasDoubleLayerCompletionProvider (simpleSpectrumApproximation A k)
      (closure (parallelOuterDomain (numericalRange A) k))

/-- The faithful manuscript theorem follows from precisely the canonical contour-provider
statement, with the positive-real completion and Toeplitz--Hausdorff inputs supplied internally. -/
theorem mainTheoremStatement_of_canonicalParallelDoubleLayer
    (hDoubleLayer : CanonicalParallelDoubleLayerStatement (n := n)) :
    MainTheoremStatement (n := n) := by
  intro A p
  exact polynomialCrouzeixBound_of_canonicalParallelOuterDomains A p
    (hDoubleLayer A)

end CrouzeixConjecture
