module

public import CrouzeixConjecture.MainPerturbationReduction
public import CrouzeixConjecture.CompletionDiagonalization
public import CrouzeixConjecture.Limiting
public import CrouzeixConjecture.NumericalRangeConvexity
public import CrouzeixConjecture.OuterApproximationLimit
public import CrouzeixConjecture.PerturbationInsideDomain
public import CrouzeixConjecture.SmoothConvexOuterApproximation

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Fix an open outer domain first, then let simple-spectrum matrices converge to `A`.  This is the
fixed-`ε` order of limits in the simplified proof. -/
theorem norm_polynomialEval_le_two_mul_max_on_fixed_outerDomain
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (B : ℕ → SquareMatrix n)
    (hBsimple : ∀ k, HasDistinctEigenvalues (B k))
    (hBtends : Tendsto B atTop (nhds A))
    (Omega : Set ℂ) (hOmegaOpen : IsOpen Omega)
    (hWA : numericalRange A ⊆ Omega)
    (hclosureCompact : IsCompact (closure Omega))
    (hDoubleLayer : ∀ k, numericalRange (B k) ⊆ Omega →
      HasDoubleLayerCompletionProvider (B k) (closure Omega))
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    ‖polynomialEval p A‖ ≤
      2 * maxPolynomialModulusOnSet (closure Omega) p := by
  have hclosureNonempty : (closure Omega).Nonempty :=
    (numericalRange_nonempty A).mono (hWA.trans subset_closure)
  have hWeventually : ∀ᶠ k in atTop, numericalRange (B k) ⊆ Omega :=
    eventually_numericalRange_subset_open_of_tendsto A hBtends hOmegaOpen hWA
  have hBound : ∀ᶠ k in atTop,
      ‖polynomialEval p (B k)‖ ≤
        2 * maxPolynomialModulusOnSet (closure Omega) p := by
    filter_upwards [hWeventually] with k hWB
    apply norm_polynomialEval_le_two_mul_of_simpleSpectrum
      (B k) (hBsimple k) p (closure Omega)
      (maxPolynomialModulusOnSet (closure Omega) p)
    · exact maxPolynomialModulusOnSet_nonneg hclosureCompact hclosureNonempty p
    · intro z hz
      exact subset_closure (hWB (matrixSpectrum_subset_numericalRange (B k) hz))
    · intro z hz
      exact norm_polynomial_eval_le_maxOnSet hclosureCompact hclosureNonempty p hz
    · exact hDoubleLayer k hWB
    · exact hCompletion
  exact norm_polynomialEval_le_of_tendsto p hBtends hBound

/-- Apply the fixed-domain result to each canonical parallel body, and only afterward shrink the
outer radius to zero. -/
theorem polynomialCrouzeixBound_of_parallelOuterDomains
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (hconvex : Convex ℝ (numericalRange A))
    (hDoubleLayer : ∀ k j,
      numericalRange (simpleSpectrumApproximation A j) ⊆
          parallelOuterDomain (numericalRange A) k →
        HasDoubleLayerCompletionProvider (simpleSpectrumApproximation A j)
          (closure (parallelOuterDomain (numericalRange A) k)))
    (hCompletion : PositiveRealCompletionStatement (n := n)) :
    PolynomialCrouzeixBound A p := by
  let K := numericalRange A
  let C := Metric.cthickening 1 K
  have hKcompact : IsCompact K := isCompact_numericalRange A
  have hKne : K.Nonempty := numericalRange_nonempty A
  have hCcompact : IsCompact C := fixedOuterNeighborhood_isCompact hKcompact
  have hbound (k : ℕ) :
      ‖polynomialEval p A‖ ≤
        2 * maxPolynomialModulusOnSet (closure (parallelOuterDomain K k)) p := by
    apply norm_polynomialEval_le_two_mul_max_on_fixed_outerDomain
      A p (simpleSpectrumApproximation A)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A)
      (tendsto_simpleSpectrumApproximation A)
      (parallelOuterDomain K k)
    · exact Metric.isOpen_thickening
    · exact (parallelOuterDomain_data hKcompact hconvex hKne k).contains
    · exact (parallelOuterDomain_data hKcompact hconvex hKne k).closure_isCompact
    · intro j hWB
      exact hDoubleLayer k j hWB
    · exact hCompletion
  have hmax : Tendsto
      (fun k ↦ maxPolynomialModulusOnSet (closure (parallelOuterDomain K k)) p)
      atTop (nhds (maxPolynomialModulusOnNumericalRange A p)) := by
    simpa only [K, maxPolynomialModulusOnSet_numericalRange] using
      tendsto_maxPolynomialModulusOnSet_of_outerApproximation
        p hKcompact hKne hCcompact
        (fun k ↦ (parallelOuterDomain_data hKcompact hconvex hKne k).closure_isCompact)
        (fun k ↦
          (parallelOuterDomain_data hKcompact hconvex hKne k).contains.trans subset_closure)
        (fun k ↦ parallelOuterDomain_closure_subset_fixedNeighborhood K k)
        (by
          change K ⊆ Metric.cthickening 1 K
          exact Metric.self_subset_cthickening K)
        tendsto_outerApproximationRadius
        (fun k z hz ↦ parallelOuterDomain_closure_near hKcompact k hz)
  change ‖polynomialEval p A‖ ≤ 2 * maxPolynomialModulusOnNumericalRange A p
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hmax.const_mul 2) hbound

/-- For a fixed outer parallel body, every simple-spectrum auxiliary matrix lying inside it has
the required double-layer completion.  The auxiliary matrix is deliberately independent of the
outer-domain index, matching the fixed-`ε` proof. -/
def CanonicalParallelDoubleLayerStatement : Prop :=
  ∀ (A B : SquareMatrix n) (k : ℕ),
    HasDistinctEigenvalues B →
    numericalRange B ⊆ parallelOuterDomain (numericalRange A) k →
    HasDoubleLayerCompletionProvider B
      (closure (parallelOuterDomain (numericalRange A) k))

/-- The canonical parallel-body reduction with Toeplitz--Hausdorff and the positive-real
completion theorem supplied internally. -/
theorem polynomialCrouzeixBound_of_canonicalParallelOuterDomains
    (A : SquareMatrix n) (p : Polynomial ℂ)
    (hDoubleLayer : CanonicalParallelDoubleLayerStatement (n := n)) :
    PolynomialCrouzeixBound A p :=
  polynomialCrouzeixBound_of_parallelOuterDomains A p
    (numericalRange_convex A)
    (fun k j hWB ↦ hDoubleLayer A (simpleSpectrumApproximation A j) k
      (simpleSpectrumApproximation_hasDistinctEigenvalues A j) hWB)
    positiveRealCompletionStatement

/-- The faithful manuscript theorem follows from precisely the canonical contour-provider
statement, with the positive-real completion and Toeplitz--Hausdorff inputs supplied internally. -/
theorem mainTheoremStatement_of_canonicalParallelDoubleLayer
    (hDoubleLayer : CanonicalParallelDoubleLayerStatement (n := n)) :
    MainTheoremStatement (n := n) := by
  intro A p
  exact polynomialCrouzeixBound_of_canonicalParallelOuterDomains A p
    hDoubleLayer

end CrouzeixConjecture
