module

public import CrouzeixConjecture.FunctionMaximum
public import CrouzeixConjecture.HolomorphicDoubleLayer
public import CrouzeixConjecture.HolomorphicFunctionalCalculus
public import CrouzeixConjecture.CanonicalParallelRadialGeometry

@[expose] public section

noncomputable section

open Filter Set
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A totalized `limUnder` value for an arbitrary scalar function.  Under the
holomorphy hypotheses below it is identified with the standard contour calculus. -/
def holomorphicMatrixEval (A : SquareMatrix n) (f : ℂ → ℂ) : SquareMatrix n :=
  limUnder atTop (simpleSpectrumHolomorphicEval A f)

namespace PositivePeriodicRadialData
namespace OrientedRadialConvexBoundary

/-- Every admissible oriented radial contour computes `holomorphicMatrixEval`. -/
theorem parametricBoundaryIntegral_eq_holomorphicMatrixEval
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (A : SquareMatrix n) (hWA : numericalRange A ⊆ Omega) :
    parametricBoundaryIntegral (G.parametricBoundary R c)
        contourParameterMeasure f A = holomorphicMatrixEval A f := by
  have hlimit := G.tendsto_simpleSpectrumHolomorphicEval
    R c hVopen hVconvex hclosure hf A hWA
  symm
  simpa only [holomorphicMatrixEval] using hlimit.limUnder_eq

/-- Under the same admissibility hypotheses, the defining simple-spectrum
sequence tends to `holomorphicMatrixEval`. -/
theorem tendsto_simpleSpectrumHolomorphicEval_to_holomorphicMatrixEval
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hVconvex : Convex ℝ V)
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (A : SquareMatrix n) (hWA : numericalRange A ⊆ Omega) :
    Tendsto (simpleSpectrumHolomorphicEval A f) atTop
      (nhds (holomorphicMatrixEval A f)) := by
  simpa only [G.parametricBoundaryIntegral_eq_holomorphicMatrixEval
    R c hVopen hVconvex hclosure hf A hWA] using
      G.tendsto_simpleSpectrumHolomorphicEval
        R c hVopen hVconvex hclosure hf A hWA

end OrientedRadialConvexBoundary
end PositivePeriodicRadialData

omit [Nonempty n] in
/-- Function evaluation through a simple diagonalization agrees with matrix
polynomial evaluation. -/
theorem SimpleDiagonalization.functionEval_polynomial
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ) :
    hB.functionEval (fun z ↦ Polynomial.eval z p) = polynomialEval p B := by
  rw [hB.polynomialEval_eq_innerConjugation_diagonal]
  rfl

/-- The holomorphic calculus extends the pre-existing polynomial calculus. -/
theorem holomorphicMatrixEval_polynomial
    (A : SquareMatrix n) (p : Polynomial ℂ) :
    holomorphicMatrixEval A (fun z ↦ Polynomial.eval z p) =
      polynomialEval p A := by
  have heq :
      simpleSpectrumHolomorphicEval A (fun z ↦ Polynomial.eval z p) =
        fun k ↦ polynomialEval p (simpleSpectrumApproximation A k) := by
    funext k
    exact (simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)).functionEval_polynomial p
  unfold holomorphicMatrixEval
  rw [heq]
  have hpoly : Tendsto
      (fun k ↦ polynomialEval p (simpleSpectrumApproximation A k)) atTop
      (nhds (polynomialEval p A)) := by
    simpa only [polynomialEval] using
      ((p.continuous_aeval.tendsto A).comp
        (tendsto_simpleSpectrumApproximation A))
  exact hpoly.limUnder_eq

/-- The calculus is local near the numerical range: changing a function away
from an open neighborhood of `W(A)` does not change its value at `A`. -/
theorem holomorphicMatrixEval_congr_on_neighborhood
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ U, f z = g z) :
    holomorphicMatrixEval A f = holomorphicMatrixEval A g := by
  have hinside : ∀ᶠ k in atTop,
      numericalRange (simpleSpectrumApproximation A k) ⊆ U :=
    eventually_simpleSpectrumApproximation_numericalRange_subset_open
      A hUopen hWU
  have heq : simpleSpectrumHolomorphicEval A f =ᶠ[atTop]
      simpleSpectrumHolomorphicEval A g := by
    filter_upwards [hinside] with k hk
    let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)
    change hdiag.functionEval f = hdiag.functionEval g
    unfold SimpleDiagonalization.functionEval
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      apply hfg
      exact hk (matrixSpectrum_subset_numericalRange _
        (hdiag.eigenvalue_mem_matrixSpectrum i))
    · simp [Matrix.diagonal, hij]
  unfold holomorphicMatrixEval
  unfold limUnder
  rw [Filter.map_congr heq]

/-- Holomorphic evaluation is the limit of the concrete simple-spectrum evaluations whenever
the scalar function is holomorphic on a neighborhood of the numerical range. -/
theorem tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    Tendsto (simpleSpectrumHolomorphicEval A f) atTop
      (nhds (holomorphicMatrixEval A f)) := by
  let K := numericalRange A
  have hKcompact : IsCompact K := isCompact_numericalRange A
  obtain ⟨epsilon, hepsilon, hbuffer⟩ :=
    hKcompact.exists_cthickening_subset_open hUopen hWU
  let V := Metric.thickening epsilon K
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVconvex : Convex ℝ V := (numericalRange_convex A).thickening epsilon
  have hVsubsetU : V ⊆ U :=
    (Metric.thickening_subset_cthickening epsilon K).trans hbuffer
  have heventually : ∀ᶠ k in atTop, outerApproximationRadius k < epsilon :=
    (tendsto_order.1 tendsto_outerApproximationRadius).2 epsilon hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  let Omega := parallelOuterDomain K N
  have hclosure : closure Omega ⊆ V := by
    rw [parallelOuterDomain_closure]
    exact Metric.cthickening_subset_thickening' hepsilon (hN N le_rfl) K
  have hWA : numericalRange A ⊆ Omega := by
    exact (parallelOuterDomain_data hKcompact (numericalRange_convex A)
      (numericalRange_nonempty A) N).contains
  obtain ⟨R, c, ⟨G⟩⟩ :=
    canonicalParallelOrientedRadialBoundaryStatement (n := n) A N
  exact G.tendsto_simpleSpectrumHolomorphicEval_to_holomorphicMatrixEval
    R c hVopen hVconvex hclosure (hf.mono hVsubsetU) A hWA

omit [Nonempty n] in
/-- Evaluation through a simple diagonalization preserves pointwise addition. -/
theorem SimpleDiagonalization.functionEval_add
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (f g : ℂ → ℂ) :
    hB.functionEval (fun z ↦ f z + g z) = hB.functionEval f + hB.functionEval g := by
  unfold SimpleDiagonalization.functionEval
  rw [← map_add]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

omit [Nonempty n] in
/-- Evaluation through a simple diagonalization preserves pointwise negation. -/
theorem SimpleDiagonalization.functionEval_neg
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (f : ℂ → ℂ) :
    hB.functionEval (fun z ↦ -f z) = -hB.functionEval f := by
  unfold SimpleDiagonalization.functionEval
  rw [← map_neg]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

omit [Nonempty n] in
/-- Evaluation through a simple diagonalization preserves pointwise multiplication, with the
factor order shown in the conclusion. -/
theorem SimpleDiagonalization.functionEval_mul
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (f g : ℂ → ℂ) :
    hB.functionEval (fun z ↦ f z * g z) = hB.functionEval f * hB.functionEval g := by
  unfold SimpleDiagonalization.functionEval
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.mul_apply, Matrix.diagonal]
  · simp [Matrix.mul_apply, Matrix.diagonal, hij]

/-- The finite-matrix holomorphic calculus preserves addition on a common holomorphic
neighborhood of the numerical range. -/
theorem holomorphicMatrixEval_add
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicMatrixEval A (fun z ↦ f z + g z) =
      holomorphicMatrixEval A f + holomorphicMatrixEval A g := by
  have hfLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hf
  have hgLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hg
  have hsumLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU (hf.add hg)
  have hpointwise :
      simpleSpectrumHolomorphicEval A (fun z ↦ f z + g z) =
        fun k ↦ simpleSpectrumHolomorphicEval A f k +
          simpleSpectrumHolomorphicEval A g k := by
    funext k
    exact (simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)).functionEval_add f g
  change Tendsto (simpleSpectrumHolomorphicEval A (fun z ↦ f z + g z)) atTop
    (nhds (holomorphicMatrixEval A (fun z ↦ f z + g z))) at hsumLimit
  rw [hpointwise] at hsumLimit
  exact tendsto_nhds_unique hsumLimit (hfLimit.add hgLimit)

/-- The finite-matrix holomorphic calculus preserves negation on a holomorphic neighborhood of
the numerical range. -/
theorem holomorphicMatrixEval_neg
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) :
    holomorphicMatrixEval A (fun z ↦ -f z) = -holomorphicMatrixEval A f := by
  have hfLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hf
  have hnegLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hf.neg
  have hpointwise :
      simpleSpectrumHolomorphicEval A (fun z ↦ -f z) =
        fun k ↦ -simpleSpectrumHolomorphicEval A f k := by
    funext k
    exact (simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)).functionEval_neg f
  change Tendsto (simpleSpectrumHolomorphicEval A (fun z ↦ -f z)) atTop
    (nhds (holomorphicMatrixEval A (fun z ↦ -f z))) at hnegLimit
  rw [hpointwise] at hnegLimit
  exact tendsto_nhds_unique hnegLimit hfLimit.neg

/-- The finite-matrix holomorphic calculus preserves subtraction on a common holomorphic
neighborhood of the numerical range. -/
theorem holomorphicMatrixEval_sub
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicMatrixEval A (fun z ↦ f z - g z) =
      holomorphicMatrixEval A f - holomorphicMatrixEval A g := by
  have hadd := holomorphicMatrixEval_add A hUopen hWU hf hg.neg
  have hneg := holomorphicMatrixEval_neg A hUopen hWU hg
  change holomorphicMatrixEval A (-g) = -holomorphicMatrixEval A g at hneg
  calc
    holomorphicMatrixEval A (fun z ↦ f z - g z) =
        holomorphicMatrixEval A f + holomorphicMatrixEval A (-g) := by
      simpa only [sub_eq_add_neg, Pi.neg_apply] using hadd
    _ = holomorphicMatrixEval A f - holomorphicMatrixEval A g := by
      rw [hneg]
      rfl

/-- The finite-matrix holomorphic calculus preserves multiplication on a common holomorphic
neighborhood of the numerical range, including the displayed noncommutative factor order. -/
theorem holomorphicMatrixEval_mul
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    holomorphicMatrixEval A (fun z ↦ f z * g z) =
      holomorphicMatrixEval A f * holomorphicMatrixEval A g := by
  have hfLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hf
  have hgLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU hg
  have hmulLimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hUopen hWU (hf.mul hg)
  have hpointwise :
      simpleSpectrumHolomorphicEval A (fun z ↦ f z * g z) =
        fun k ↦ simpleSpectrumHolomorphicEval A f k *
          simpleSpectrumHolomorphicEval A g k := by
    funext k
    exact (simpleDiagonalization_of_hasDistinctEigenvalues
      (simpleSpectrumApproximation A k)
      (simpleSpectrumApproximation_hasDistinctEigenvalues A k)).functionEval_mul f g
  change Tendsto (simpleSpectrumHolomorphicEval A (fun z ↦ f z * g z)) atTop
    (nhds (holomorphicMatrixEval A (fun z ↦ f z * g z))) at hmulLimit
  rw [hpointwise] at hmulLimit
  exact tendsto_nhds_unique hmulLimit (hfLimit.mul hgLimit)

/-- The normalized holomorphic double-layer estimate scales to an arbitrary
nonnegative scalar bound. -/
theorem norm_functionEval_le_two_mul_of_holomorphic_of_simpleDiagonalization
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : R.OrientedRadialConvexBoundary c Omega)
    (hVopen : IsOpen V) (hclosureCompact : IsCompact (closure Omega))
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ M)
    (B : SquareMatrix n) (hB : SimpleDiagonalization B)
    (hWB : numericalRange B ⊆ Omega) :
    ‖hB.functionEval f‖ ≤ 2 * M := by
  rcases hM.eq_or_lt with rfl | hMpos
  · have hfzero : ∀ i, f (hB.eigenvalues i) = 0 := by
      intro i
      apply norm_eq_zero.mp
      apply le_antisymm
      · apply hbound
        exact subset_closure
          (hWB (matrixSpectrum_subset_numericalRange B
            (hB.eigenvalue_mem_matrixSpectrum i)))
      · exact norm_nonneg _
    have hevalZero : hB.functionEval f = 0 := by
      simp [SimpleDiagonalization.functionEval, hfzero]
    simp [hevalZero]
  · let alpha : ℂ := ((M : ℂ))⁻¹
    let g : ℂ → ℂ := fun z ↦ alpha * f z
    have hg : DifferentiableOn ℂ g V := by
      simpa only [g] using hf.const_mul alpha
    have hgbound : ∀ z ∈ closure Omega, ‖g z‖ ≤ 1 := by
      intro z hz
      dsimp only [g, alpha]
      rw [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hMpos]
      exact (inv_mul_le_one₀ hMpos).mpr (hbound z hz)
    have hnormalized : ‖hB.functionEval g‖ ≤ 2 :=
      G.norm_functionEval_le_two_of_holomorphic_of_simpleDiagonalization
        R c hVopen hclosureCompact hclosure hg hgbound B hB hWB
    have heval : hB.functionEval g = alpha • hB.functionEval f := by
      unfold SimpleDiagonalization.functionEval
      rw [← map_smul]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst j
        simp [g, smul_eq_mul]
      · simp [g, Matrix.diagonal, hij, smul_eq_mul]
    rw [heval, norm_smul] at hnormalized
    dsimp only [alpha] at hnormalized
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hMpos] at hnormalized
    exact (div_le_iff₀ hMpos).mp
      (by simpa [div_eq_inv_mul] using hnormalized)

namespace PositivePeriodicRadialData
namespace OrientedRadialConvexBoundary

/-- On one fixed admissible radial domain, the holomorphic bound passes from
the simple-spectrum approximants to an arbitrary finite matrix. -/
theorem norm_holomorphicMatrixEval_le_two_mul_on_fixedRadialDomain
    (R : PositivePeriodicRadialData) (c : ℂ) {Omega V : Set ℂ}
    (G : OrientedRadialConvexBoundary R c Omega)
    (hVopen : IsOpen V) (hclosureCompact : IsCompact (closure Omega))
    (hclosure : closure Omega ⊆ V)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ closure Omega, ‖f z‖ ≤ M)
    (A : SquareMatrix n) (hWA : numericalRange A ⊆ Omega) :
    ‖holomorphicMatrixEval A f‖ ≤ 2 * M := by
  have hWV : numericalRange A ⊆ V :=
    hWA.trans (subset_closure.trans hclosure)
  have hlimit :=
    tendsto_simpleSpectrumHolomorphicEval_of_differentiableOn_neighborhood
      A hVopen hWV hf
  have hinside : ∀ᶠ k in atTop,
      numericalRange (simpleSpectrumApproximation A k) ⊆ Omega :=
    eventually_simpleSpectrumApproximation_numericalRange_subset_open
      A G.domain.isOpen_domain hWA
  have hestimates : ∀ᶠ k in atTop,
      ‖simpleSpectrumHolomorphicEval A f k‖ ≤ 2 * M := by
    filter_upwards [hinside] with k hk
    exact norm_functionEval_le_two_mul_of_holomorphic_of_simpleDiagonalization
      R c G hVopen hclosureCompact hclosure hf M hM hbound
      (simpleSpectrumApproximation A k)
      (simpleDiagonalization_of_hasDistinctEigenvalues
        (simpleSpectrumApproximation A k)
        (simpleSpectrumApproximation_hasDistinctEigenvalues A k)) hk
  exact le_of_tendsto hlimit.norm hestimates

end OrientedRadialConvexBoundary
end PositivePeriodicRadialData

/-- The standard finite-matrix holomorphic Crouzeix estimate.  Its assumptions
say exactly that `f` is holomorphic on an open neighborhood of `W(A)`. -/
theorem holomorphicCrouzeixBound
    (A : SquareMatrix n) {U : Set ℂ} (hUopen : IsOpen U)
    (hWU : numericalRange A ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ‖holomorphicMatrixEval A f‖ ≤
      2 * maxFunctionModulusOnSet (numericalRange A) f := by
  let K := numericalRange A
  have hKcompact : IsCompact K := isCompact_numericalRange A
  have hKne : K.Nonempty := numericalRange_nonempty A
  have hKconvex : Convex ℝ K := numericalRange_convex A
  obtain ⟨epsilon, hepsilon, hbuffer⟩ :=
    hKcompact.exists_cthickening_subset_open hUopen hWU
  let V := Metric.thickening epsilon K
  let C := Metric.cthickening epsilon K
  have hVopen : IsOpen V := Metric.isOpen_thickening
  have hVconvex : Convex ℝ V := hKconvex.thickening epsilon
  have hVsubsetU : V ⊆ U := by
    exact (Metric.thickening_subset_cthickening epsilon K).trans hbuffer
  have hCcompact : IsCompact C := hKcompact.cthickening
  have hCsubsetU : C ⊆ U := hbuffer
  have hfV : DifferentiableOn ℂ f V := hf.mono hVsubsetU
  have hfC : ContinuousOn f C := hf.continuousOn.mono hCsubsetU
  have heventually : ∀ᶠ k in atTop, outerApproximationRadius k < epsilon :=
    (tendsto_order.1 tendsto_outerApproximationRadius).2 epsilon hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  have hsmall (k : ℕ) : outerApproximationRadius (k + N) < epsilon :=
    hN (k + N) (by omega)
  have hclosureV (k : ℕ) :
      closure (parallelOuterDomain K (k + N)) ⊆ V := by
    rw [parallelOuterDomain_closure]
    exact Metric.cthickening_subset_thickening'
      hepsilon (hsmall k) K
  have hestimate (k : ℕ) :
      ‖holomorphicMatrixEval A f‖ ≤
        2 * maxFunctionModulusOnSet
          (closure (parallelOuterDomain K (k + N))) f := by
    let Omega := parallelOuterDomain K (k + N)
    have hdata := parallelOuterDomain_data hKcompact hKconvex hKne (k + N)
    have hclosureCompact : IsCompact (closure Omega) := hdata.closure_isCompact
    have hclosureNonempty : (closure Omega).Nonempty := hdata.closure_nonempty
    have hfclosure : ContinuousOn f (closure Omega) :=
      hfV.continuousOn.mono (hclosureV k)
    let M := maxFunctionModulusOnSet (closure Omega) f
    have hM : 0 ≤ M :=
      maxFunctionModulusOnSet_nonneg
        hclosureCompact hclosureNonempty hfclosure
    have hpoint : ∀ z ∈ closure Omega, ‖f z‖ ≤ M := by
      intro z hz
      exact norm_function_le_maxFunctionModulusOnSet
        hclosureCompact hclosureNonempty hfclosure hz
    obtain ⟨R, c, ⟨G⟩⟩ :=
      canonicalParallelOrientedRadialBoundaryStatement (n := n) A (k + N)
    exact G.norm_holomorphicMatrixEval_le_two_mul_on_fixedRadialDomain
      R c hVopen hclosureCompact (hclosureV k) hfV M hM hpoint A
      (by simpa only [K, Omega] using hdata.contains)
  have hmax : Tendsto
      (fun k ↦ maxFunctionModulusOnSet
        (closure (parallelOuterDomain K (k + N))) f)
      atTop (nhds (maxFunctionModulusOnSet K f)) := by
    apply tendsto_maxFunctionModulusOnSet_of_outerApproximation
      hKcompact hKne hCcompact hfC
    · intro k
      exact (parallelOuterDomain_data hKcompact hKconvex hKne
        (k + N)).closure_isCompact
    · intro k
      exact (parallelOuterDomain_data hKcompact hKconvex hKne
        (k + N)).contains.trans subset_closure
    · intro k
      rw [parallelOuterDomain_closure]
      exact Metric.cthickening_mono (hsmall k).le K
    · exact tendsto_outerApproximationRadius.comp (tendsto_add_atTop_nat N)
    · intro k z hz
      exact parallelOuterDomain_closure_near hKcompact (k + N) hz
  change ‖holomorphicMatrixEval A f‖ ≤
    2 * maxFunctionModulusOnSet K f
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (hmax.const_mul 2) hestimate

end CrouzeixConjecture
