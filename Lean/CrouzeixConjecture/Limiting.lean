module

public import CrouzeixConjecture.SimpleSpectrum
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

noncomputable section

open Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix polynomial evaluation is continuous in its matrix argument. -/
theorem tendsto_polynomialEval {ι : Type*} {l : Filter ι} (p : Polynomial ℂ)
    {B : ι → SquareMatrix n} {A : SquareMatrix n} (hB : Tendsto B l (𝓝 A)) :
    Tendsto (fun k ↦ polynomialEval p (B k)) l (𝓝 (polynomialEval p A)) := by
  simpa only [polynomialEval] using (p.continuous_aeval.tendsto A).comp hB

/-- An eventual uniform bound on `‖p(B k)‖` is preserved when `B k` tends to
`A`.  This is the abstract topological limiting step used at the end of the
manuscript. -/
theorem norm_polynomialEval_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (p : Polynomial ℂ) {B : ι → SquareMatrix n} {A : SquareMatrix n} {C : ℝ}
    (hB : Tendsto B l (𝓝 A))
    (hBound : ∀ᶠ k in l, ‖polynomialEval p (B k)‖ ≤ C) :
    ‖polynomialEval p A‖ ≤ C := by
  exact le_of_tendsto (tendsto_polynomialEval p hB).norm hBound

/-- Sequence form of `norm_polynomialEval_le_of_tendsto`. -/
theorem norm_polynomialEval_le_of_tendsto_atTop (p : Polynomial ℂ)
    {B : ℕ → SquareMatrix n} {A : SquareMatrix n} {C : ℝ}
    (hB : Tendsto B atTop (𝓝 A))
    (hBound : ∀ᶠ k in atTop, ‖polynomialEval p (B k)‖ ≤ C) :
    ‖polynomialEval p A‖ ≤ C := by
  exact norm_polynomialEval_le_of_tendsto p hB hBound

/-- Exact evaluation formula for the normalized perturbation
`(p(z) + η z) / (1 + ‖η‖ R)` appearing in the manuscript. -/
theorem polynomialEval_manuscriptPerturbationPolynomial
    (R : ℝ) (p : Polynomial ℂ) (η : ℂ) (B : SquareMatrix n) :
    polynomialEval (manuscriptPerturbationPolynomial R p η) B =
      (((1 + ‖η‖ * R : ℝ) : ℂ)⁻¹) • (polynomialEval p B + η • B) := by
  simp [polynomialEval, manuscriptPerturbationPolynomial,
    scaledAffinePerturbationPolynomial, affinePerturbationPolynomial, Algebra.smul_def]

/-- The normalization factor `(1 + ‖η‖ R)⁻¹` tends to one as `η → 0`. -/
theorem tendsto_manuscriptPerturbationScale (R : ℝ) :
    Tendsto (fun η : ℂ ↦ (((1 + ‖η‖ * R : ℝ) : ℂ)⁻¹)) (𝓝 0) (𝓝 1) := by
  have hnorm : Tendsto (fun η : ℂ ↦ ‖η‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ℂ))
  have hreal : Tendsto (fun η : ℂ ↦ 1 + ‖η‖ * R) (𝓝 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hnorm.mul_const R)
  have hcomplex :
      Tendsto (fun η : ℂ ↦ ((1 + ‖η‖ * R : ℝ) : ℂ)) (𝓝 0) (𝓝 1) := by
    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hreal
  simpa using hcomplex.inv₀ one_ne_zero

/-- For a fixed matrix, evaluation of the exact normalized perturbation tends
to the unperturbed polynomial evaluation as `η → 0`. -/
theorem tendsto_polynomialEval_manuscriptPerturbationPolynomial
    (R : ℝ) (p : Polynomial ℂ) (B : SquareMatrix n) :
    Tendsto
      (fun η : ℂ ↦ polynomialEval (manuscriptPerturbationPolynomial R p η) B)
      (𝓝 0) (𝓝 (polynomialEval p B)) := by
  have hinner :
      Tendsto (fun η : ℂ ↦ polynomialEval p B + η • B) (𝓝 0)
        (𝓝 (polynomialEval p B)) := by
    have hηB : Tendsto (fun η : ℂ ↦ η • B) (𝓝 0) (𝓝 (0 : SquareMatrix n)) := by
      simpa using
        ((tendsto_id : Tendsto (fun η : ℂ ↦ η) (𝓝 0) (𝓝 0)).smul_const B)
    simpa using tendsto_const_nhds.add hηB
  have hnormalized := (tendsto_manuscriptPerturbationScale R).smul hinner
  simpa only [polynomialEval_manuscriptPerturbationPolynomial, one_smul] using hnormalized

/-- Norm convergence for the exact normalized perturbation. -/
theorem tendsto_norm_polynomialEval_manuscriptPerturbationPolynomial
    (R : ℝ) (p : Polynomial ℂ) (B : SquareMatrix n) :
    Tendsto
      (fun η : ℂ ↦ ‖polynomialEval (manuscriptPerturbationPolynomial R p η) B‖)
      (𝓝 0) (𝓝 ‖polynomialEval p B‖) := by
  exact (tendsto_polynomialEval_manuscriptPerturbationPolynomial R p B).norm

/-- An eventual norm bound for the normalized perturbations passes to `p(B)`
at `η = 0`. -/
theorem norm_polynomialEval_le_of_manuscriptPerturbation
    (R : ℝ) (p : Polynomial ℂ) (B : SquareMatrix n) {C : ℝ}
    (hBound : ∀ᶠ η in 𝓝 (0 : ℂ),
      ‖polynomialEval (manuscriptPerturbationPolynomial R p η) B‖ ≤ C) :
    ‖polynomialEval p B‖ ≤ C := by
  exact le_of_tendsto
    (tendsto_norm_polynomialEval_manuscriptPerturbationPolynomial R p B) hBound

/-- Parameterized version of the perturbation limit.  It applies directly to
any net (in particular a sequence of nonexceptional nonzero parameters)
converging to zero. -/
theorem norm_polynomialEval_le_of_tendsto_manuscriptPerturbation
    {ι : Type*} {l : Filter ι} [l.NeBot] (R : ℝ) (p : Polynomial ℂ)
    (B : SquareMatrix n) {η : ι → ℂ} {C : ℝ} (hη : Tendsto η l (𝓝 0))
    (hBound : ∀ᶠ k in l,
      ‖polynomialEval (manuscriptPerturbationPolynomial R p (η k)) B‖ ≤ C) :
    ‖polynomialEval p B‖ ≤ C := by
  apply le_of_tendsto
    ((tendsto_norm_polynomialEval_manuscriptPerturbationPolynomial R p B).comp hη)
  exact hBound

end CrouzeixConjecture
