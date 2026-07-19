module

public import CrouzeixConjecture.Spectrum
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

open scoped Matrix

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by a unit, regarded as an algebra automorphism.  This is the
matrix change-of-basis map used in the manuscript. -/
def innerConjugation (u : (SquareMatrix n)ˣ) :
    SquareMatrix n ≃ₐ[ℂ] SquareMatrix n where
  toFun A := u.val * A * u.inv
  invFun A := u.inv * A * u.val
  left_inv A := by
    simp only [mul_assoc]
    rw [u.inv_val, mul_one, ← mul_assoc, u.inv_val, one_mul]
  right_inv A := by
    simp only [mul_assoc]
    rw [u.val_inv, mul_one, ← mul_assoc, u.val_inv, one_mul]
  map_add' A B := by rw [mul_add, add_mul]
  map_mul' A B := by
    simp only [mul_assoc]
    rw [← mul_assoc u.inv u.val (B * u.inv), u.inv_val, one_mul]
  commutes' z := by
    rw [← Algebra.commutes z (u : SquareMatrix n), mul_assoc, u.val_inv, mul_one]

/-- Explicit simple-spectrum diagonalization data: the matrix is similar to a
diagonal matrix whose diagonal entries are pairwise distinct. -/
structure SimpleDiagonalization (B : SquareMatrix n) where
  eigenvalues : n → ℂ
  changeBasis : (SquareMatrix n)ˣ
  eq_conjugate : B = innerConjugation changeBasis (Matrix.diagonal eigenvalues)
  eigenvalues_injective : Function.Injective eigenvalues

/-- The finite set containing every parameter at which two perturbed values
`values i + η * nodes i` can collide. -/
def exceptionalParameters (nodes values : n → ℂ) : Finset ℂ :=
  (((Finset.univ : Finset n) ×ˢ Finset.univ).filter fun ij ↦ ij.1 ≠ ij.2).image
    fun ij ↦ (values ij.2 - values ij.1) / (nodes ij.1 - nodes ij.2)

/-- The polynomial implementing the manuscript's unnormalised perturbation
`f(z) + η z`. -/
def affinePerturbationPolynomial (p : Polynomial ℂ) (η : ℂ) : Polynomial ℂ :=
  p + Polynomial.C η * Polynomial.X

theorem eval_affinePerturbationPolynomial (p : Polynomial ℂ) (η z : ℂ) :
    Polynomial.eval z (affinePerturbationPolynomial p η) =
      Polynomial.eval z p + η * z := by
  simp only [affinePerturbationPolynomial, Polynomial.eval_add, Polynomial.eval_C_mul,
    Polynomial.eval_X]

/-- Multiplication by a nonzero scalar models the normalising denominator in
`f_η` without changing whether the perturbed eigenvalues are distinct. -/
def scaledAffinePerturbationPolynomial (c : ℂ) (p : Polynomial ℂ) (η : ℂ) :
    Polynomial ℂ :=
  Polynomial.C c * affinePerturbationPolynomial p η

theorem eval_scaledAffinePerturbationPolynomial (c : ℂ) (p : Polynomial ℂ) (η z : ℂ) :
    Polynomial.eval z (scaledAffinePerturbationPolynomial c p η) =
      c * (Polynomial.eval z p + η * z) := by
  rw [scaledAffinePerturbationPolynomial, Polynomial.eval_C_mul,
    eval_affinePerturbationPolynomial]

/-- The exact normalised perturbation polynomial from manuscript equation
`f_η(z) = (f(z) + ηz) / (1 + |η|R)`. -/
def manuscriptPerturbationPolynomial (R : ℝ) (p : Polynomial ℂ) (η : ℂ) :
    Polynomial ℂ :=
  scaledAffinePerturbationPolynomial (((1 + ‖η‖ * R : ℝ) : ℂ)⁻¹) p η

theorem manuscriptPerturbationScale_ne_zero (η : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (((1 + ‖η‖ * R : ℝ) : ℂ)⁻¹) ≠ 0 := by
  apply inv_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  exact (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg η) hR)).ne'

/-- Away from `exceptionalParameters`, perturbation by pairwise distinct nodes
produces pairwise distinct values. -/
theorem perturbedValues_injective_of_not_mem_exceptional
    {nodes values : n → ℂ} (hnodes : Function.Injective nodes) {η : ℂ}
    (hη : η ∉ exceptionalParameters nodes values) :
    Function.Injective (fun i ↦ values i + η * nodes i) := by
  intro i j hij
  by_contra hijne
  have hden : nodes i - nodes j ≠ 0 := sub_ne_zero.mpr (hnodes.ne hijne)
  have heta : η = (values j - values i) / (nodes i - nodes j) := by
    apply (eq_div_iff hden).2
    linear_combination hij
  apply hη
  refine Finset.mem_image.mpr ⟨(i, j), ?_, heta.symm⟩
  refine Finset.mem_filter.mpr ⟨?_, hijne⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩

/-- Equivalently, every parameter producing a collision belongs to the explicit
finite exceptional set. -/
theorem not_injective_perturbedValues_mem_exceptional
    {nodes values : n → ℂ} (hnodes : Function.Injective nodes) {η : ℂ}
    (hη : ¬Function.Injective (fun i ↦ values i + η * nodes i)) :
    η ∈ exceptionalParameters nodes values := by
  by_contra hmem
  exact hη (perturbedValues_injective_of_not_mem_exceptional hnodes hmem)

/-- The set of parameters at which a collision occurs is finite.  This is the
precise “apart from finitely many values of `η`” assertion in lines 392--397. -/
theorem finite_collisionParameters {nodes values : n → ℂ}
    (hnodes : Function.Injective nodes) :
    Set.Finite {η : ℂ | ¬Function.Injective (fun i ↦ values i + η * nodes i)} := by
  refine (exceptionalParameters nodes values).finite_toSet.subset ?_
  intro η hη
  exact not_injective_perturbedValues_mem_exceptional hnodes hη

/-- Lagrange's polynomial interpolating `values` at all of the finite family of
nodes. -/
def interpolationPolynomial (nodes values : n → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ nodes values

/-- The interpolation polynomial has the prescribed value at every node. -/
theorem eval_interpolationPolynomial {nodes values : n → ℂ}
    (hnodes : Function.Injective nodes) (i : n) :
    Polynomial.eval (nodes i) (interpolationPolynomial nodes values) = values i := by
  exact Lagrange.eval_interpolate_at_node values hnodes.injOn (Finset.mem_univ i)

/-- Polynomial evaluation on a diagonal matrix is entrywise scalar evaluation. -/
theorem polynomialEval_diagonal (p : Polynomial ℂ) (nodes : n → ℂ) :
    polynomialEval p (Matrix.diagonal nodes) =
      Matrix.diagonal (fun i ↦ Polynomial.eval (nodes i) p) := by
  calc
    polynomialEval p (Matrix.diagonal nodes) =
        Matrix.diagonal (Polynomial.aeval nodes p) := by
      exact Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℂ) nodes p
    _ = Matrix.diagonal (fun i ↦ Polynomial.eval (nodes i) p) := by
      congr 1
      funext i
      rw [Polynomial.aeval_pi_apply₂]
      exact Polynomial.coe_aeval_eq_eval (nodes i) ▸ rfl

/-- Lagrange interpolation recovers one diagonal matrix as a polynomial in
another whenever the latter's diagonal entries are pairwise distinct. -/
theorem polynomialEval_interpolationPolynomial_diagonal
    {nodes values : n → ℂ} (hnodes : Function.Injective nodes) :
    polynomialEval (interpolationPolynomial nodes values) (Matrix.diagonal nodes) =
      Matrix.diagonal values := by
  rw [polynomialEval_diagonal]
  congr 1
  funext i
  exact eval_interpolationPolynomial hnodes i

/-- Membership of one generator in the other generated algebra gives the
corresponding inclusion of singly generated algebras. -/
theorem generatedAlgebra_le_of_mem {A B : SquareMatrix n}
    (hA : A ∈ generatedAlgebra B) :
    generatedAlgebra A ≤ generatedAlgebra B := by
  exact Algebra.adjoin_singleton_le hA

/-- Mutual generator membership is equivalent to equality of the generated
unital complex matrix algebras. -/
theorem generatedAlgebra_eq_of_mutual_mem {A B : SquareMatrix n}
    (hA : A ∈ generatedAlgebra B) (hB : B ∈ generatedAlgebra A) :
    generatedAlgebra A = generatedAlgebra B := by
  exact le_antisymm (generatedAlgebra_le_of_mem hA) (generatedAlgebra_le_of_mem hB)

/-- If a polynomial separates the eigenvalues in an explicit simple
diagonalization of `B`, Lagrange interpolation gives a polynomial recovering
`B` from that polynomial in `B`. -/
theorem exists_polynomialEval_polynomialEval_eq_of_simpleDiagonalization
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    (hsep : Function.Injective (fun i ↦ Polynomial.eval (hB.eigenvalues i) p)) :
    ∃ q : Polynomial ℂ, polynomialEval q (polynomialEval p B) = B := by
  let q := interpolationPolynomial
    (fun i ↦ Polynomial.eval (hB.eigenvalues i) p) hB.eigenvalues
  refine ⟨q, ?_⟩
  let D := Matrix.diagonal hB.eigenvalues
  let e := innerConjugation hB.changeBasis
  have hdiagonal : polynomialEval q (polynomialEval p D) = D := by
    rw [polynomialEval_diagonal]
    exact polynomialEval_interpolationPolynomial_diagonal hsep
  have hpmap : polynomialEval p (e D) = e (polynomialEval p D) := by
    exact Polynomial.aeval_algHom_apply e D p
  have hqmap : polynomialEval q (e (polynomialEval p D)) =
      e (polynomialEval q (polynomialEval p D)) := by
    exact Polynomial.aeval_algHom_apply e (polynomialEval p D) q
  calc
    polynomialEval q (polynomialEval p B) =
        polynomialEval q (polynomialEval p (e D)) := by
      exact congrArg (fun A ↦ polynomialEval q (polynomialEval p A)) hB.eq_conjugate
    _ = polynomialEval q (e (polynomialEval p D)) := congrArg (polynomialEval q) hpmap
    _ = e (polynomialEval q (polynomialEval p D)) := hqmap
    _ = e D := congrArg e hdiagonal
    _ = B := hB.eq_conjugate.symm

/-- Under the same separation hypothesis, `p(B)` and `B` generate exactly the
same unital complex matrix algebra, as asserted in manuscript lines 403--408. -/
theorem generatedAlgebra_polynomialEval_eq_of_simpleDiagonalization
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    (hsep : Function.Injective (fun i ↦ Polynomial.eval (hB.eigenvalues i) p)) :
    generatedAlgebra (polynomialEval p B) = generatedAlgebra B := by
  obtain ⟨q, hq⟩ :=
    exists_polynomialEval_polynomialEval_eq_of_simpleDiagonalization hB p hsep
  apply generatedAlgebra_eq_of_mutual_mem
  · exact polynomialEval_mem_generatedAlgebra p B
  · simpa only [hq] using
      (polynomialEval_mem_generatedAlgebra q (polynomialEval p B))

/-- Outside the explicit finite exceptional set, the manuscript's affine
perturbation polynomial generates the same algebra as `B`. -/
theorem generatedAlgebra_affinePerturbationPolynomial_eq
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ) {η : ℂ}
    (hη : η ∉ exceptionalParameters hB.eigenvalues
      (fun i ↦ Polynomial.eval (hB.eigenvalues i) p)) :
    generatedAlgebra (polynomialEval (affinePerturbationPolynomial p η) B) =
      generatedAlgebra B := by
  apply generatedAlgebra_polynomialEval_eq_of_simpleDiagonalization hB
  simpa only [eval_affinePerturbationPolynomial] using
    (perturbedValues_injective_of_not_mem_exceptional
      (values := fun i ↦ Polynomial.eval (hB.eigenvalues i) p)
      hB.eigenvalues_injective hη)

/-- A nonzero scalar normalisation preserves the preceding generated-algebra
equality, covering the denominator in the definition of `f_η`. -/
theorem generatedAlgebra_scaledAffinePerturbationPolynomial_eq
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    {c η : ℂ} (hc : c ≠ 0)
    (hη : η ∉ exceptionalParameters hB.eigenvalues
      (fun i ↦ Polynomial.eval (hB.eigenvalues i) p)) :
    generatedAlgebra (polynomialEval (scaledAffinePerturbationPolynomial c p η) B) =
      generatedAlgebra B := by
  apply generatedAlgebra_polynomialEval_eq_of_simpleDiagonalization hB
  have hvalues : Function.Injective
      (fun i ↦ Polynomial.eval (hB.eigenvalues i) p + η * hB.eigenvalues i) :=
    perturbedValues_injective_of_not_mem_exceptional
      (values := fun i ↦ Polynomial.eval (hB.eigenvalues i) p)
      hB.eigenvalues_injective hη
  intro i j hij
  apply hvalues
  apply mul_left_cancel₀ hc
  simpa only [eval_scaledAffinePerturbationPolynomial] using hij

/-- Equation `f_η` has the same generated algebra as `B` for every admissible
parameter when the manuscript's radius `R` is nonnegative. -/
theorem generatedAlgebra_manuscriptPerturbationPolynomial_eq
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    {R : ℝ} (hR : 0 ≤ R) {η : ℂ}
    (hη : η ∉ exceptionalParameters hB.eigenvalues
      (fun i ↦ Polynomial.eval (hB.eigenvalues i) p)) :
    generatedAlgebra (polynomialEval (manuscriptPerturbationPolynomial R p η) B) =
      generatedAlgebra B := by
  exact generatedAlgebra_scaledAffinePerturbationPolynomial_eq hB p
    (manuscriptPerturbationScale_ne_zero η hR) hη

end CrouzeixConjecture
