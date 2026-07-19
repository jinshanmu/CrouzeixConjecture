module

public import CrouzeixConjecture.CompletionStatement
public import CrouzeixConjecture.SimpleSpectrum
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

noncomputable section

open scoped Matrix
open Module

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The project predicate based on noduplicity of the characteristic roots
supplies the explicit simple diagonalization used in the manuscript. -/
def simpleDiagonalization_of_hasDistinctEigenvalues (B : SquareMatrix n)
    (hB : HasDistinctEigenvalues B) :
    SimpleDiagonalization B := by
  classical
  let standard : Basis n ℂ (n → ℂ) := Pi.basisFun ℂ n
  let f : Module.End ℂ (n → ℂ) := Matrix.toLin standard standard B
  let roots : Finset ℂ := B.charpoly.roots.toFinset
  have hsplits : B.charpoly.Splits := IsAlgClosed.splits B.charpoly
  have hrootsCard : roots.card = Fintype.card n := by
    calc
      roots.card = B.charpoly.roots.card := by
        exact Multiset.toFinset_card_of_nodup hB
      _ = B.charpoly.natDegree := hsplits.natDegree_eq_card_roots.symm
      _ = Fintype.card n := Matrix.charpoly_natDegree_eq_dim B
  let rootEquiv : n ≃ ↥roots := Fintype.equivOfCardEq (by simpa using hrootsCard.symm)
  let eigenvalues : n → ℂ := fun i ↦ rootEquiv i
  have heigenvalues : Function.Injective eigenvalues := by
    intro i j hij
    apply rootEquiv.injective
    exact Subtype.ext hij
  have hroot (i : n) : eigenvalues i ∈ B.charpoly.roots := by
    change (rootEquiv i : ℂ) ∈ B.charpoly.roots
    exact Multiset.mem_toFinset.mp (rootEquiv i).property
  have hfcharpoly : f.charpoly = B.charpoly := by
    exact Matrix.charpoly_toLin B standard
  have heigenvalue (i : n) : f.HasEigenvalue (eigenvalues i) := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly f (eigenvalues i)).2
    rw [hfcharpoly]
    exact Polynomial.isRoot_of_mem_roots (hroot i)
  choose eigenvector heigenvector using fun i ↦ (heigenvalue i).exists_hasEigenvector
  have heigenvectorIndependent : LinearIndependent ℂ eigenvector :=
    f.eigenvectors_linearIndependent' eigenvalues heigenvalues eigenvector heigenvector
  let eigenbasis : Basis n ℂ (n → ℂ) :=
    basisOfPiSpaceOfLinearIndependent heigenvectorIndependent
  have heigenbasis (i : n) : eigenbasis i = eigenvector i := by
    exact congrFun (coe_basisOfPiSpaceOfLinearIndependent heigenvectorIndependent) i
  have hfEigenbasis (i : n) :
      f (eigenbasis i) = eigenvalues i • eigenbasis i := by
    rw [heigenbasis i]
    exact (heigenvector i).apply_eq_smul
  have hdiagonal :
      LinearMap.toMatrix eigenbasis eigenbasis f = Matrix.diagonal eigenvalues := by
    ext i j
    rw [LinearMap.toMatrix_apply, hfEigenbasis j]
    by_cases hij : i = j
    · subst i
      simp
    · simp [Matrix.diagonal, hij]
  let changeBasis : (SquareMatrix n)ˣ :=
    { val := standard.toMatrix eigenbasis
      inv := eigenbasis.toMatrix standard
      val_inv := Module.Basis.toMatrix_mul_toMatrix_flip standard eigenbasis
      inv_val := Module.Basis.toMatrix_mul_toMatrix_flip eigenbasis standard }
  refine
    { eigenvalues := eigenvalues
      changeBasis := changeBasis
      eigenvalues_injective := heigenvalues
      eq_conjugate := ?_ }
  change B = standard.toMatrix eigenbasis * Matrix.diagonal eigenvalues *
    eigenbasis.toMatrix standard
  calc
    B = LinearMap.toMatrix standard standard f := by
      symm
      exact LinearMap.toMatrix_toLin standard standard B
    _ = standard.toMatrix eigenbasis * LinearMap.toMatrix eigenbasis eigenbasis f *
        eigenbasis.toMatrix standard := by
      exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        standard eigenbasis standard eigenbasis f).symm
    _ = standard.toMatrix eigenbasis * Matrix.diagonal eigenvalues *
        eigenbasis.toMatrix standard := by rw [hdiagonal]

/-- Proposition-valued existence form of
`simpleDiagonalization_of_hasDistinctEigenvalues`. -/
theorem nonempty_simpleDiagonalization_of_hasDistinctEigenvalues (B : SquareMatrix n)
    (hB : HasDistinctEigenvalues B) :
    Nonempty (SimpleDiagonalization B) :=
  ⟨simpleDiagonalization_of_hasDistinctEigenvalues B hB⟩

/-- Conversely, explicit simple diagonalization data certifies noduplicity of
the characteristic roots. -/
theorem hasDistinctEigenvalues_of_simpleDiagonalization
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) :
    HasDistinctEigenvalues B := by
  classical
  have hproduct :
      (Finset.univ.prod fun i : n ↦
        Polynomial.X - Polynomial.C (hB.eigenvalues i)) =
      (Finset.univ.image hB.eigenvalues).prod fun z ↦
        Polynomial.X - Polynomial.C z := by
    exact (Finset.prod_image
      (f := fun z : ℂ ↦ (Polynomial.X - Polynomial.C z : Polynomial ℂ))
      (s := Finset.univ) (g := hB.eigenvalues)
      hB.eigenvalues_injective.injOn).symm
  have hdiagonalRoots :
      (Matrix.diagonal hB.eigenvalues).charpoly.roots =
        (Finset.univ.image hB.eigenvalues).val := by
    rw [Matrix.charpoly_diagonal, hproduct, Polynomial.roots_prod_X_sub_C]
  have hcharpoly :
      B.charpoly = (Matrix.diagonal hB.eigenvalues).charpoly := by
    calc
      B.charpoly =
          (innerConjugation hB.changeBasis
            (Matrix.diagonal hB.eigenvalues)).charpoly :=
        congrArg Matrix.charpoly hB.eq_conjugate
      _ = (Matrix.diagonal hB.eigenvalues).charpoly := by
        change
          (hB.changeBasis.val * Matrix.diagonal hB.eigenvalues *
            hB.changeBasis.inv).charpoly =
            (Matrix.diagonal hB.eigenvalues).charpoly
        simpa only [Units.inv_eq_val_inv] using
          Matrix.charpoly_units_conj hB.changeBasis (Matrix.diagonal hB.eigenvalues)
  change B.charpoly.roots.Nodup
  rw [hcharpoly, hdiagonalRoots]
  exact (Finset.univ.image hB.eigenvalues).nodup

/-- Polynomial functional calculus preserves an explicit diagonalization; if
the polynomial separates the original eigenvalues, the result is again simple. -/
def SimpleDiagonalization.ofPolynomialEval {B : SquareMatrix n}
    (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    (hsep : Function.Injective fun i ↦ Polynomial.eval (hB.eigenvalues i) p) :
    SimpleDiagonalization (polynomialEval p B) := by
  let diagonal := Matrix.diagonal hB.eigenvalues
  let conjugation := innerConjugation hB.changeBasis
  refine
    { eigenvalues := fun i ↦ Polynomial.eval (hB.eigenvalues i) p
      changeBasis := hB.changeBasis
      eigenvalues_injective := hsep
      eq_conjugate := ?_ }
  calc
    polynomialEval p B = polynomialEval p (conjugation diagonal) :=
      congrArg (polynomialEval p) hB.eq_conjugate
    _ = conjugation (polynomialEval p diagonal) := by
      exact Polynomial.aeval_algHom_apply conjugation diagonal p
    _ = conjugation
        (Matrix.diagonal fun i ↦ Polynomial.eval (hB.eigenvalues i) p) := by
      exact congrArg conjugation (polynomialEval_diagonal p hB.eigenvalues)

/-- A polynomial separating the eigenvalues of a simple diagonalization has
distinct characteristic roots. -/
theorem hasDistinctEigenvalues_polynomialEval_of_simpleDiagonalization
    {B : SquareMatrix n} (hB : SimpleDiagonalization B) (p : Polynomial ℂ)
    (hsep : Function.Injective fun i ↦ Polynomial.eval (hB.eigenvalues i) p) :
    HasDistinctEigenvalues (polynomialEval p B) := by
  exact hasDistinctEigenvalues_of_simpleDiagonalization (hB.ofPolynomialEval p hsep)

/-- The Lagrange-interpolation algebra equality can therefore be invoked from
the project's root-based distinct-eigenvalues predicate alone. -/
theorem generatedAlgebra_polynomialEval_eq_of_hasDistinctEigenvalues
    {B : SquareMatrix n} (hB : HasDistinctEigenvalues B) (p : Polynomial ℂ)
    (hsep : Function.Injective fun i ↦
      Polynomial.eval ((simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues i) p) :
    generatedAlgebra (polynomialEval p B) = generatedAlgebra B := by
  exact generatedAlgebra_polynomialEval_eq_of_simpleDiagonalization
    (simpleDiagonalization_of_hasDistinctEigenvalues B hB) p hsep

/-- The exact normalized perturbation from manuscript equation `f_η` generates
the same algebra as a matrix satisfying the project's distinct-root predicate,
outside the explicit finite collision set. -/
theorem generatedAlgebra_manuscriptPerturbation_eq_of_hasDistinctEigenvalues
    {B : SquareMatrix n} (hB : HasDistinctEigenvalues B) (p : Polynomial ℂ)
    {R : ℝ} (hR : 0 ≤ R) {η : ℂ}
    (hη : η ∉ exceptionalParameters
      (simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues
      (fun i ↦ Polynomial.eval
        ((simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues i) p)) :
    generatedAlgebra (polynomialEval (manuscriptPerturbationPolynomial R p η) B) =
      generatedAlgebra B := by
  exact generatedAlgebra_manuscriptPerturbationPolynomial_eq
    (simpleDiagonalization_of_hasDistinctEigenvalues B hB) p hR hη

/-- For every admissible parameter, the exact normalized perturbation also
satisfies the project's original characteristic-root predicate. -/
theorem hasDistinctEigenvalues_manuscriptPerturbation
    {B : SquareMatrix n} (hB : HasDistinctEigenvalues B) (p : Polynomial ℂ)
    {R : ℝ} (hR : 0 ≤ R) {η : ℂ}
    (hη : η ∉ exceptionalParameters
      (simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues
      (fun i ↦ Polynomial.eval
        ((simpleDiagonalization_of_hasDistinctEigenvalues B hB).eigenvalues i) p)) :
    HasDistinctEigenvalues
      (polynomialEval (manuscriptPerturbationPolynomial R p η) B) := by
  let hdiag := simpleDiagonalization_of_hasDistinctEigenvalues B hB
  have hunscaled : Function.Injective
      (fun i ↦ Polynomial.eval (hdiag.eigenvalues i) p + η * hdiag.eigenvalues i) :=
    perturbedValues_injective_of_not_mem_exceptional
      (values := fun i ↦ Polynomial.eval (hdiag.eigenvalues i) p)
      hdiag.eigenvalues_injective hη
  apply hasDistinctEigenvalues_polynomialEval_of_simpleDiagonalization hdiag
  intro i j hij
  apply hunscaled
  apply mul_left_cancel₀ (manuscriptPerturbationScale_ne_zero η hR)
  simpa only [manuscriptPerturbationPolynomial,
    eval_scaledAffinePerturbationPolynomial] using hij

end CrouzeixConjecture
