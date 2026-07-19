module

public import CrouzeixConjecture.Definitions
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace CrouzeixConjecture

/-- The normalized linear perturbation from manuscript line 389. -/
def normalizedLinearPerturbation (f : ℂ → ℂ) (R : ℝ) (η z : ℂ) : ℂ :=
  (f z + η * z) / ((1 + ‖η‖ * R : ℝ) : ℂ)

/-- The normalization in line 389 preserves the unit sup-norm bound. -/
theorem norm_normalizedLinearPerturbation_le_one {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) {s : Set ℂ} (hf : ∀ z ∈ s, ‖f z‖ ≤ 1)
    (hz : ∀ z ∈ s, ‖z‖ ≤ R) (η : ℂ) {z : ℂ} (hmem : z ∈ s) :
    ‖normalizedLinearPerturbation f R η z‖ ≤ 1 := by
  have hden : 0 < 1 + ‖η‖ * R := by positivity
  have hnum : ‖f z + η * z‖ ≤ 1 + ‖η‖ * R := by
    calc
      ‖f z + η * z‖ ≤ ‖f z‖ + ‖η * z‖ := norm_add_le _ _
      _ = ‖f z‖ + ‖η‖ * ‖z‖ := by rw [norm_mul]
      _ ≤ 1 + ‖η‖ * R := by
        exact add_le_add (hf z hmem)
          (mul_le_mul_of_nonneg_left (hz z hmem) (norm_nonneg η))
  rw [normalizedLinearPerturbation, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  exact (div_le_one₀ hden).mpr hnum

/-- Parameters for which the affine perturbation fails to separate the finitely many values. -/
def collisionParameters {ι : Type*} (β F : ι → ℂ) : Set ℂ :=
  {η | ¬Function.Injective (fun i ↦ F i + η * β i)}

/-- If the base points are distinct, only finitely many perturbation parameters cause a
collision. -/
theorem collisionParameters_finite {ι : Type*} [Fintype ι]
    {β F : ι → ℂ} (hβ : Function.Injective β) :
    (collisionParameters β F).Finite := by
  classical
  let candidate : ι × ι → ℂ := fun ij ↦
    (F ij.2 - F ij.1) / (β ij.1 - β ij.2)
  refine (Set.finite_univ.image candidate).subset ?_
  intro η hη
  have hnotInjective : ¬Function.Injective (fun i ↦ F i + η * β i) := hη
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hnotInjective
  refine ⟨(i, j), Set.mem_univ _, ?_⟩
  dsimp [candidate]
  symm
  apply (eq_div_iff (sub_ne_zero.mpr (hβ.ne hij))).2
  linear_combination heq

/-- There are arbitrarily small nonzero parameters for which all perturbed values are distinct. -/
theorem exists_small_injective_perturbation {ι : Type*} [Fintype ι]
    {β F : ι → ℂ} (hβ : Function.Injective β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℂ, η ≠ 0 ∧ ‖η‖ < ε ∧
      Function.Injective (fun i ↦ F i + η * β i) := by
  classical
  have hinfinite : (((fun r : ℝ ↦ (r : ℂ)) '' Set.Ioo 0 ε) : Set ℂ).Infinite :=
    (Set.Ioo_infinite hε).image Complex.ofReal_injective.injOn
  obtain ⟨η, ⟨r, hr, rfl⟩, havoid⟩ :=
    hinfinite.exists_notMem_finite (collisionParameters_finite hβ)
  refine ⟨(r : ℂ), ?_, ?_, ?_⟩
  · exact_mod_cast hr.1.ne'
  · simpa [abs_of_pos hr.1] using hr.2
  · simpa [collisionParameters] using havoid

/-- A concrete choice of the admissible sequence used in lines 398--399. -/
def admissiblePerturbation {ι : Type*} [Fintype ι] {β F : ι → ℂ}
    (hβ : Function.Injective β) (k : ℕ) : ℂ :=
  Classical.choose (exists_small_injective_perturbation (F := F) hβ
    (ε := 1 / (k + 1 : ℝ)) (by positivity))

theorem admissiblePerturbation_ne_zero {ι : Type*} [Fintype ι] {β F : ι → ℂ}
    (hβ : Function.Injective β) (k : ℕ) :
    admissiblePerturbation (F := F) hβ k ≠ 0 :=
  (Classical.choose_spec (exists_small_injective_perturbation (F := F) hβ
    (ε := 1 / (k + 1 : ℝ)) (by positivity))).1

theorem norm_admissiblePerturbation_lt {ι : Type*} [Fintype ι] {β F : ι → ℂ}
    (hβ : Function.Injective β) (k : ℕ) :
    ‖admissiblePerturbation (F := F) hβ k‖ < 1 / (k + 1 : ℝ) :=
  (Classical.choose_spec (exists_small_injective_perturbation (F := F) hβ
    (ε := 1 / (k + 1 : ℝ)) (by positivity))).2.1

theorem injective_admissiblePerturbation {ι : Type*} [Fintype ι] {β F : ι → ℂ}
    (hβ : Function.Injective β) (k : ℕ) :
    Function.Injective (fun i ↦ F i + admissiblePerturbation (F := F) hβ k * β i) :=
  (Classical.choose_spec (exists_small_injective_perturbation (F := F) hβ
    (ε := 1 / (k + 1 : ℝ)) (by positivity))).2.2

/-- The chosen admissible parameters tend to zero. -/
theorem tendsto_admissiblePerturbation_zero {ι : Type*} [Fintype ι] {β F : ι → ℂ}
    (hβ : Function.Injective β) :
    Filter.Tendsto (admissiblePerturbation (F := F) hβ) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun k ↦ norm_nonneg _)
    (fun k ↦ (norm_admissiblePerturbation_lt (F := F) hβ k).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end CrouzeixConjecture
