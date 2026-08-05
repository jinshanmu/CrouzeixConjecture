module

public import CrouzeixConjecture.SmoothConvexOuterApproximation
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CrouzeixConjecture

/-- Maximum-modulus notation for a scalar function on an arbitrary set. -/
def maxFunctionModulusOnSet (s : Set ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' s)

/-- A continuous scalar function attains its maximum modulus on a nonempty compact set. -/
theorem exists_maxFunctionModulusOnSet {s : Set ℂ} {f : ℂ → ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ z ∈ s, ‖f z‖ = maxFunctionModulusOnSet s f := by
  obtain ⟨z, hz, hmax⟩ := hs.exists_isMaxOn hne hf.norm
  refine ⟨z, hz, ?_⟩
  have hgreatest :
      IsGreatest ((fun w : ℂ ↦ ‖f w‖) '' s) ‖f z‖ := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmax hw
  exact hgreatest.csSup_eq.symm

/-- Every value is bounded by the attained maximum modulus. -/
theorem norm_function_le_maxFunctionModulusOnSet {s : Set ℂ} {f : ℂ → ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s)
    {z : ℂ} (hz : z ∈ s) :
    ‖f z‖ ≤ maxFunctionModulusOnSet s f := by
  obtain ⟨w, hw, hmax⟩ := hs.exists_isMaxOn hne hf.norm
  have hgreatest :
      IsGreatest ((fun y : ℂ ↦ ‖f y‖) '' s) ‖f w‖ := by
    refine ⟨⟨w, hw, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  rw [maxFunctionModulusOnSet, hgreatest.csSup_eq]
  exact hmax hz

/-- The maximum modulus on a nonempty compact set is nonnegative. -/
theorem maxFunctionModulusOnSet_nonneg {s : Set ℂ} {f : ℂ → ℂ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    0 ≤ maxFunctionModulusOnSet s f := by
  obtain ⟨z, _, hmax⟩ := exists_maxFunctionModulusOnSet hs hne hf
  rw [← hmax]
  exact norm_nonneg _

/-- Enlarging the compact set cannot decrease the maximum modulus. -/
theorem maxFunctionModulusOnSet_mono {s t : Set ℂ} {f : ℂ → ℂ}
    (hs : IsCompact s) (hsne : s.Nonempty)
    (ht : IsCompact t) (htne : t.Nonempty)
    (hf : ContinuousOn f t) (hst : s ⊆ t) :
    maxFunctionModulusOnSet s f ≤ maxFunctionModulusOnSet t f := by
  obtain ⟨z, hz, hmax⟩ :=
    exists_maxFunctionModulusOnSet hs hsne (hf.mono hst)
  rw [← hmax]
  exact norm_function_le_maxFunctionModulusOnSet ht htne hf (hst hz)

/-- Maximum moduli of a continuous function on compact outer approximations converge to the
maximum on the limit set. -/
theorem tendsto_maxFunctionModulusOnSet_of_outerApproximation
    {f : ℂ → ℂ} {K C : Set ℂ}
    (hKcompact : IsCompact K) (hKne : K.Nonempty)
    (hCcompact : IsCompact C) (hf : ContinuousOn f C)
    {s : ℕ → Set ℂ}
    (hscompact : ∀ k, IsCompact (s k))
    (hKs : ∀ k, K ⊆ s k)
    (hsC : ∀ k, s k ⊆ C)
    {radius : ℕ → ℝ}
    (hradius : Tendsto radius atTop (nhds 0))
    (hclose : ∀ k z, z ∈ s k → ∃ w ∈ K, ‖z - w‖ ≤ radius k) :
    Tendsto (fun k ↦ maxFunctionModulusOnSet (s k) f) atTop
      (nhds (maxFunctionModulusOnSet K f)) := by
  let g : ℂ → ℝ := fun z ↦ ‖f z‖
  have hKC : K ⊆ C := (hKs 0).trans (hsC 0)
  have hguniform : UniformContinuousOn g C :=
    hCcompact.uniformContinuousOn_of_continuous hf.norm
  refine Metric.tendsto_atTop.2 ?_
  intro eta heta
  obtain ⟨delta, hdelta, huniform⟩ :=
    Metric.uniformContinuousOn_iff.mp hguniform eta heta
  have heventually : ∀ᶠ k in atTop, radius k < delta :=
    (tendsto_order.1 hradius).2 delta hdelta
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  refine ⟨N, fun k hk ↦ ?_⟩
  have hskne : (s k).Nonempty := hKne.mono (hKs k)
  have hfs : ContinuousOn f (s k) := hf.mono (hsC k)
  have hlower :
      maxFunctionModulusOnSet K f ≤ maxFunctionModulusOnSet (s k) f :=
    maxFunctionModulusOnSet_mono hKcompact hKne (hscompact k) hskne hfs (hKs k)
  obtain ⟨z, hzs, hzmax⟩ :=
    exists_maxFunctionModulusOnSet (hscompact k) hskne hfs
  obtain ⟨w, hwK, hzw⟩ := hclose k z hzs
  have hzw' : dist z w < delta := by
    rw [dist_eq_norm]
    exact hzw.trans_lt (hN k hk)
  have hvalues : dist (g z) (g w) < eta :=
    huniform z (hsC k hzs) w (hKC hwK) hzw'
  have hwle : g w ≤ maxFunctionModulusOnSet K f :=
    norm_function_le_maxFunctionModulusOnSet hKcompact hKne
      (hf.mono hKC) hwK
  have hupper :
      maxFunctionModulusOnSet (s k) f <
        maxFunctionModulusOnSet K f + eta := by
    rw [← hzmax]
    rw [Real.dist_eq, abs_lt] at hvalues
    exact (sub_lt_iff_lt_add.mp hvalues.2).trans_le
      (by simpa [add_comm] using add_le_add_right hwle eta)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end CrouzeixConjecture
