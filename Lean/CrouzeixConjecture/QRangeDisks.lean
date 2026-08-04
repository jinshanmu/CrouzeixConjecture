module

public import CrouzeixConjecture.QNumericalRange
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

noncomputable section

open Set
open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared length of the component of `A x` orthogonal to a unit vector `x`. -/
def qResidualSq (A : SquareMatrix n) (x : EuclideanVector n) : ℝ :=
  ‖euclideanOperator A x‖ ^ 2 - ‖⟪x, euclideanOperator A x⟫_ℂ‖ ^ 2

/-- The nonnegative residual occurring in Tsing's disk description of the
`q`-numerical range. -/
def qResidual (A : SquareMatrix n) (x : EuclideanVector n) : ℝ :=
  √(qResidualSq A x)

/-- The union of Tsing disks indexed by unit vectors.  For `0 < r ≤ 1`, this is the
set described on the right-hand side of Tsing's disk-union formula. -/
def qDiskUnion (r : ℝ) (A : SquareMatrix n) : Set ℂ :=
  {z | ∃ x : EuclideanVector n, ‖x‖ = 1 ∧
    ‖z - ⟪x, euclideanOperator A x⟫_ℂ‖ ≤
      (qTau r / r) * qResidual A x}

/-- The signed difference whose zero set is the boundary of the disk indexed by `x`. -/
def qDiskGap (r : ℝ) (A : SquareMatrix n) (z : ℂ) (x : EuclideanVector n) : ℝ :=
  ‖z - ⟪x, euclideanOperator A x⟫_ℂ‖ -
    (qTau r / r) * qResidual A x

theorem qResidualSq_nonneg (A : SquareMatrix n) {x : EuclideanVector n}
    (hx : ‖x‖ = 1) : 0 ≤ qResidualSq A x := by
  have hinner : ‖⟪x, euclideanOperator A x⟫_ℂ‖ ≤
      ‖x‖ * ‖euclideanOperator A x‖ :=
    norm_inner_le_norm x (euclideanOperator A x)
  rw [hx, one_mul] at hinner
  unfold qResidualSq
  nlinarith [norm_nonneg (⟪x, euclideanOperator A x⟫_ℂ),
    norm_nonneg (euclideanOperator A x)]

theorem qResidual_nonneg (A : SquareMatrix n) (x : EuclideanVector n) :
    0 ≤ qResidual A x :=
  Real.sqrt_nonneg _

theorem qResidual_sq (A : SquareMatrix n) {x : EuclideanVector n}
    (hx : ‖x‖ = 1) : qResidual A x ^ 2 = qResidualSq A x := by
  exact Real.sq_sqrt (qResidualSq_nonneg A hx)

theorem continuous_qResidualSq (A : SquareMatrix n) :
    Continuous (qResidualSq A) := by
  unfold qResidualSq
  fun_prop

theorem continuous_qResidual (A : SquareMatrix n) :
    Continuous (qResidual A) := by
  unfold qResidual
  exact Real.continuous_sqrt.comp (continuous_qResidualSq A)

theorem continuous_qDiskGap (r : ℝ) (A : SquareMatrix n) (z : ℂ) :
    Continuous (qDiskGap r A z) := by
  unfold qDiskGap
  exact (continuous_const.sub (continuous_euclideanQuadraticForm A)).norm.sub
    (continuous_const.mul (continuous_qResidual A))

/-- The orthogonal residual vector realizes `qResidual` as an ordinary norm. -/
theorem norm_sub_inner_smul_eq_qResidual (A : SquareMatrix n)
    {x : EuclideanVector n} (hx : ‖x‖ = 1) :
    ‖euclideanOperator A x - ⟪x, euclideanOperator A x⟫_ℂ • x‖ = qResidual A x := by
  let a : ℂ := ⟪x, euclideanOperator A x⟫_ℂ
  let e : EuclideanVector n := euclideanOperator A x - a • x
  have hxe : ⟪x, e⟫_ℂ = 0 := by
    dsimp [e, a]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  have hae : ⟪a • x, e⟫_ℂ = 0 := by
    rw [inner_smul_left, hxe, mul_zero]
  have hdecomp : euclideanOperator A x = a • x + e := by
    simp [e]
  have hnormsq : ‖e‖ ^ 2 = qResidualSq A x := by
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (a • x) e hae
    rw [← hdecomp, norm_smul, hx, mul_one] at hpyth
    unfold qResidualSq
    dsimp [a] at hpyth ⊢
    nlinarith
  have hsqrt : ‖e‖ = √(qResidualSq A x) := by
    rw [← Real.sqrt_sq (norm_nonneg e), hnormsq]
  simpa [e, qResidual] using hsqrt

/-- Tsing's easy inclusion: every constrained pair lies in the disk associated
with its first vector. -/
theorem scaledQNumericalRange_mem_disk
    {r : ℝ} (hr0 : 0 < r) (A : SquareMatrix n) {z : ℂ}
    (hz : z ∈ scaledQNumericalRange (r : ℂ) A) :
    ∃ x : EuclideanVector n, ‖x‖ = 1 ∧
      ‖z - ⟪x, euclideanOperator A x⟫_ℂ‖ ≤
        (qTau r / r) * qResidual A x := by
  rw [mem_scaledQNumericalRange_iff] at hz
  obtain ⟨x, y, hx, hy, hyx, hvalue⟩ := hz
  refine ⟨x, hx, ?_⟩
  let a : ℂ := ⟪x, euclideanOperator A x⟫_ℂ
  let v : EuclideanVector n := y - (r : ℂ) • x
  let e : EuclideanVector n := euclideanOperator A x - a • x
  have hvx : ⟪v, x⟫_ℂ = 0 := by
    dsimp [v]
    rw [inner_sub_left, inner_smul_left_eq_smul x x r, hyx,
      inner_self_eq_norm_sq_to_K, hx]
    simp
  have hveq : ⟪v, euclideanOperator A x⟫_ℂ = ⟪v, e⟫_ℂ := by
    rw [show euclideanOperator A x = a • x + e by simp [e], inner_add_right,
      inner_smul_right, hvx]
    simp
  have hvnormsq : ‖v‖ ^ 2 = 1 - r ^ 2 := by
    rw [@norm_sub_sq ℂ]
    simp only [hy, hx, norm_smul, mul_one, inner_smul_right, hyx,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    norm_num
    ring
  have hsubnonneg : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hvnorm : ‖v‖ = qTau r := by
    rw [qTau, ← Real.sqrt_sq (norm_nonneg v), hvnormsq]
  have henorm : ‖e‖ = qResidual A x := by
    simpa [e, a] using norm_sub_inner_smul_eq_qResidual A hx
  have hinner : ‖⟪v, euclideanOperator A x⟫_ℂ‖ ≤
      qTau r * qResidual A x := by
    rw [hveq]
    exact (norm_inner_le_norm v e).trans_eq (by rw [hvnorm, henorm])
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr0
  have hvalue' : ⟪y, euclideanOperator A x⟫_ℂ = (r : ℂ) * z := by
    apply (inv_mul_eq_iff_eq_mul₀ hrC).mp
    simpa using hvalue
  have hvvalue : ⟪v, euclideanOperator A x⟫_ℂ =
      (r : ℂ) * (z - a) := by
    dsimp [v]
    rw [inner_sub_left, inner_smul_left_eq_smul x (euclideanOperator A x) r, hvalue']
    rw [RCLike.real_smul_eq_coe_mul]
    dsimp [a]
    ring
  have hnormIdentity : ‖⟪v, euclideanOperator A x⟫_ℂ‖ =
      r * ‖z - a‖ := by
    rw [hvvalue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
  rw [hnormIdentity] at hinner
  calc
    ‖z - ⟪x, euclideanOperator A x⟫_ℂ‖ ≤
        (qTau r * qResidual A x) / r :=
      (le_div_iff₀ hr0).2 (by simpa [mul_comm, a] using hinner)
    _ = (qTau r / r) * qResidual A x := by ring

/-- The disk radius coefficient `√(1-r²)/r` decreases as `r` increases. -/
theorem qTau_div_antitone {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) :
    qTau s / s ≤ qTau r / r := by
  have hs0 : 0 < s := hr0.trans_le hrs
  have hrsSq : r ^ 2 ≤ s ^ 2 := by nlinarith
  have htau : qTau s ≤ qTau r := by
    unfold qTau
    exact Real.sqrt_le_sqrt (by linarith)
  rw [div_le_div_iff₀ hs0 hr0]
  calc
    qTau s * r ≤ qTau r * r :=
      mul_le_mul_of_nonneg_right htau hr0.le
    _ ≤ qTau r * s :=
      mul_le_mul_of_nonneg_left hrs (qTau_nonneg r)

/-- The Tsing disk union is nested in the expected direction: decreasing `r` enlarges it. -/
theorem qDiskUnion_mono {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s)
    (A : SquareMatrix n) : qDiskUnion s A ⊆ qDiskUnion r A := by
  rintro z ⟨x, hx, hz⟩
  refine ⟨x, hx, hz.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (qTau_div_antitone hr0 hrs)
    (qResidual_nonneg A x)

/-- The easy half of Tsing's formula, stated as a set inclusion. -/
theorem scaledQNumericalRange_subset_qDiskUnion
    {r : ℝ} (hr0 : 0 < r) (A : SquareMatrix n) :
    scaledQNumericalRange (r : ℂ) A ⊆ qDiskUnion r A := by
  intro z hz
  exact scaledQNumericalRange_mem_disk hr0 A hz

/-- At the endpoint `r = 1`, every Tsing disk degenerates to its numerical-range center. -/
theorem qDiskUnion_one (A : SquareMatrix n) : qDiskUnion 1 A = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, hz⟩
    have hzero : ‖z - ⟪x, euclideanOperator A x⟫_ℂ‖ = 0 := by
      apply le_antisymm
      · simpa [qTau] using hz
      · exact norm_nonneg _
    have hz' : z = ⟪x, euclideanOperator A x⟫_ℂ :=
      sub_eq_zero.mp (norm_eq_zero.mp hzero)
    exact ⟨x, hx, hz'.symm⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [sub_self, norm_zero, div_one]
    exact mul_nonneg (qTau_nonneg 1) (qResidual_nonneg A x)

/-- A finite complex matrix on a nonzero space has a normalized eigenvector. -/
theorem exists_unit_eigenvector [Nontrivial n] (A : SquareMatrix n) :
    ∃ (lam : ℂ) (x : EuclideanVector n), ‖x‖ = 1 ∧
      euclideanOperator A x = lam • x := by
  obtain ⟨lam, hlam⟩ := spectrum.nonempty A
  have hlamLinear : lam ∈ spectrum ℂ (Matrix.toLpLin 2 2 A) := by
    rw [Matrix.spectrum_toLpLin 2]
    exact hlam
  obtain ⟨v, hv⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hlamLinear).exists_hasEigenvector
  let x : EuclideanVector n := (‖v‖ : ℂ)⁻¹ • v
  have hvNorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  have hxNorm : ‖x‖ = 1 := by
    simp [x, norm_smul, hvNorm]
  refine ⟨lam, x, hxNorm, ?_⟩
  change Matrix.toLpLin 2 2 A x = lam • x
  simp [x, hv.apply_eq_smul, smul_smul, mul_comm]

omit [DecidableEq n] in
/-- The unit sphere in a complex vector space of dimension at least two is path-connected. -/
theorem isPathConnected_euclideanUnitSphere [Nontrivial n] :
    IsPathConnected (Metric.sphere (0 : EuclideanVector n) 1) := by
  apply isPathConnected_sphere ?_ (0 : EuclideanVector n) (by positivity)
  apply Module.one_lt_rank_of_one_lt_finrank
  have hcomplex : 1 < Module.finrank ℂ (EuclideanVector n) := by
    simpa using (Fintype.one_lt_card : 1 < Fintype.card n)
  exact hcomplex.trans_le
    (Module.finrank_top_le_finrank_of_isScalarTower ℝ ℂ (EuclideanVector n))

omit [DecidableEq n] in
/-- A unit vector in complex dimension at least two has a unit orthogonal companion. -/
theorem exists_unit_orthogonal [Nontrivial n] {u : EuclideanVector n} (hu : ‖u‖ = 1) :
    ∃ w : EuclideanVector n, ‖w‖ = 1 ∧ ⟪w, u⟫_ℂ = 0 := by
  let K : Submodule ℂ (EuclideanVector n) := ℂ ∙ u
  have hu0 : u ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hK : Module.finrank ℂ K = 1 := by
    exact finrank_span_singleton hu0
  have hcomplex : 1 < Module.finrank ℂ (EuclideanVector n) := by
    simpa using (Fintype.one_lt_card : 1 < Fintype.card n)
  have hsum := K.finrank_add_finrank_orthogonal
  have hperpPos : 0 < Module.finrank ℂ Kᗮ := by
    rw [hK] at hsum
    omega
  letI : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos hperpPos
  obtain ⟨v, hv⟩ := exists_ne (0 : Kᗮ)
  have hv0 : (v : EuclideanVector n) ≠ 0 := by
    exact Subtype.coe_ne_coe.mpr hv
  have hvNorm : ‖(v : EuclideanVector n)‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  let w : EuclideanVector n := (‖(v : EuclideanVector n)‖ : ℂ)⁻¹ •
    (v : EuclideanVector n)
  have hw : ‖w‖ = 1 := by
    simp [w, norm_smul, hvNorm]
  have hvOrth : ⟪(v : EuclideanVector n), u⟫_ℂ = 0 := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property
  have hwOrth : ⟪w, u⟫_ℂ = 0 := by
    rw [show w = (‖(v : EuclideanVector n)‖ : ℂ)⁻¹ •
      (v : EuclideanVector n) by rfl, inner_smul_left, hvOrth, mul_zero]
  exact ⟨w, hw, hwOrth⟩

/-- A unit residual direction.  In the degenerate (eigenvector) case, any unit vector
orthogonal to `u` supplies the required zero residual pairing. -/
theorem exists_unit_residual_direction [Nontrivial n] (A : SquareMatrix n)
    {u : EuclideanVector n} (hu : ‖u‖ = 1) :
    ∃ w : EuclideanVector n, ‖w‖ = 1 ∧ ⟪w, u⟫_ℂ = 0 ∧
      ⟪w, euclideanOperator A u⟫_ℂ = (qResidual A u : ℂ) := by
  let a : ℂ := ⟪u, euclideanOperator A u⟫_ℂ
  let e : EuclideanVector n := euclideanOperator A u - a • u
  have hue : ⟪u, e⟫_ℂ = 0 := by
    dsimp [e, a]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have heu : ⟪e, u⟫_ℂ = 0 := by
    rwa [inner_eq_zero_symm]
  have henorm : ‖e‖ = qResidual A u := by
    simpa only [e, a] using norm_sub_inner_smul_eq_qResidual A hu
  by_cases hd : qResidual A u = 0
  · obtain ⟨w, hw, hwu⟩ := exists_unit_orthogonal hu
    have he0 : e = 0 := by
      apply norm_eq_zero.mp
      rw [henorm, hd]
    have hAu : euclideanOperator A u = a • u := by
      exact sub_eq_zero.mp he0
    refine ⟨w, hw, hwu, ?_⟩
    rw [hAu, inner_smul_right, hwu, mul_zero, hd]
    norm_num
  · have hd0 : 0 < qResidual A u :=
      lt_of_le_of_ne (qResidual_nonneg A u) (Ne.symm hd)
    have hdC : (qResidual A u : ℂ) ≠ 0 := by exact_mod_cast hd
    let w : EuclideanVector n := ((qResidual A u : ℂ)⁻¹) • e
    have hw : ‖w‖ = 1 := by
      rw [show w = ((qResidual A u : ℂ)⁻¹) • e by rfl, norm_smul,
        norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, henorm]
      exact inv_mul_cancel₀ hd
    have hwu : ⟪w, u⟫_ℂ = 0 := by
      rw [show w = ((qResidual A u : ℂ)⁻¹) • e by rfl,
        inner_smul_left, heu, mul_zero]
    have hwe : ⟪w, e⟫_ℂ = (qResidual A u : ℂ) := by
      rw [show w = ((qResidual A u : ℂ)⁻¹) • e by rfl,
        inner_smul_left, map_inv₀, Complex.conj_ofReal,
        inner_self_eq_norm_sq_to_K, henorm]
      field_simp [hdC]
      norm_cast
    refine ⟨w, hw, hwu, ?_⟩
    rw [show euclideanOperator A u = a • u + e by simp [e], inner_add_right,
      inner_smul_right, hwu]
    simp [hwe]

/-- A point on one of the boundary circles in Tsing's description is represented by an
explicit constrained pair. -/
theorem qDisk_boundary_mem_scaledQNumericalRange [Nontrivial n]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (A : SquareMatrix n) {z : ℂ}
    {u : EuclideanVector n} (hu : ‖u‖ = 1)
    (hboundary : ‖z - ⟪u, euclideanOperator A u⟫_ℂ‖ =
      (qTau r / r) * qResidual A u) :
    z ∈ scaledQNumericalRange (r : ℂ) A := by
  let a : ℂ := ⟪u, euclideanOperator A u⟫_ℂ
  let delta : ℂ := z - a
  let d : ℝ := qResidual A u
  have hdNonneg : 0 ≤ d := qResidual_nonneg A u
  have hboundary' : ‖delta‖ = (qTau r / r) * d := by
    simpa only [delta, a, d] using hboundary
  obtain ⟨w, hw, hwu, hwA⟩ := exists_unit_residual_direction A hu
  have hwA' : ⟪w, euclideanOperator A u⟫_ℂ = (d : ℂ) := by
    simpa only [d] using hwA
  let beta : ℂ := if d = 0 then (qTau r : ℂ)
    else (r : ℂ) * conj delta / (d : ℂ)
  have hbetaNorm : ‖beta‖ = qTau r := by
    by_cases hd : d = 0
    · rw [show beta = (qTau r : ℂ) by simp [beta, hd],
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (qTau_nonneg r)]
    · have hd0 : 0 < d := lt_of_le_of_ne hdNonneg (Ne.symm hd)
      rw [show beta = (r : ℂ) * conj delta / (d : ℂ) by simp [beta, hd],
        norm_div, norm_mul, Complex.norm_conj,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0, hboundary']
      field_simp [ne_of_gt hr0, ne_of_gt hd0]
  have hbetaResidual : conj beta * (d : ℂ) = (r : ℂ) * delta := by
    by_cases hd : d = 0
    · have hdeltaNorm : ‖delta‖ = 0 := by rw [hboundary', hd, mul_zero]
      have hdelta : delta = 0 := norm_eq_zero.mp hdeltaNorm
      simp [beta, hd, hdelta]
    · have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
      rw [show beta = (r : ℂ) * conj delta / (d : ℂ) by simp [beta, hd]]
      simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj]
      field_simp [hdC]
  let y : EuclideanVector n := (r : ℂ) • u + beta • w
  have huw : ⟪u, w⟫_ℂ = 0 := by
    rwa [inner_eq_zero_symm]
  have horth : ⟪(r : ℂ) • u, beta • w⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, huw]
    simp
  have hfirstNorm : ‖(r : ℂ) • u‖ = r := by
    rw [norm_smul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hsecondNorm : ‖beta • w‖ = qTau r := by
    rw [norm_smul, hw, mul_one, hbetaNorm]
  have hySq : ‖y‖ ^ 2 = 1 := by
    calc
      ‖y‖ ^ 2 = ‖(r : ℂ) • u‖ ^ 2 + ‖beta • w‖ ^ 2 := by
        simpa only [y, pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      _ = r ^ 2 + qTau r ^ 2 := by rw [hfirstNorm, hsecondNorm]
      _ = 1 := by rw [qTau_sq hr1 hr0.le]; ring
  have hy : ‖y‖ = 1 := by nlinarith [norm_nonneg y]
  have hyu : ⟪y, u⟫_ℂ = (r : ℂ) := by
    rw [show y = (r : ℂ) • u + beta • w by rfl, inner_add_left,
      inner_smul_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hu, hwu]
    simp
  have hyA : ⟪y, euclideanOperator A u⟫_ℂ = (r : ℂ) * z := by
    rw [show y = (r : ℂ) • u + beta • w by rfl, inner_add_left,
      inner_smul_left, inner_smul_left, show ⟪u, euclideanOperator A u⟫_ℂ = a by rfl,
      hwA', Complex.conj_ofReal, hbetaResidual]
    dsimp [delta]
    ring
  rw [mem_scaledQNumericalRange_iff]
  refine ⟨u, y, hu, hy, hyu, ?_⟩
  rw [hyA, ← mul_assoc, inv_mul_cancel₀]
  · exact one_mul z
  · exact_mod_cast ne_of_gt hr0

/-- Every point in a Tsing disk union lies on the boundary of one of its constituent disks.
The proof is the connected-sphere argument from Tsing's lemma: the disk gap is nonpositive at
the vector that supplies membership and nonnegative at a normalized eigenvector. -/
theorem exists_qDisk_boundary [Nontrivial n]
    {r : ℝ} (A : SquareMatrix n) {z : ℂ}
    (hz : z ∈ qDiskUnion r A) :
    ∃ u : EuclideanVector n, ‖u‖ = 1 ∧
      ‖z - ⟪u, euclideanOperator A u⟫_ℂ‖ =
        (qTau r / r) * qResidual A u := by
  obtain ⟨x, hx, hxDisk⟩ := hz
  obtain ⟨lam, e, he, heEigen⟩ := exists_unit_eigenvector A
  have heInner : ⟪e, euclideanOperator A e⟫_ℂ = lam := by
    rw [heEigen, inner_smul_right, inner_self_eq_norm_sq_to_K, he]
    norm_num
  have heResidual : qResidual A e = 0 := by
    rw [← norm_sub_inner_smul_eq_qResidual A he, heInner, heEigen, sub_self, norm_zero]
  have hxGap : qDiskGap r A z x ≤ 0 := by
    exact sub_nonpos.mpr hxDisk
  have heGap : 0 ≤ qDiskGap r A z e := by
    unfold qDiskGap
    rw [heResidual, mul_zero, sub_zero]
    exact norm_nonneg _
  have hxSphere : x ∈ Metric.sphere (0 : EuclideanVector n) 1 := by
    simpa only [mem_sphere_zero_iff_norm] using hx
  have heSphere : e ∈ Metric.sphere (0 : EuclideanVector n) 1 := by
    simpa only [mem_sphere_zero_iff_norm] using he
  obtain ⟨u, huSphere, huGap⟩ :=
    (isPathConnected_euclideanUnitSphere (n := n)).isConnected.isPreconnected.intermediate_value₂
      hxSphere heSphere (continuous_qDiskGap r A z).continuousOn
      continuous_const.continuousOn hxGap heGap
  refine ⟨u, mem_sphere_zero_iff_norm.mp huSphere, ?_⟩
  exact sub_eq_zero.mp huGap

/-- The hard inclusion in Tsing's disk-union formula. -/
theorem qDiskUnion_subset_scaledQNumericalRange [Nontrivial n]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (A : SquareMatrix n) :
    qDiskUnion r A ⊆ scaledQNumericalRange (r : ℂ) A := by
  intro z hz
  obtain ⟨u, hu, hboundary⟩ := exists_qDisk_boundary A hz
  exact qDisk_boundary_mem_scaledQNumericalRange hr0 hr1 A hu hboundary

/-- Tsing's disk-union characterization of the scaled real-parameter `q`-numerical range. -/
theorem scaledQNumericalRange_eq_qDiskUnion [Nontrivial n]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (A : SquareMatrix n) :
    scaledQNumericalRange (r : ℂ) A = qDiskUnion r A := by
  apply Set.Subset.antisymm
  · exact scaledQNumericalRange_subset_qDiskUnion hr0 A
  · exact qDiskUnion_subset_scaledQNumericalRange hr0 hr1 A

/-- Nesting of scaled `q`-numerical ranges for positive real parameters. -/
theorem scaledQNumericalRange_antitone [Nontrivial n]
    {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s) (hs1 : s ≤ 1)
    (A : SquareMatrix n) :
    scaledQNumericalRange (s : ℂ) A ⊆ scaledQNumericalRange (r : ℂ) A := by
  rw [scaledQNumericalRange_eq_qDiskUnion (hr0.trans_le hrs) hs1 A,
    scaledQNumericalRange_eq_qDiskUnion hr0 (hrs.trans hs1) A]
  exact qDiskUnion_mono hr0 hrs A

end CrouzeixConjecture
