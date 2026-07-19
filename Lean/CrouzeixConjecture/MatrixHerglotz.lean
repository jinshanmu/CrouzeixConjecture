module

public import CrouzeixConjecture.HerglotzKernel
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.MeanValue

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator Topology

namespace CrouzeixConjecture

private def diskFeature (z ζ : ℂ) : ℂ :=
  (1 - starRingEnd ℂ z * ζ)⁻¹

private def matrixEntryCLM {n : Type*} [Fintype n] [DecidableEq n] (i j : n) :
    SquareMatrix n →L[ℂ] ℂ := by
  letI : Nonempty n := ⟨i⟩
  exact LinearMap.mkContinuous
    { toFun := fun A ↦ A i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun A ↦ by
      calc
        ‖A i j‖ = ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
            (EuclideanSpace.single j 1)) i‖ := by
          simp only [Matrix.toEuclideanCLM_toLp, EuclideanSpace.single,
            Matrix.mulVec_single_one, Matrix.col_apply]
        _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
            (EuclideanSpace.single j 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ *
            ‖EuclideanSpace.single j (1 : ℂ)‖ :=
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm _
        _ = 1 * ‖A‖ := by simp [Matrix.l2_opNorm_toEuclideanCLM])

private lemma analyticOnNhd_matrixEntry
    {n : Type*} [Fintype n] [DecidableEq n] {K : ℂ → SquareMatrix n}
    {s : Set ℂ} (hK : AnalyticOnNhd ℂ K s) (i j : n) :
    AnalyticOnNhd ℂ (fun z ↦ K z i j) s := by
  intro z hz
  simpa [matrixEntryCLM] using ((matrixEntryCLM i j).analyticAt (K z)).comp (hK z hz)

private lemma continuousAt_fintype_sum {ι α : Type*} [Fintype ι]
    [TopologicalSpace α] {f : ι → α → ℂ} {x : α}
    (hf : ∀ i, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i, f i y) x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : α ↦ (0 : ℂ)) x)
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using (hf a).add ih

private lemma sum_comm_three { α β γ : Type* } [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, f a b c := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ b, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

private lemma disk_denominator_ne_zero {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ζ ∈ Metric.closedBall 0 1) :
    1 - starRingEnd ℂ z * ζ ≠ 0 := by
  intro h
  have heq : starRingEnd ℂ z * ζ = 1 := (sub_eq_zero.mp h).symm
  have hζn : ‖ζ‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hζ
  have hlt : ‖starRingEnd ℂ z * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg z) hz hζn
  rw [heq, norm_one] at hlt
  exact (lt_irrefl 1 hlt).elim

private lemma star_diskFeature_on_unitCircle {z ζ : ℂ} (
    hζ : ζ ∈ unitCircle) :
    starRingEnd ℂ (diskFeature z ζ) = ζ / (ζ - z) := by
  have hnorm : ‖ζ‖ = 1 := by
    simpa [unitCircle, Metric.mem_sphere, dist_eq_norm] using hζ
  have hu : ζ * starRingEnd ℂ ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have hζzero : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hconjzero : starRingEnd ℂ ζ ≠ 0 := by simp [hζzero]
  simp only [diskFeature, map_inv₀, map_sub, map_one, map_mul, starRingEnd_self_apply]
  have hden : 1 - z * starRingEnd ℂ ζ = starRingEnd ℂ ζ * (ζ - z) := by
    rw [mul_sub, mul_comm (starRingEnd ℂ ζ) ζ, hu]
    ring
  rw [hden, mul_inv_rev, inv_eq_of_mul_eq_one_left hu]
  simp [div_eq_mul_inv, mul_comm]

private lemma circleAverage_star_diskFeature_mul
    {f : ℂ → ℂ} {z : ℂ} (hf : DiffContOnCl ℂ f (Metric.ball 0 1))
    (hz : z ∈ openUnitDisk) :
    Real.circleAverage (fun ζ ↦ starRingEnd ℂ (diskFeature z ζ) * f ζ) 0 1 = f z := by
  calc
    Real.circleAverage (fun ζ ↦ starRingEnd ℂ (diskFeature z ζ) * f ζ) 0 1 =
        Real.circleAverage (fun ζ ↦ ((ζ - 0) / (ζ - z)) • f ζ) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      change starRingEnd ℂ (diskFeature z ζ) * f ζ = ((ζ - 0) / (ζ - z)) • f ζ
      rw [star_diskFeature_on_unitCircle (by simpa [unitCircle] using hζ)]
      simp only [sub_zero, smul_eq_mul]
    _ = f z := by
      have hf' : DiffContOnCl ℂ f (Metric.ball 0 |(1 : ℝ)|) := by simpa using hf
      exact hf'.circleAverage_smul_div (by simpa [openUnitDisk] using hz)

private lemma circleAverage_two_features
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f openUnitDisk)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z w : ℂ}
    (hz : z ∈ openUnitDisk) (hw : w ∈ openUnitDisk) :
    Real.circleAverage
        (fun ζ ↦ starRingEnd ℂ (diskFeature z ζ) * diskFeature w ζ * f (r * ζ)) 0 1 =
      diskFeature w z * f (r * z) := by
  have hwnorm : ‖w‖ < 1 := by
    simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hw
  have hfeature : DiffContOnCl ℂ (diskFeature w) (Metric.ball 0 1) := by
    have hden : DiffContOnCl ℂ (fun ζ : ℂ ↦ 1 - starRingEnd ℂ w * ζ)
        (Metric.ball 0 1) := by
      exact (by fun_prop : Differentiable ℂ (fun ζ : ℂ ↦
        1 - starRingEnd ℂ w * ζ)).diffContOnCl
    simpa [diskFeature] using hden.inv (fun ζ hζ ↦
      disk_denominator_ne_zero hwnorm (by
        rwa [closure_ball (0 : ℂ) one_ne_zero] at hζ))
  have hscaled : DiffContOnCl ℂ (fun ζ : ℂ ↦ f (r * ζ)) (Metric.ball 0 1) := by
    apply DifferentiableOn.diffContOnCl_ball
        (U := Metric.closedBall (0 : ℂ) 1) (c := 0) (R := 1) _ subset_rfl
    intro ζ hζ
    have hζnorm : ‖ζ‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hζ
    have hrnorm : ‖(r : ℂ)‖ = r := by
      simp [Real.norm_eq_abs, abs_of_nonneg hr₀]
    have hrζ : (r : ℂ) * ζ ∈ openUnitDisk := by
      simp only [openUnitDisk, Metric.mem_ball, dist_zero_right, norm_mul, hrnorm]
      exact lt_of_le_of_lt (mul_le_of_le_one_right hr₀ hζnorm) hr₁
    simpa [Function.comp_def] using
      ((hf ((r : ℂ) * ζ) hrζ).differentiableAt.comp ζ (by fun_prop)).differentiableWithinAt
  have hproduct : DiffContOnCl ℂ
      (fun ζ ↦ diskFeature w ζ * f (r * ζ)) (Metric.ball 0 1) := by
    simpa [smul_eq_mul] using hfeature.smul hscaled
  simpa [mul_assoc] using circleAverage_star_diskFeature_mul hproduct hz

private lemma circleAverage_matrix_entry
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z w : ℂ}
    (hz : z ∈ openUnitDisk) (hw : w ∈ openUnitDisk) (a b : n) :
    Real.circleAverage
        (fun ζ ↦ starRingEnd ℂ (diskFeature z ζ) * diskFeature w ζ * K (r * ζ) a b) 0 1 =
      diskFeature w z * K (r * z) a b := by
  exact circleAverage_two_features (f := fun u ↦ K u a b)
    (analyticOnNhd_matrixEntry hK a b)
    hr₀ hr₁ hz hw

private lemma circleIntegrable_matrix_entry_term
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {z w : ℂ}
    (hz : z ∈ openUnitDisk) (hw : w ∈ openUnitDisk) (a b : n) :
    CircleIntegrable
      (fun ζ ↦ starRingEnd ℂ (diskFeature z ζ) * diskFeature w ζ * K (r * ζ) a b) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  intro ζ hζ
  have hclosed : ζ ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.sphere_subset_closedBall hζ
  have hζnorm : ‖ζ‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hclosed
  have hznorm : ‖z‖ < 1 := by
    simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hz
  have hwnorm : ‖w‖ < 1 := by
    simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hw
  have hrnorm : ‖(r : ℂ)‖ = r := by
    simp [Real.norm_eq_abs, abs_of_nonneg hr₀]
  have hrζ : (r : ℂ) * ζ ∈ openUnitDisk := by
    simp only [openUnitDisk, Metric.mem_ball, dist_zero_right, norm_mul, hrnorm]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hr₀ hζnorm) hr₁
  have hzcont : ContinuousAt (diskFeature z) ζ := by
    apply ContinuousAt.inv₀ (by fun_prop)
    exact disk_denominator_ne_zero hznorm hclosed
  have hwcont : ContinuousAt (diskFeature w) ζ := by
    apply ContinuousAt.inv₀ (by fun_prop)
    exact disk_denominator_ne_zero hwnorm hclosed
  have hKcont : ContinuousAt (fun u : ℂ ↦ K (r * u) a b) ζ := by
    exact ((analyticOnNhd_matrixEntry hK a b) _ hrζ).continuousAt.comp (by fun_prop)
  have hzstarcont : ContinuousAt (fun u ↦ starRingEnd ℂ (diskFeature z u)) ζ := by
    simpa [Function.comp_def] using Complex.continuous_conj.continuousAt.comp hzcont
  exact ((hzstarcont.mul hwcont).mul hKcont).continuousWithinAt

private def circleQuadratic {n : Type*} [Fintype n] {m : ℕ}
    (K : ℂ → SquareMatrix n) (r : ℝ) (z : Fin m → ℂ)
    (x : Fin m × n → ℂ) (ζ : ℂ) : ℂ :=
  ∑ p : Fin m × n, ∑ q : Fin m × n,
    (starRingEnd ℂ (x p) * x q) *
      (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
        K (r * ζ) p.2 q.2)

private def sampledAnalyticQuadratic {n : Type*} [Fintype n] {m : ℕ}
    (K : ℂ → SquareMatrix n) (r : ℝ) (z : Fin m → ℂ)
    (x : Fin m × n → ℂ) : ℂ :=
  ∑ p : Fin m × n, ∑ q : Fin m × n,
    starRingEnd ℂ (x p) *
      (diskFeature (z q.1) (z p.1) * K (r * z p.1) p.2 q.2) * x q

private lemma circleAverage_circleQuadratic
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (z : Fin m → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (x : Fin m × n → ℂ) :
    Real.circleAverage (circleQuadratic K r z x) 0 1 =
      sampledAnalyticQuadratic K r z x := by
  unfold circleQuadratic sampledAnalyticQuadratic
  have hterm (p q : Fin m × n) : CircleIntegrable
      (fun ζ ↦ (starRingEnd ℂ (x p) * x q) *
        (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
          K (r * ζ) p.2 q.2)) 0 1 := by
    exact (circleIntegrable_matrix_entry_term hK hr₀ hr₁
      (hz p.1) (hz q.1) p.2 q.2).const_mul (starRingEnd ℂ (x p) * x q)
  have hinner (p : Fin m × n) :
      Real.circleAverage (fun ζ ↦ ∑ q : Fin m × n,
        (starRingEnd ℂ (x p) * x q) *
          (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
            K (r * ζ) p.2 q.2)) 0 1 =
        ∑ q : Fin m × n, Real.circleAverage (fun ζ ↦
          (starRingEnd ℂ (x p) * x q) *
            (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
              K (r * ζ) p.2 q.2)) 0 1 := by
    exact Real.circleAverage_fun_sum (fun q _ ↦ hterm p q)
  have hinnerInt (p : Fin m × n) : CircleIntegrable (fun ζ ↦ ∑ q : Fin m × n,
      (starRingEnd ℂ (x p) * x q) *
        (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
          K (r * ζ) p.2 q.2)) 0 1 := by
    have hs := CircleIntegrable.sum Finset.univ (fun q _ ↦ hterm p q)
    have heq : (∑ q : Fin m × n, fun ζ ↦
        (starRingEnd ℂ (x p) * x q) *
          (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
            K (r * ζ) p.2 q.2)) = fun ζ ↦ ∑ q : Fin m × n,
        (starRingEnd ℂ (x p) * x q) *
          (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
            K (r * ζ) p.2 q.2) := by
      funext ζ
      simp
    rwa [heq] at hs
  have houter := Real.circleAverage_fun_sum (c := (0 : ℂ)) (R := (1 : ℝ))
    (s := Finset.univ)
    (f := fun p ζ ↦ ∑ q : Fin m × n,
      (starRingEnd ℂ (x p) * x q) *
        (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
          K (r * ζ) p.2 q.2))
    (fun p _ ↦ hinnerInt p)
  rw [houter]
  simp_rw [hinner]
  have hconst (p q : Fin m × n) : Real.circleAverage (fun ζ ↦
      (starRingEnd ℂ (x p) * x q) *
        (starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
          K (r * ζ) p.2 q.2)) 0 1 =
      (starRingEnd ℂ (x p) * x q) * Real.circleAverage (fun ζ ↦
        starRingEnd ℂ (diskFeature (z p.1) ζ) * diskFeature (z q.1) ζ *
          K (r * ζ) p.2 q.2) 0 1 := by
    simpa [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := starRingEnd ℂ (x p) * x q)
        (f := fun ζ ↦ starRingEnd ℂ (diskFeature (z p.1) ζ) *
          diskFeature (z q.1) ζ * K (r * ζ) p.2 q.2) (c := 0) (R := 1))
  simp_rw [hconst]
  simp_rw [circleAverage_matrix_entry hK hr₀ hr₁ (hz _) (hz _)]
  simp [mul_assoc, mul_comm, mul_left_comm]

private def circleVector {n : Type*} [Fintype n] {m : ℕ}
    (z : Fin m → ℂ) (x : Fin m × n → ℂ) (ζ : ℂ) : n → ℂ :=
  fun a ↦ ∑ i, diskFeature (z i) ζ * x (i, a)

private lemma circleQuadratic_eq_vector_quadratic
    {n : Type*} [Fintype n] {m : ℕ} (K : ℂ → SquareMatrix n)
    (r : ℝ) (z : Fin m → ℂ) (x : Fin m × n → ℂ) (ζ : ℂ) :
    circleQuadratic K r z x ζ =
      star (circleVector z x ζ) ⬝ᵥ (K (r * ζ) *ᵥ circleVector z x ζ) := by
  have hstar (a : n) : star (∑ i, diskFeature (z i) ζ * x (i, a)) =
      ∑ i, starRingEnd ℂ (x (i, a)) * starRingEnd ℂ (diskFeature (z i) ζ) := by
    change starRingEnd ℂ (∑ i, diskFeature (z i) ζ * x (i, a)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [map_mul, mul_comm]
  simp only [circleQuadratic, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    Pi.star_apply, starRingEnd_apply, circleVector]
  simp_rw [hstar]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_rhs => rw [sum_comm_three]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  simp only [starRingEnd_apply]
  ring

private def analyticSampleMatrix {n : Type*} {m : ℕ}
    (K : ℂ → SquareMatrix n) (r : ℝ) (z : Fin m → ℂ) :
    Matrix (Fin m × n) (Fin m × n) ℂ :=
  fun p q ↦ diskFeature (z q.1) (z p.1) * K (r * z p.1) p.2 q.2

private lemma sampledAnalyticQuadratic_eq
    {n : Type*} [Fintype n] {m : ℕ} (K : ℂ → SquareMatrix n)
    (r : ℝ) (z : Fin m → ℂ) (x : Fin m × n → ℂ) :
    sampledAnalyticQuadratic K r z x =
      star x ⬝ᵥ (analyticSampleMatrix K r z *ᵥ x) := by
  unfold sampledAnalyticQuadratic analyticSampleMatrix
  simp only [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  simp [mul_assoc]

private lemma star_quadratic_eq_conjTranspose
    {n : Type*} [Fintype n] (A : SquareMatrix n) (x : n → ℂ) :
    starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (Aᴴ *ᵥ x) := by
  calc
    starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) =
        starRingEnd ℂ (star (star (A *ᵥ x) ⬝ᵥ x)) := by
      rw [Matrix.star_dotProduct]
    _ = star (A *ᵥ x) ⬝ᵥ x := by
      change star (star (star (A *ᵥ x) ⬝ᵥ x)) = _
      rw [star_star]
    _ = (star x ᵥ* Aᴴ) ⬝ᵥ x := by rw [Matrix.star_mulVec]
    _ = star x ⬝ᵥ (Aᴴ *ᵥ x) := by rw [Matrix.dotProduct_mulVec]

private lemma sampled_regularized_kernel_eq_add_conjTranspose
    {n : Type*} [Fintype n] {m : ℕ} (K : ℂ → SquareMatrix n)
    (r : ℝ) (z : Fin m → ℂ) :
    sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z =
      analyticSampleMatrix K r z + (analyticSampleMatrix K r z)ᴴ := by
  ext p q
  simp only [sampledKernelMatrix, matrixHerglotzKernel, analyticSampleMatrix,
    Matrix.add_apply, Matrix.smul_apply, Matrix.conjTranspose_apply, smul_eq_mul]
  simp [diskFeature]
  ring

private lemma regularized_sampled_quadratic_eq
    {n : Type*} [Fintype n] {m : ℕ} (K : ℂ → SquareMatrix n)
    (r : ℝ) (z : Fin m → ℂ) (x : Fin m × n → ℂ) :
    star x ⬝ᵥ
        (sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z *ᵥ x) =
      sampledAnalyticQuadratic K r z x +
        starRingEnd ℂ (sampledAnalyticQuadratic K r z x) := by
  rw [sampled_regularized_kernel_eq_add_conjTranspose,
    Matrix.add_mulVec, dotProduct_add, sampledAnalyticQuadratic_eq]
  rw [star_quadratic_eq_conjTranspose]

private lemma circleQuadratic_continuousOn_closedBall
    {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) (z : Fin m → ℂ)
    (hz : ∀ i, z i ∈ openUnitDisk) (x : Fin m × n → ℂ) :
    ContinuousOn (circleQuadratic K r z x) (Metric.closedBall 0 1) := by
  intro ζ hζ
  have hζnorm : ‖ζ‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hζ
  have hrnorm : ‖(r : ℂ)‖ = r := by
    simp [Real.norm_eq_abs, abs_of_nonneg hr₀]
  have hrζ : (r : ℂ) * ζ ∈ openUnitDisk := by
    simp only [openUnitDisk, Metric.mem_ball, dist_zero_right, norm_mul, hrnorm]
    exact lt_of_le_of_lt (mul_le_of_le_one_right hr₀ hζnorm) hr₁
  have hfeature (i : Fin m) : ContinuousAt (diskFeature (z i)) ζ := by
    apply ContinuousAt.inv₀ (by fun_prop)
    apply disk_denominator_ne_zero
    · simpa [openUnitDisk, Metric.mem_ball, dist_eq_norm] using hz i
    · exact hζ
  have hKcont (a b : n) : ContinuousAt (fun u : ℂ ↦ K (r * u) a b) ζ := by
    exact ((analyticOnNhd_matrixEntry hK a b) _ hrζ).continuousAt.comp (by fun_prop)
  apply ContinuousAt.continuousWithinAt
  unfold circleQuadratic
  apply continuousAt_fintype_sum
  intro p
  apply continuousAt_fintype_sum
  intro q
  have hpstar : ContinuousAt
      (fun u ↦ starRingEnd ℂ (diskFeature (z p.1) u)) ζ := by
    simpa [Function.comp_def] using Complex.continuous_conj.continuousAt.comp (hfeature p.1)
  exact continuousAt_const.mul ((hpstar.mul (hfeature q.1)).mul (hKcont p.2 q.2))

private lemma quadratic_add_star_eq_two_rePart
    {n : Type*} [Fintype n] (A : SquareMatrix n) (x : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) + starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) =
      2 * (star x ⬝ᵥ (rePart A *ᵥ x)) := by
  rw [star_quadratic_eq_conjTranspose]
  simp only [rePart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_add,
    dotProduct_smul]
  norm_num
  ring

private theorem regularized_matrixHerglotzKernel_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    (hpos : ∀ u ∈ openUnitDisk, (rePart (K u)).PosSemidef)
    {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) {m : ℕ}
    (z : Fin m → ℂ) (hz : ∀ i, z i ∈ openUnitDisk) :
    (sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [sampled_regularized_kernel_eq_add_conjTranspose]
    rw [Matrix.IsHermitian]
    simp [add_comm]
  · intro x
    let q : ℂ → ℂ := circleQuadratic K r z x
    have hqcont : ContinuousOn q (Metric.sphere 0 1) :=
      (circleQuadratic_continuousOn_closedBall hK hr₀ hr₁ z hz x).mono
        Metric.sphere_subset_closedBall
    have hqint : CircleIntegrable q 0 1 := hqcont.circleIntegrable (by norm_num)
    have hstarcont : ContinuousOn (fun ζ ↦ starRingEnd ℂ (q ζ)) (Metric.sphere 0 1) :=
      fun ζ hζ ↦ by
        simpa [Function.comp_def] using
          Complex.continuous_conj.continuousAt.comp_continuousWithinAt (hqcont ζ hζ)
    have hstarint : CircleIntegrable (fun ζ ↦ starRingEnd ℂ (q ζ)) 0 1 :=
      hstarcont.circleIntegrable (by norm_num)
    have havgq : Real.circleAverage q 0 1 = sampledAnalyticQuadratic K r z x :=
      circleAverage_circleQuadratic hK hr₀ hr₁ z hz x
    have havgstar :
        Real.circleAverage (fun ζ ↦ starRingEnd ℂ (q ζ)) 0 1 =
          starRingEnd ℂ (Real.circleAverage q 0 1) := by
      have hcomm :=
        (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.circleAverage_comp_comm hqint
      simpa [Function.comp_def, Complex.conjCLE_apply] using hcomm
    have havgfull :
        Real.circleAverage (fun ζ ↦ q ζ + starRingEnd ℂ (q ζ)) 0 1 =
          star x ⬝ᵥ
            (sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z *ᵥ x) := by
      rw [Real.circleAverage_fun_add hqint hstarint, havgq, havgstar, havgq]
      exact (regularized_sampled_quadratic_eq K r z x).symm
    have hpoint : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1,
        0 ≤ (q ζ + starRingEnd ℂ (q ζ)).re := by
      intro ζ hζ
      have hζnorm : ‖ζ‖ ≤ 1 := by
        have : ζ ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hζ
        simpa [Metric.mem_closedBall, dist_eq_norm] using this
      have hrnorm : ‖(r : ℂ)‖ = r := by
        simp [Real.norm_eq_abs, abs_of_nonneg hr₀]
      have hrζ : (r : ℂ) * ζ ∈ openUnitDisk := by
        simp only [openUnitDisk, Metric.mem_ball, dist_zero_right, norm_mul, hrnorm]
        exact lt_of_le_of_lt (mul_le_of_le_one_right hr₀ hζnorm) hr₁
      let v := circleVector z x ζ
      have hvpos : 0 ≤ star v ⬝ᵥ (rePart (K (r * ζ)) *ᵥ v) :=
        (hpos _ hrζ).dotProduct_mulVec_nonneg v
      have hid : q ζ + starRingEnd ℂ (q ζ) =
          2 * (star v ⬝ᵥ (rePart (K (r * ζ)) *ᵥ v)) := by
        rw [show q ζ = star v ⬝ᵥ (K (r * ζ) *ᵥ v) by
          exact circleQuadratic_eq_vector_quadratic K r z x ζ]
        exact quadratic_add_star_eq_two_rePart _ _
      rw [hid]
      simpa using mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
        (Complex.nonneg_iff.mp hvpos).1
    have havgreal_nonneg :
        0 ≤ Real.circleAverage (fun ζ ↦ (q ζ + starRingEnd ℂ (q ζ)).re) 0 1 :=
      Real.circleAverage_nonneg_of_nonneg (by simpa only [abs_one] using hpoint)
    have hsumint : CircleIntegrable
        (fun ζ ↦ q ζ + starRingEnd ℂ (q ζ)) 0 1 := hqint.add hstarint
    have hrecomm := Complex.reCLM.circleAverage_comp_comm hsumint
    rw [havgfull] at hrecomm
    rw [Complex.nonneg_iff]
    constructor
    · have hrecomm' :
          Real.circleAverage (fun ζ ↦ (q ζ + starRingEnd ℂ (q ζ)).re) 0 1 =
            (star x ⬝ᵥ
              (sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z *ᵥ x)).re := by
          simpa [Function.comp_def] using hrecomm
      rw [← hrecomm']
      exact havgreal_nonneg
    · rw [regularized_sampled_quadratic_eq]
      simp

/-- The matrix Herglotz kernel theorem on the open unit disk: analyticity and positive
matrix real part imply positivity of every finite sampling of the Herglotz kernel. -/
theorem matrixHerglotzKernel_isPositiveMatrixKernelOn
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℂ → SquareMatrix n} (hK : AnalyticOnNhd ℂ K openUnitDisk)
    (hpos : ∀ u ∈ openUnitDisk, (rePart (K u)).PosSemidef) :
    IsPositiveMatrixKernelOn openUnitDisk (matrixHerglotzKernel K) := by
  intro m z hz
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext p q
    simp [sampledKernelMatrix, matrixHerglotzKernel, smul_eq_mul]
    ring
  · intro x
    let radius : ℕ → ℝ := fun k ↦ (k : ℝ) / (k + 1)
    have hradius₀ (k : ℕ) : 0 ≤ radius k := by
      dsimp [radius]
      positivity
    have hradius₁ (k : ℕ) : radius k < 1 := by
      dsimp [radius]
      rw [div_lt_one (by positivity : (0 : ℝ) < k + 1)]
      norm_num
    have hradius_tendsto : Tendsto radius atTop (nhds 1) := by
      simpa [radius] using (tendsto_natCast_div_add_atTop (1 : ℝ))
    let quadratic : ℝ → ℂ := fun r ↦
      star x ⬝ᵥ
        (sampledKernelMatrix (matrixHerglotzKernel (fun u ↦ K (r * u))) z *ᵥ x)
    have hKcont (p q : Fin m × n) :
        ContinuousAt (fun r : ℝ ↦ K (r * z p.1) p.2 q.2) 1 := by
      have hbase := ((analyticOnNhd_matrixEntry hK p.2 q.2) (z p.1) (hz p.1)).continuousAt
      exact hbase.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const) (by simp)
    have hsampled : ContinuousAt (fun r : ℝ ↦ sampledAnalyticQuadratic K r z x) 1 := by
      unfold sampledAnalyticQuadratic
      apply continuousAt_fintype_sum
      intro p
      apply continuousAt_fintype_sum
      intro q
      exact (continuousAt_const.mul (continuousAt_const.mul (hKcont p q))).mul continuousAt_const
    have hquadratic : ContinuousAt quadratic 1 := by
      have hstar : ContinuousAt
          (fun r : ℝ ↦ starRingEnd ℂ (sampledAnalyticQuadratic K r z x)) 1 := by
        simpa [Function.comp_def] using Complex.continuous_conj.continuousAt.comp hsampled
      have hsum := hsampled.add hstar
      have heq : quadratic = fun r ↦ sampledAnalyticQuadratic K r z x +
          starRingEnd ℂ (sampledAnalyticQuadratic K r z x) := by
        funext r
        exact regularized_sampled_quadratic_eq K r z x
      rw [heq]
      exact hsum
    have htendsto : Tendsto (fun k ↦ quadratic (radius k)) atTop (nhds (quadratic 1)) :=
      hquadratic.tendsto.comp hradius_tendsto
    have hnonneg (k : ℕ) : 0 ≤ quadratic (radius k) := by
      exact (regularized_matrixHerglotzKernel_posSemidef hK hpos
        (hradius₀ k) (hradius₁ k) z hz).dotProduct_mulVec_nonneg x
    have hlimit : 0 ≤ quadratic 1 := ge_of_tendsto' htendsto hnonneg
    simpa [quadratic] using hlimit

end CrouzeixConjecture
