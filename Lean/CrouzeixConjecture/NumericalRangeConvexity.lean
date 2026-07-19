module

public import CrouzeixConjecture.NumericalRange
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

noncomputable section

open scoped ComplexConjugate InnerProductSpace Matrix Matrix.Norms.L2Operator

namespace CrouzeixConjecture

/-- A real-linear map from a higher-dimensional finite-dimensional inner-product space has the
same image on the unit sphere as on the closed unit ball.  The missing radial length can be added
in a nonzero kernel direction without changing the image. -/
theorem LinearMap.image_unitSphere_eq_image_closedUnitBall_of_finrank_lt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (hdim : Module.finrank ℝ F < Module.finrank ℝ E) :
    L '' Metric.sphere (0 : E) 1 = L '' Metric.closedBall (0 : E) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Metric.sphere_subset_closedBall hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    let K : Submodule ℝ E := LinearMap.ker L
    have hK : K ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
    obtain ⟨k, hkK, hk0⟩ : ∃ k : E, k ∈ K ∧ k ≠ 0 := by
      simpa only [Submodule.ne_bot_iff] using hK
    let e : E := ‖k‖⁻¹ • k
    have heK : e ∈ K := K.smul_mem _ hkK
    have henorm : ‖e‖ = 1 := by
      simp [e, norm_smul, norm_ne_zero_iff.mpr hk0]
    let p : E := Kᗮ.starProjection x
    have hpK : p ∈ Kᗮ := by
      exact (Kᗮ.orthogonalProjection x).property
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hpnorm : ‖p‖ ≤ 1 := by
      exact (Kᗮ.norm_starProjection_apply_le x).trans hxnorm
    have hpnormsq : ‖p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p]
    let a : ℝ := √(1 - ‖p‖ ^ 2)
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hasq : a ^ 2 = 1 - ‖p‖ ^ 2 := by
      exact Real.sq_sqrt (sub_nonneg.mpr hpnormsq)
    let z : E := p + a • e
    have hpe : ⟪p, e⟫_ℝ = 0 := by
      exact (K.mem_orthogonal' p).mp hpK e heK
    have hp_smul_e : ⟪p, a • e⟫_ℝ = 0 := by
      rw [real_inner_smul_right, hpe, mul_zero]
    have hnormae : ‖a • e‖ = a := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, henorm, mul_one]
    have hznormsq : ‖z‖ ^ 2 = 1 := by
      change ‖p + a • e‖ ^ 2 = 1
      calc
        _ = ‖p + a • e‖ * ‖p + a • e‖ := pow_two _
        _ = ‖p‖ * ‖p‖ + ‖a • e‖ * ‖a • e‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (a • e) hp_smul_e
        _ = ‖p‖ ^ 2 + a ^ 2 := by rw [pow_two, pow_two, hnormae]
        _ = 1 := by rw [hasq]; ring
    have hznorm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    refine ⟨z, mem_sphere_zero_iff_norm.mpr hznorm, ?_⟩
    have hLe : L e = 0 := LinearMap.mem_ker.mp heK
    have hLp : L p = L x := by
      change L (Kᗮ.starProjection x) = L x
      rw [Submodule.starProjection_orthogonal_val, map_sub]
      have hproj : L (K.starProjection x) = 0 :=
        LinearMap.mem_ker.mp (K.starProjection_apply_mem x)
      rw [hproj, sub_zero]
    simp [z, hLp, hLe]

/-- The Bloch vector of a vector in `ℂ²`.  Its coordinates are chosen for Mathlib's
conjugate-linear-in-the-first-variable inner-product convention. -/
def blochVector (x : EuclideanVector (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * (conj (x 0) * x 1).re,
    2 * (conj (x 0) * x 1).im,
    ‖x 0‖ ^ 2 - ‖x 1‖ ^ 2]

/-- The elementary identity behind the Bloch-sphere parametrization. -/
theorem blochVector_norm_sq (x : EuclideanVector (Fin 2)) :
    ‖blochVector x‖ ^ 2 = (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [blochVector, Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem blochVector_mem_unitSphere {x : EuclideanVector (Fin 2)} (hx : ‖x‖ = 1) :
    blochVector x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hxcoord : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    calc
      _ = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_succ]
      _ = 1 := by rw [hx]; norm_num
  have hsq : ‖blochVector x‖ ^ 2 = 1 := by rw [blochVector_norm_sq, hxcoord]; norm_num
  nlinarith [norm_nonneg (blochVector x)]

/-- Coordinate equation for the real three-dimensional unit sphere. -/
theorem euclideanThree_unitSphere_coord_sq {r : EuclideanSpace ℝ (Fin 3)}
    (hr : r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (r 0) ^ 2 + (r 1) ^ 2 + (r 2) ^ 2 = 1 := by
  have hrnorm : ‖r‖ = 1 := mem_sphere_zero_iff_norm.mp hr
  calc
    (r 0) ^ 2 + (r 1) ^ 2 + (r 2) ^ 2 = ‖r‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    _ = 1 := by rw [hrnorm]; norm_num

/-- Reflection of the Bloch sphere induced by swapping the two complex coordinates. -/
def blochFlip (r : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![r 0, -r 1, -r 2]

/-- Swap the two coordinates of a vector in `ℂ²`. -/
def qubitSwap (x : EuclideanVector (Fin 2)) : EuclideanVector (Fin 2) :=
  WithLp.toLp 2 ![x 1, x 0]

@[simp]
theorem blochFlip_involutive (r : EuclideanSpace ℝ (Fin 3)) :
    blochFlip (blochFlip r) = r := by
  ext i
  fin_cases i <;> simp [blochFlip]

theorem blochFlip_mem_unitSphere {r : EuclideanSpace ℝ (Fin 3)}
    (hr : r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    blochFlip r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have hcoords := euclideanThree_unitSphere_coord_sq hr
  have hsq : ‖blochFlip r‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [blochFlip, Fin.sum_univ_succ]
    nlinarith
  nlinarith [norm_nonneg (blochFlip r)]

theorem qubitSwap_norm (x : EuclideanVector (Fin 2)) :
    ‖qubitSwap x‖ = ‖x‖ := by
  have hsq : ‖qubitSwap x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [qubitSwap, Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (qubitSwap x), norm_nonneg x]

theorem blochVector_qubitSwap (x : EuclideanVector (Fin 2)) :
    blochVector (qubitSwap x) = blochFlip (blochVector x) := by
  ext i
  fin_cases i <;>
    simp [blochVector, blochFlip, qubitSwap, mul_comm,
      Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The north-hemisphere inverse to the Bloch map. -/
theorem exists_unit_blochVector_eq_of_coord_two_nonneg
    {r : EuclideanSpace ℝ (Fin 3)}
    (hr : r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hrtwo : 0 ≤ r 2) :
    ∃ x : EuclideanVector (Fin 2), ‖x‖ = 1 ∧ blochVector x = r := by
  have hcoords := euclideanThree_unitSphere_coord_sq hr
  let a : ℝ := √((1 + r 2) / 2)
  have harg : 0 < (1 + r 2) / 2 := by nlinarith
  have ha : 0 < a := by
    exact Real.sqrt_pos.2 harg
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hasq : a ^ 2 = (1 + r 2) / 2 := by
    dsimp [a]
    exact Real.sq_sqrt harg.le
  let b_re : ℝ := r 0 / (2 * a)
  let b_im : ℝ := r 1 / (2 * a)
  have hbsq : b_re ^ 2 + b_im ^ 2 = (1 - r 2) / 2 := by
    dsimp [b_re, b_im]
    field_simp [ha_ne]
    nlinarith [hasq]
  let x : EuclideanVector (Fin 2) :=
    WithLp.toLp 2 ![(⟨a, 0⟩ : ℂ), (⟨b_re, b_im⟩ : ℂ)]
  have hxcoords : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    simp [x, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [hasq, hbsq]
  have hxnorm : ‖x‖ = 1 := by
    have hsq : ‖x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa [Fin.sum_univ_succ] using hxcoords
    nlinarith [norm_nonneg x]
  refine ⟨x, hxnorm, ?_⟩
  ext i
  fin_cases i
  · simp [blochVector, x, b_re, b_im]
    field_simp [ha_ne]
  · simp [blochVector, x, b_re, b_im]
    field_simp [ha_ne]
  · simp [blochVector, x, Complex.sq_norm, Complex.normSq_apply]
    nlinarith [hasq, hbsq]

/-- The Bloch map sends the unit sphere in `ℂ²` onto the unit sphere in `ℝ³`. -/
theorem exists_unit_blochVector_eq
    {r : EuclideanSpace ℝ (Fin 3)}
    (hr : r ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ x : EuclideanVector (Fin 2), ‖x‖ = 1 ∧ blochVector x = r := by
  by_cases hrtwo : 0 ≤ r 2
  · exact exists_unit_blochVector_eq_of_coord_two_nonneg hr hrtwo
  · have hrflip := blochFlip_mem_unitSphere hr
    have hflip_two : 0 ≤ blochFlip r 2 := by
      simpa [blochFlip] using neg_nonneg.mpr (le_of_not_ge hrtwo)
    obtain ⟨x, hx, hbloch⟩ :=
      exists_unit_blochVector_eq_of_coord_two_nonneg hrflip hflip_two
    refine ⟨qubitSwap x, by simpa [qubitSwap_norm] using hx, ?_⟩
    rw [blochVector_qubitSwap, hbloch, blochFlip_involutive]

/-- The real-linear part of the Bloch-sphere expression for a complex quadratic form in two
variables. -/
def blochLinearMap (b00 b01 b10 b11 : ℂ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℂ where
  toFun r :=
    (r 0) • ((b01 + b10) / 2) +
    (r 1) • (Complex.I * (b01 - b10) / 2) +
    (r 2) • ((b00 - b11) / 2)
  map_add' r s := by
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' c r := by
    simp [smul_add, mul_smul]

/-- The center of the Bloch-sphere expression. -/
def blochCenter (b00 b11 : ℂ) : ℂ :=
  (b00 + b11) / 2

/-- A general complex sesquilinear quadratic expression in two coordinates. -/
def twoQuadraticForm (b00 b01 b10 b11 : ℂ)
    (x : EuclideanVector (Fin 2)) : ℂ :=
  conj (x 0) * (b00 * x 0 + b01 * x 1) +
    conj (x 1) * (b10 * x 0 + b11 * x 1)

/-- On unit vectors, a two-dimensional complex quadratic form is an affine real-linear function
of the Bloch vector. -/
theorem twoQuadraticForm_eq_bloch
    (b00 b01 b10 b11 : ℂ) {x : EuclideanVector (Fin 2)} (hx : ‖x‖ = 1) :
    twoQuadraticForm b00 b01 b10 b11 x =
      blochCenter b00 b11 + blochLinearMap b00 b01 b10 b11 (blochVector x) := by
  have hxcoord : ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 = 1 := by
    calc
      _ = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_succ]
      _ = 1 := by rw [hx]; norm_num
  let u : ℂ := conj (x 0) * x 1
  have huconj : conj u = conj (x 1) * x 0 := by
    simp [u, map_mul, mul_comm]
  have hself (z : ℂ) : conj z * z = (‖z‖ ^ 2 : ℝ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hquadratic :
      twoQuadraticForm b00 b01 b10 b11 x =
        (‖x 0‖ ^ 2) • b00 + (‖x 1‖ ^ 2) • b11 +
          (b01 * u + b10 * conj u) := by
    have h00 : conj (x 0) * (b00 * x 0) = (‖x 0‖ ^ 2) • b00 := by
      calc
        _ = (conj (x 0) * x 0) * b00 := by ring
        _ = (‖x 0‖ ^ 2) • b00 := by
          rw [hself]
          simp only [Complex.real_smul]
    have h01 : conj (x 0) * (b01 * x 1) = b01 * u := by
      dsimp [u]
      ring
    have h10 : conj (x 1) * (b10 * x 0) = b10 * conj u := by
      rw [huconj]
      ring
    have h11 : conj (x 1) * (b11 * x 1) = (‖x 1‖ ^ 2) • b11 := by
      calc
        _ = (conj (x 1) * x 1) * b11 := by ring
        _ = (‖x 1‖ ^ 2) • b11 := by
          rw [hself]
          simp only [Complex.real_smul]
    rw [twoQuadraticForm, mul_add, mul_add, h00, h01, h10, h11]
    ring
  have hdiagonal :
      blochCenter b00 b11 +
          (‖x 0‖ ^ 2 - ‖x 1‖ ^ 2) • ((b00 - b11) / 2) =
        (‖x 0‖ ^ 2) • b00 + (‖x 1‖ ^ 2) • b11 := by
    rw [show blochCenter b00 b11 =
        (‖x 0‖ ^ 2 + ‖x 1‖ ^ 2) • blochCenter b00 b11 by
      rw [hxcoord]; simp]
    apply Complex.ext <;>
      simp [blochCenter, Complex.real_smul] <;>
      ring
  have hcross :
      (2 * u.re) • ((b01 + b10) / 2) +
          (2 * u.im) • (Complex.I * (b01 - b10) / 2) =
        b01 * u + b10 * conj u := by
    apply Complex.ext <;>
      simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;>
      ring
  rw [hquadratic]
  rw [show blochLinearMap b00 b01 b10 b11 (blochVector x) =
      (2 * u.re) • ((b01 + b10) / 2) +
        (2 * u.im) • (Complex.I * (b01 - b10) / 2) +
        (‖x 0‖ ^ 2 - ‖x 1‖ ^ 2) • ((b00 - b11) / 2) by
    simp [blochLinearMap, blochVector, u]]
  rw [hcross]
  calc
    (‖x 0‖ ^ 2) • b00 + (‖x 1‖ ^ 2) • b11 +
        (b01 * u + b10 * conj u) =
      (blochCenter b00 b11 +
          (‖x 0‖ ^ 2 - ‖x 1‖ ^ 2) • ((b00 - b11) / 2)) +
        (b01 * u + b10 * conj u) := by rw [hdiagonal]
    _ = blochCenter b00 b11 +
        (b01 * u + b10 * conj u +
          (‖x 0‖ ^ 2 - ‖x 1‖ ^ 2) • ((b00 - b11) / 2)) := by ring

/-- Toeplitz--Hausdorff in complex dimension two, for an arbitrary sesquilinear quadratic
expression. -/
theorem convex_twoQuadraticForm_unitSphere (b00 b01 b10 b11 : ℂ) :
    Convex ℝ
      (twoQuadraticForm b00 b01 b10 b11 ''
        Metric.sphere (0 : EuclideanVector (Fin 2)) 1) := by
  let L := blochLinearMap b00 b01 b10 b11
  let c := blochCenter b00 b11
  have hdim : Module.finrank ℝ ℂ <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Complex.finrank_real_complex]
  have himage :
      twoQuadraticForm b00 b01 b10 b11 ''
          Metric.sphere (0 : EuclideanVector (Fin 2)) 1 =
        (fun r ↦ c + L r) ''
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      refine ⟨blochVector x, Metric.sphere_subset_closedBall
        (blochVector_mem_unitSphere hxnorm), ?_⟩
      simpa [c, L] using
        (twoQuadraticForm_eq_bloch b00 b01 b10 b11 hxnorm).symm
    · rintro _ ⟨r, hr, rfl⟩
      have hLimage :=
        LinearMap.image_unitSphere_eq_image_closedUnitBall_of_finrank_lt L hdim
      have hLr : L r ∈ L '' Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨r, hr, rfl⟩
      rw [← hLimage] at hLr
      obtain ⟨s, hs, hLs⟩ := hLr
      obtain ⟨x, hxnorm, hbloch⟩ := exists_unit_blochVector_eq hs
      refine ⟨x, mem_sphere_zero_iff_norm.mpr hxnorm, ?_⟩
      rw [twoQuadraticForm_eq_bloch b00 b01 b10 b11 hxnorm, hbloch]
      simpa [c, L] using congrArg (fun z ↦ c + z) hLs
  rw [himage]
  have hconv :=
    ((convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).linear_image L).translate c
  simpa only [Set.image_image, Function.comp_apply] using hconv

/-- A complex linear isometry out of `ℂ²` is determined by its values on the two coordinate
vectors. -/
theorem LinearIsometry.finTwo_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : EuclideanVector (Fin 2) →ₗᵢ[ℂ] E) (u : EuclideanVector (Fin 2)) :
    J u = u 0 • J (EuclideanSpace.single 0 1) +
      u 1 • J (EuclideanSpace.single 1 1) := by
  have hu : u = u 0 • EuclideanSpace.single 0 1 +
      u 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    J u = J (u 0 • EuclideanSpace.single 0 1 +
        u 1 • EuclideanSpace.single 1 1) := congrArg J hu
    _ = u 0 • J (EuclideanSpace.single 0 1) +
        u 1 • J (EuclideanSpace.single 1 1) := by
      rw [map_add, map_smul, map_smul]

/-- Compression to any isometric copy of `ℂ²` has exactly the four-coefficient quadratic form
used above. -/
theorem inner_linearIsometry_apply_operator_eq_twoQuadraticForm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (J : EuclideanVector (Fin 2) →ₗᵢ[ℂ] E) (T : E →L[ℂ] E)
    (u : EuclideanVector (Fin 2)) :
    ⟪J u, T (J u)⟫_ℂ =
      twoQuadraticForm
        ⟪J (EuclideanSpace.single 0 1),
          T (J (EuclideanSpace.single 0 1))⟫_ℂ
        ⟪J (EuclideanSpace.single 0 1),
          T (J (EuclideanSpace.single 1 1))⟫_ℂ
        ⟪J (EuclideanSpace.single 1 1),
          T (J (EuclideanSpace.single 0 1))⟫_ℂ
        ⟪J (EuclideanSpace.single 1 1),
          T (J (EuclideanSpace.single 1 1))⟫_ℂ u := by
  rw [CrouzeixConjecture.LinearIsometry.finTwo_apply J u,
    map_add, map_smul, map_smul]
  simp only [twoQuadraticForm, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  ring

/-- The Toeplitz--Hausdorff theorem for the manuscript's numerical range and inner-product
convention. -/
theorem numericalRange_convex
    {n : Type*} [Fintype n] [DecidableEq n] (A : SquareMatrix n) :
    Convex ℝ (numericalRange A) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  let v : Fin 2 → EuclideanVector n := ![x, y]
  by_cases hv : LinearIndependent ℂ v
  · let S : Submodule ℂ (EuclideanVector n) :=
      Submodule.span ℂ (Set.range v)
    have hfinrank : Module.finrank ℂ S = 2 := by
      simpa [S] using finrank_span_eq_card hv
    let basisS : OrthonormalBasis (Fin 2) ℂ S :=
      (stdOrthonormalBasis ℂ S).reindex (finCongr hfinrank)
    let Jsub : EuclideanVector (Fin 2) ≃ₗᵢ[ℂ] S :=
      basisS.repr.symm
    let J : EuclideanVector (Fin 2) →ₗᵢ[ℂ] EuclideanVector n :=
      S.subtypeₗᵢ.comp Jsub.toLinearIsometry
    have hxS : x ∈ S := by
      apply Submodule.subset_span
      exact ⟨0, by simp [v]⟩
    have hyS : y ∈ S := by
      apply Submodule.subset_span
      exact ⟨1, by simp [v]⟩
    let ux : EuclideanVector (Fin 2) := Jsub.symm ⟨x, hxS⟩
    let uy : EuclideanVector (Fin 2) := Jsub.symm ⟨y, hyS⟩
    have hJux : J ux = x := by
      simp [J, ux]
    have hJuy : J uy = y := by
      simp [J, uy]
    have hux : ‖ux‖ = 1 := by
      calc
        ‖ux‖ = ‖J ux‖ := (J.norm_map ux).symm
        _ = ‖x‖ := by rw [hJux]
        _ = 1 := hx
    have huy : ‖uy‖ = 1 := by
      calc
        ‖uy‖ = ‖J uy‖ := (J.norm_map uy).symm
        _ = ‖y‖ := by rw [hJuy]
        _ = 1 := hy
    let e0 : EuclideanVector (Fin 2) := EuclideanSpace.single 0 1
    let e1 : EuclideanVector (Fin 2) := EuclideanSpace.single 1 1
    let b00 : ℂ := ⟪J e0, euclideanOperator A (J e0)⟫_ℂ
    let b01 : ℂ := ⟪J e0, euclideanOperator A (J e1)⟫_ℂ
    let b10 : ℂ := ⟪J e1, euclideanOperator A (J e0)⟫_ℂ
    let b11 : ℂ := ⟪J e1, euclideanOperator A (J e1)⟫_ℂ
    let q : EuclideanVector (Fin 2) → ℂ :=
      twoQuadraticForm b00 b01 b10 b11
    have hcompress (u : EuclideanVector (Fin 2)) :
        ⟪J u, euclideanOperator A (J u)⟫_ℂ = q u := by
      simpa [q, b00, b01, b10, b11, e0, e1] using
        inner_linearIsometry_apply_operator_eq_twoQuadraticForm
          J (euclideanOperator A) u
    have hqux : q ux = ⟪x, euclideanOperator A x⟫_ℂ := by
      simpa [hJux] using (hcompress ux).symm
    have hquy : q uy = ⟪y, euclideanOperator A y⟫_ℂ := by
      simpa [hJuy] using (hcompress uy).symm
    have hqconv : Convex ℝ
        (q '' Metric.sphere (0 : EuclideanVector (Fin 2)) 1) := by
      simpa [q] using convex_twoQuadraticForm_unitSphere b00 b01 b10 b11
    have hqux_mem : q ux ∈ q '' Metric.sphere
        (0 : EuclideanVector (Fin 2)) 1 :=
      ⟨ux, mem_sphere_zero_iff_norm.mpr hux, rfl⟩
    have hquy_mem : q uy ∈ q '' Metric.sphere
        (0 : EuclideanVector (Fin 2)) 1 :=
      ⟨uy, mem_sphere_zero_iff_norm.mpr huy, rfl⟩
    obtain ⟨u, hu, hqcomb⟩ := hqconv hqux_mem hquy_mem ha hb hab
    refine ⟨J u, ?_, ?_⟩
    · rw [J.norm_map]
      exact mem_sphere_zero_iff_norm.mp hu
    · rw [hcompress u, hqcomb, hqux, hquy]
  · have hy0 : y ≠ 0 := by
      intro hyzero
      rw [hyzero, norm_zero] at hy
      norm_num at hy
    have hnot : ¬ ∀ c : ℂ, c • y ≠ x := by
      intro hall
      apply hv
      rw [linearIndependent_fin2]
      simpa [v] using And.intro hy0 hall
    obtain ⟨c, hc⟩ := not_forall.mp hnot
    have hcy : c • y = x := Classical.not_not.mp hc
    have hcnorm : ‖c‖ = 1 := by
      have h := hx
      rw [← hcy, norm_smul, hy, mul_one] at h
      exact h
    have hcc : conj c * c = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hcnorm]
      norm_num
    have hquadratic :
        ⟪x, euclideanOperator A x⟫_ℂ =
          ⟪y, euclideanOperator A y⟫_ℂ := by
      rw [← hcy, map_smul, inner_smul_left, inner_smul_right,
        ← mul_assoc, hcc, one_mul]
    refine ⟨y, hy, ?_⟩
    rw [hquadratic, ← add_smul, hab, one_smul]

end CrouzeixConjecture
