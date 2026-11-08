-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GroundUpperProofs
public import TensorPCA.MaximumProofs
public import Mathlib.Data.Fin.VecNotation

/-!
# The finite Gaussian slice decomposition

A fixed-axis sphere slice is parameterized explicitly by its remaining unit
coordinates. Equality of expected Gaussian suprema follows from increment comparison in both directions; no process-law or independent
constant hypothesis is introduced.
-/
@[expose] public section
namespace TensorPCA.SliceDecompositionProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal
noncomputable section

/-- Equal increment metrics imply equal actual expected suprema even when the
canonical Gaussian coefficient spaces have different finite index types. -/
theorem expected_supremum_eq_of_increment_eq {V ι κ : Type*}
    [TopologicalSpace V] [CompactSpace V] [Nonempty V] [Fintype ι] [Fintype κ]
    (a : V → EuclideanSpace ℝ ι) (b : V → EuclideanSpace ℝ κ)
    (ha : Continuous a) (hb : Continuous b)
    (hinc : ∀ v u, ‖a v-a u‖ = ‖b v-b u‖) :
    (∫ g, (⨆ v, inner ℝ (a v) g) ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ∫ g, (⨆ v, inner ℝ (b v) g) ∂stdGaussian (EuclideanSpace ℝ κ) := by
  classical
  exact le_antisymm
    (GaussianMaximumComparisonProofs.expected_supremum_comparison a b ha hb
      (fun v u ↦ (hinc v u).le))
    (GaussianMaximumComparisonProofs.expected_supremum_comparison b a hb ha
      (fun v u ↦ (hinc v u).ge))

/-- The fixed first coordinate direction in the ambient N+1-dimensional space. -/
def firstAxis (N : ℕ) : Model.Vector (N+1) := (EuclideanSpace.basisFun (Fin (N+1)) ℝ) 0

/-- The explicit overlap-slice parameterization in ordered coordinates. -/
def sliceVector {N : ℕ} (m : ℝ) (u : Model.Vector N) : Model.Vector (N+1) :=
  WithLp.toLp 2 (Fin.cons (α := fun _ : Fin (N+1) ↦ ℝ) m (fun i ↦ Real.sqrt (1-m^2)*u i))

/-- The remaining coordinates of an ambient vector. -/
def tailVector {N : ℕ} (v : Model.Vector (N+1)) : Model.Vector N :=
  WithLp.toLp 2 (fun i ↦ v i.succ)

@[simp] theorem sliceVector_zero {N : ℕ} (m : ℝ) (u : Model.Vector N) :
    sliceVector m u 0 = m := by simp [sliceVector]

@[simp] theorem sliceVector_succ {N : ℕ} (m : ℝ) (u : Model.Vector N) (i : Fin N) :
    sliceVector m u i.succ = Real.sqrt (1-m^2)*u i := by simp [sliceVector]

@[simp] theorem tailVector_apply {N : ℕ} (v : Model.Vector (N+1)) (i : Fin N) :
    tailVector v i = v i.succ := rfl

theorem firstAxis_norm (N : ℕ) : ‖firstAxis N‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (N+1)) ℝ).orthonormal.norm_eq_one 0

@[simp] theorem inner_firstAxis {N : ℕ} (v : Model.Vector (N+1)) :
    inner ℝ v (firstAxis N) = v 0 := by
  change inner ℝ v ((EuclideanSpace.basisFun (Fin (N+1)) ℝ) 0) = v 0
  rw [real_inner_comm, EuclideanSpace.basisFun_inner]

theorem norm_sq_head_tail {N : ℕ} (v : Model.Vector (N+1)) :
    ‖v‖^2 = (v 0)^2+‖tailVector v‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_succ]
  rfl

theorem sliceVector_inner {N : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (u v : Model.Vector N) :
    inner ℝ (sliceVector m u) (sliceVector m v) = m^2+(1-m^2)*inner ℝ u v := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fin.sum_univ_succ]
  simp only [sliceVector_zero, sliceVector_succ]
  have ht (i : Fin N) : (Real.sqrt (1-m^2)*v i)*(Real.sqrt (1-m^2)*u i) =
      (1-m^2)*(v i*u i) := by
    calc
      _ = (Real.sqrt (1-m^2))^2*(v i*u i) := by ring
      _ = _ := by rw [Real.sq_sqrt (VariationalProofs.one_sub_sq_nonneg hm)]
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

theorem continuous_sliceVector (N : ℕ) (m : ℝ) : Continuous (sliceVector (N := N) m) := by
  change Continuous (fun u : Model.Vector N ↦ WithLp.toLp 2
    (Fin.cons (α := fun _ : Fin (N+1) ↦ ℝ) m (fun i ↦ Real.sqrt (1-m^2)*u i)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (N+1) ↦ ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using (continuous_const : Continuous (fun _ : Model.Vector N ↦ m))
  · simpa only [Fin.cons_succ] using
      ((PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) j).const_mul (Real.sqrt (1-m^2)))

theorem sliceVector_norm_sq {N : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (u : Model.Vector N) :
    ‖sliceVector m u‖^2 = m^2+(1-m^2)*‖u‖^2 := by
  rw [← real_inner_self_eq_norm_sq, sliceVector_inner hm, real_inner_self_eq_norm_sq]

theorem sliceVector_mem_slice {N : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {u : Model.Vector N} (hu : u ∈ Model.unitSphere N) :
    sliceVector m u ∈ {v ∈ Model.unitSphere (N+1) | inner ℝ v (firstAxis N) = m} := by
  constructor
  · change ‖sliceVector m u‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [sliceVector_norm_sq hm, show ‖u‖ = 1 from hu, one_pow]
    ring
  · rw [inner_firstAxis, sliceVector_zero]

theorem tailVector_norm_on_slice {N : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {v : Model.Vector (N+1)}
    (hv : v ∈ {v ∈ Model.unitSphere (N+1) | inner ℝ v (firstAxis N) = m}) :
    ‖tailVector v‖ = Real.sqrt (1-m^2) := by
  have hh : v 0 = m := by simpa only [inner_firstAxis] using hv.2
  have hn := norm_sq_head_tail v
  rw [show ‖v‖ = 1 from hv.1, hh] at hn
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (VariationalProofs.one_sub_sq_nonneg hm)]
  nlinarith [hn]

/-- The explicit coordinate parameterization covers the entire physical slice.
A fixed unit fallback at zero tail also handles the endpoint overlaps ±1. -/
theorem exists_sliceVector {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {v : Model.Vector (N+1)}
    (hv : v ∈ {v ∈ Model.unitSphere (N+1) | inner ℝ v (firstAxis N) = m}) :
    ∃ u ∈ Model.unitSphere N, sliceVector m u = v := by
  let t := tailVector v
  have htNorm : ‖t‖ = Real.sqrt (1-m^2) := tailVector_norm_on_slice hm hv
  have hv0 : v 0 = m := by simpa only [inner_firstAxis] using hv.2
  by_cases ht : t = 0
  · obtain ⟨u, hu⟩ := Geometry.unitSphere_nonempty hN
    refine ⟨u, hu, ?_⟩
    have hs : Real.sqrt (1-m^2) = 0 := by rw [← htNorm, ht, norm_zero]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [sliceVector_zero]
      exact hv0.symm
    · rw [sliceVector_succ, hs, zero_mul]
      have hj := congrArg (fun z : Model.Vector N ↦ z j) ht
      have hz : v j.succ = 0 := by simpa only [t, tailVector_apply, PiLp.zero_apply] using hj
      exact hz.symm
  · refine ⟨Model.normalize t, Model.norm_normalize t ht, ?_⟩
    have hscale : Real.sqrt (1-m^2) • Model.normalize t = t := by
      rw [← htNorm, Model.normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ht), one_smul]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [sliceVector_zero]
      exact hv0.symm
    · rw [sliceVector_succ]
      have hj := congrArg (fun z : Model.Vector N ↦ z j) hscale
      simpa only [PiLp.smul_apply, smul_eq_mul, t, tailVector_apply] using hj

theorem sliceVector_image_unitSphere {N : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    sliceVector m '' Model.unitSphere N =
      {v ∈ Model.unitSphere (N+1) | inner ℝ v (firstAxis N) = m} := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact sliceVector_mem_slice hm hu
  · exact exists_sliceVector hN hm

theorem physical_slice_increment_sq {N k : ℕ} {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    {u v : Model.Vector N} (hu : u ∈ Model.unitSphere N) (hv : v ∈ Model.unitSphere N) :
    ‖Model.feature k (sliceVector m u)-Model.feature k (sliceVector m v)‖^2 =
      2*(1-(m^2+(1-m^2)*inner ℝ u v)^k) := by
  rw [norm_sub_sq_real, Geometry.feature_unit_norm _ (sliceVector_mem_slice hm hu).1,
    Geometry.feature_unit_norm _ (sliceVector_mem_slice hm hv).1,
    Geometry.feature_inner, sliceVector_inner hm]
  ring

theorem scaled_slice_increment_sq {N k : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) {u v : Model.Vector N}
    (hu : u ∈ Model.unitSphere N) (hv : v ∈ Model.unitSphere N) :
    ‖(Real.sqrt N)⁻¹ • GroundState.sliceFeature k m u-
      (Real.sqrt N)⁻¹ • GroundState.sliceFeature k m v‖^2 =
      2*(1-(m^2+(1-m^2)*inner ℝ u v)^k) := by
  have hsf : ‖GroundState.sliceFeature k m u-GroundState.sliceFeature k m v‖^2 =
      2*(N : ℝ)*(1-(m^2+(1-m^2)*inner ℝ u v)^k) := by
    rw [norm_sub_sq_real, GroundUpperProofs.sliceFeature_norm_sq hm hu,
      GroundUpperProofs.sliceFeature_norm_sq hm hv, GroundUpperProofs.sliceFeature_inner hm]
    unfold Scalar.xiSlice
    ring
  rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), hsf]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  calc
    _ = ((N : ℝ)⁻¹*(N : ℝ))*(2*(1-(m^2+(1-m^2)*inner ℝ u v)^k)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hNz, one_mul]

theorem slice_increment_eq {N k : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) {u v : Model.Vector N}
    (hu : u ∈ Model.unitSphere N) (hv : v ∈ Model.unitSphere N) :
    ‖Model.feature k (sliceVector m u)-Model.feature k (sliceVector m v)‖ =
      ‖(Real.sqrt N)⁻¹ • GroundState.sliceFeature k m u-
        (Real.sqrt N)⁻¹ • GroundState.sliceFeature k m v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [physical_slice_increment_sq hm hu hv, scaled_slice_increment_sq hN hm hu hv]

/-- Two checked Gaussian comparisons identify the actual expected noise
suprema; the constant covariance block cancels in the increment metric. -/
theorem expected_slice_supremum_eq {N k : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    (∫ w : Model.Tensor (N+1) k, (⨆ u : Model.unitSphere N,
      inner ℝ (Model.feature k (sliceVector m u)) w) ∂stdGaussian (Model.Tensor (N+1) k)) =
      ∫ g : GroundState.Disorder N k, (⨆ u : Model.unitSphere N,
        inner ℝ ((Real.sqrt N)⁻¹ • GroundState.sliceFeature k m u) g)
          ∂stdGaussian (GroundState.Disorder N k) := by
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have huCont : Continuous (fun u : Model.unitSphere N ↦ (u : Model.Vector N)) := continuous_subtype_val
  have hMap : Continuous (fun u : Model.unitSphere N ↦ sliceVector m (u : Model.Vector N)) :=
    (continuous_sliceVector N m).comp huCont
  have ha : Continuous (fun u : Model.unitSphere N ↦ Model.feature k (sliceVector m u)) :=
    (Model.continuous_feature (N+1) k).comp hMap
  have hGround : Continuous (fun u : Model.unitSphere N ↦ GroundState.sliceFeature k m (u : Model.Vector N)) :=
    (GroundUpperProofs.continuous_sliceFeature N k m).comp huCont
  have hb : Continuous (fun u : Model.unitSphere N ↦
      (Real.sqrt N)⁻¹ • GroundState.sliceFeature (N := N) k m (u : Model.Vector N)) :=
    (continuous_const_smul ((Real.sqrt N)⁻¹)).comp hGround
  exact expected_supremum_eq_of_increment_eq _ _ ha hb
    (fun u v ↦ slice_increment_eq hN hm u.property v.property)

/-- A continuous compact supremum commutes with a nonnegative affine map. -/
theorem ciSup_affine {V : Type*} [TopologicalSpace V] [CompactSpace V] [Nonempty V]
    (f : V → ℝ) (hf : Continuous f) (c d : ℝ) (hd : 0 ≤ d) :
    (⨆ v, c+d*f v) = c+d*(⨆ v, f v) := by
  obtain ⟨v, _, hv⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  have hb : BddAbove (range f) := (isCompact_range hf).bddAbove
  have hbf : BddAbove (range (fun u ↦ c+d*f u)) :=
    (isCompact_range (continuous_const.add (hf.const_mul d))).bddAbove
  have hs : (⨆ u, f u) = f v :=
    le_antisymm (ciSup_le (fun u ↦ hv (mem_univ u))) (le_ciSup hb v)
  rw [hs]
  exact le_antisymm (ciSup_le (fun u ↦ add_le_add (le_refl c) (mul_le_mul_of_nonneg_left
    (hv (mem_univ u)) hd))) (le_ciSup hbf v)

/-- The actual fixed-axis constrained maximum as a compact noise supremum. -/
theorem constrainedMaximum_firstAxis {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) (w : Model.Tensor (N+1) k) :
    Model.constrainedMaximum lam (firstAxis N) w m = lam*m^k +
      (Real.sqrt (N+1))⁻¹*(⨆ u : Model.unitSphere N,
        inner ℝ (Model.feature k (sliceVector m u)) w) := by
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have hc : Continuous (fun u : Model.unitSphere N ↦
      inner ℝ (Model.feature k (sliceVector m u)) w) :=
    (((Model.continuous_feature (N+1) k).comp (continuous_sliceVector N m)).comp
      continuous_subtype_val).inner continuous_const
  unfold Model.constrainedMaximum
  rw [← sliceVector_image_unitSphere hN hm, Set.image_image, Set.image_eq_range]
  simp only [Model.score, Nat.cast_add, Nat.cast_one]
  rw [← iSup]
  simp_rw [div_eq_mul_inv, mul_comm _ ((Real.sqrt (N+1))⁻¹)]
  exact ciSup_affine _ hc _ _ (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The scaled slice field's supremum, with its exact finite dimension factor. -/
theorem scaled_slice_supremum {N k : ℕ} (hN : 0 < N) (m : ℝ)
    (g : GroundState.Disorder N k) :
    (⨆ u : Model.unitSphere N,
      inner ℝ ((Real.sqrt N)⁻¹ • GroundState.sliceFeature k m u) g) =
    (Real.sqrt N)⁻¹*(⨆ u : Model.unitSphere N,
      inner ℝ (GroundState.sliceFeature k m u) g) := by
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have hc : Continuous (fun u : Model.unitSphere N ↦
      inner ℝ (GroundState.sliceFeature k m u) g) :=
    ((GroundUpperProofs.continuous_sliceFeature N k m).comp continuous_subtype_val).inner continuous_const
  simp_rw [real_inner_smul_left]
  simpa only [zero_add] using ciSup_affine _ hc 0 ((Real.sqrt N)⁻¹)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Exact finite mean decomposition for the physical random-signal slice. -/
theorem constrainedMaximum_mean_decomposition {N k : ℕ} (hN : 0 < N) (lam : ℝ)
    {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    (∫ z : Model.Vector (N+1) × Model.Tensor (N+1) k,
      Model.constrainedMaximum lam z.1 z.2 m ∂Model.experimentLaw (N+1) k) =
    lam*m^k + Real.sqrt N / Real.sqrt (N+1)*GroundState.expectedSliceGround N k m := by
  classical
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have hc : Continuous (fun u : Model.unitSphere N ↦ Model.feature k (sliceVector m (u : Model.Vector N))) :=
    ((Model.continuous_feature (N+1) k).comp (continuous_sliceVector N m)).comp continuous_subtype_val
  have hInt := GaussianMaximumComparisonProofs.supremum_integrable _ hc
  rw [MaximumProofs.constrainedMaximum_experiment_mean (by omega) lam m
    (abs_le.mpr hm) (firstAxis N) (firstAxis_norm N)]
  change (∫ w, Model.constrainedMaximum lam (firstAxis N) w m
    ∂stdGaussian (Model.Tensor (N+1) k)) = _
  simp_rw [constrainedMaximum_firstAxis hN lam hm]
  rw [integral_add (integrable_const _) (hInt.const_mul _)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_const_mul]
  rw [expected_slice_supremum_eq hN hm]
  simp_rw [scaled_slice_supremum hN m]
  rw [integral_const_mul]
  unfold GroundState.expectedSliceGround
  have hsup (g : GroundState.Disorder N k) :
      sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
      ⨆ u : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m u) g := by
    rw [iSup, Set.image_eq_range]
  simp_rw [hsup]
  rw [integral_div]
  have hNz : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsNz : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have hinv : (Real.sqrt (N : ℝ))⁻¹ = Real.sqrt N / N := by
    apply (eq_div_iff hNz).mpr
    apply (inv_mul_eq_iff_eq_mul₀ hsNz).mpr
    rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hinv]
  ring

/-- A centered continuous compact Gaussian field has nonnegative expected supremum. -/
theorem expected_supremum_nonneg {V ι : Type*}
    [TopologicalSpace V] [CompactSpace V] [Nonempty V] [Fintype ι]
    (a : V → EuclideanSpace ℝ ι) (ha : Continuous a) :
    0 ≤ ∫ g, (⨆ v, inner ℝ (a v) g) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  classical
  have h := GaussianMaximumComparisonProofs.expected_supremum_comparison
    (fun _ : V ↦ (0 : EuclideanSpace ℝ ι)) a continuous_const ha (fun _ _ ↦ by simp)
  simpa only [inner_zero_left, ciSup_const, integral_zero] using h

/-- The independently defined slice Gaussian ground energy is nonnegative. -/
theorem expectedSliceGround_nonneg {N k : ℕ} (hN : 0 < N) (m : ℝ) :
    0 ≤ GroundState.expectedSliceGround N k m := by
  have : Nonempty (Model.unitSphere N) := (Geometry.unitSphere_nonempty hN).to_subtype
  have : CompactSpace (Model.unitSphere N) :=
    isCompact_iff_compactSpace.mp (Geometry.unitSphere_isCompact N)
  have hc : Continuous (fun u : Model.unitSphere N ↦
      GroundState.sliceFeature k m (u : Model.Vector N)) :=
    (GroundUpperProofs.continuous_sliceFeature N k m).comp continuous_subtype_val
  have H := expected_supremum_nonneg _ hc
  unfold GroundState.expectedSliceGround
  have hsup (g : GroundState.Disorder N k) :
      sSup ((fun x ↦ inner ℝ (GroundState.sliceFeature k m x) g) '' Model.unitSphere N) =
      ⨆ u : Model.unitSphere N, inner ℝ (GroundState.sliceFeature k m u) g := by
    rw [iSup, Set.image_eq_range]
  simp_rw [hsup]
  rw [integral_div]
  exact div_nonneg H (Nat.cast_nonneg N)

/-- A uniform dimension-free bound for the actual slice energy. -/
theorem abs_expectedSliceGround_le {N k : ℕ} (hN : 0 < N) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    |GroundState.expectedSliceGround N k m| ≤ Real.sqrt k := by
  rw [abs_of_nonneg (expectedSliceGround_nonneg hN m)]
  apply (GroundUpperProofs.expectedSliceGround_le hN hm).trans
  apply Real.sqrt_le_sqrt
  have hmul := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg m)
  nlinarith

/-- The exact finite dimension prefactor tends to one. -/
theorem sqrt_dimension_ratio_tendsto :
    Tendsto (fun n : ℕ ↦ Real.sqrt (n+1 : ℕ) / Real.sqrt (n+2 : ℕ)) atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ ↦ (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ le_add_of_nonneg_right (le_of_lt zero_lt_two))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht : Tendsto (fun n : ℕ ↦ 1-1/((n : ℝ)+2)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (hd.const_div_atTop (1 : ℝ))
  have heq (n : ℕ) : 1-1/((n : ℝ)+2) = ((n+1 : ℕ) : ℝ)/(n+2 : ℕ) := by
    push_cast
    field_simp
    ring
  simp_rw [heq] at ht
  have hs := Real.continuous_sqrt.tendsto (1 : ℝ) |>.comp ht
  simpa only [Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_one] using hs

/-- The physical slice decomposition, without any ground-state-limit premise. -/
theorem sliceDecomposition (k : ℕ) (lam : ℝ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.SliceDecomposition k lam m := by
  unfold GroundState.SliceDecomposition
  have hz : Tendsto (fun n : ℕ ↦
      |Real.sqrt (n+1 : ℕ)/Real.sqrt (n+2 : ℕ)-1| * Real.sqrt k) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      (sqrt_dimension_ratio_tendsto.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))).abs.mul_const (Real.sqrt k)
  apply squeeze_zero_norm _ hz
  intro n
  rw [constrainedMaximum_mean_decomposition (Nat.succ_pos n) lam hm]
  have heq (a b c : ℝ) : (a+b*c)-(a+c) = (b-1)*c := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  have hDim : ((n+2 : ℕ) : ℝ) = (n.succ : ℝ)+1 := by push_cast; ring
  rw [hDim]
  exact mul_le_mul_of_nonneg_left (abs_expectedSliceGround_le (k := k) (Nat.succ_pos n) hm)
    (abs_nonneg _)

end
end TensorPCA.SliceDecompositionProofs
