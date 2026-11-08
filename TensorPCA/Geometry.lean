-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Model
public import TensorPCA.GaussianConcentrationBridge
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Ordered tensor geometry and the angular prior

The short finite-product inner-product argument adapts the Apache-2.0 proof
pattern `tensorFeature_inner` in the following immutable public source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/PureTensorJetFeatures.lean
Its definitions and imports are not copied; these results concern the reviewed
`TensorPCA.Model.feature` directly. The finite distributivity identity is the
canonical Mathlib theorem `Fintype.prod_sum`.
-/
@[expose] public section

namespace TensorPCA.Geometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace ENNReal

@[simp] theorem feature_apply {N k : ℕ} (x : Model.Vector N) (i : Fin k → Fin N) :
    Model.feature k x i = ∏ j, x (i j) := rfl

/-- Ordered tensor products reproduce the kth power of the vector overlap. -/
theorem feature_inner {N k : ℕ} (x y : Model.Vector N) :
    inner ℝ (Model.feature k x) (Model.feature k y) = (inner ℝ x y)^k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, feature_apply,
    ← Finset.prod_mul_distrib]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (Fintype.prod_sum (fun (_ : Fin k) (i : Fin N) ↦ y i * x i)).symm

/-- Frobenius norm of an actual tensor power. -/
theorem feature_norm_sq {N k : ℕ} (x : Model.Vector N) :
    ‖Model.feature k x‖^2 = (‖x‖^2)^k := by
  rw [← real_inner_self_eq_norm_sq, feature_inner, real_inner_self_eq_norm_sq]

theorem feature_norm {N k : ℕ} (x : Model.Vector N) :
    ‖Model.feature k x‖ = ‖x‖^k := by
  apply (sq_eq_sq₀ (norm_nonneg _) (pow_nonneg (norm_nonneg x) k)).mp
  rw [feature_norm_sq]
  ring

theorem feature_unit_norm {N k : ℕ} (x : Model.Vector N) (hx : x ∈ Model.unitSphere N) :
    ‖Model.feature k x‖ = 1 := by
  rw [feature_norm, show ‖x‖ = 1 from hx, one_pow]

/-- The canonical noise covariance of the spherical Hamiltonian. -/
theorem covariance_features {N k : ℕ} (x y : Model.Vector N) :
    covarianceBilin (Model.noiseLaw N k) (Model.feature k x) (Model.feature k y) =
      (inner ℝ x y)^k := by
  rw [Model.noiseLaw, covarianceBilin_stdGaussian]
  exact feature_inner x y

/-- Scalar homogeneity of the genuine ordered tensor power. -/
theorem feature_smul {N k : ℕ} (a : ℝ) (x : Model.Vector N) :
    Model.feature k (a • x) = a^k • Model.feature k x := by
  ext i
  change (∏ j : Fin k, a * x (i j)) = a^k * ∏ j : Fin k, x (i j)
  rw [Finset.prod_mul_distrib]
  simp

/-- Evaluating on a unit tensor feature is one-Lipschitz in the observation. -/
theorem score_sub_le {N k : ℕ} (x : Model.Vector N) (hx : x ∈ Model.unitSphere N)
    (y z : Model.Tensor N k) : |Model.score y x - Model.score z x| ≤ ‖y-z‖ := by
  change |inner ℝ (Model.feature k x) y - inner ℝ (Model.feature k x) z| ≤ ‖y-z‖
  rw [← inner_sub_right]
  calc
    _ ≤ ‖Model.feature k x‖ * ‖y-z‖ := abs_real_inner_le_norm _ _
    _ = ‖y-z‖ := by rw [feature_unit_norm x hx, one_mul]

/-- Positive-dimensional standard Gaussian measure does not charge the origin.
This follows directly from its product-coordinate realization. -/
theorem gaussian_origin_null {N : ℕ} (hN : 0 < N) :
    (stdGaussian (Model.Vector N)) {0} = 0 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  rw [← map_pi_eq_stdGaussian, Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hp : (WithLp.toLp 2) ⁻¹' ({0} : Set (Model.Vector N)) =
      ({0} : Set (Fin N → ℝ)) := by
    ext x
    simp
  rw [hp]
  exact measure_singleton 0

theorem gaussian_ne_zero_ae {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x ∂stdGaussian (Model.Vector N), x ≠ 0 := by
  rw [ae_iff]
  simpa using gaussian_origin_null hN

/-- The actual angular prior is supported on the physical unit sphere. -/
theorem spherePrior_norm_ae {N : ℕ} (hN : 0 < N) :
    ∀ᵐ x ∂Model.spherePrior N, ‖x‖ = 1 := by
  unfold Model.spherePrior
  apply (ae_map_iff (Model.measurable_normalize N).aemeasurable
    ((measurableSet_singleton (1 : ℝ)).preimage measurable_norm)).mpr
  exact (gaussian_ne_zero_ae hN).mono (fun x hx ↦ Model.norm_normalize x hx)

/-- Radial normalization commutes with every orthogonal transformation. -/
theorem normalize_isometry {N : ℕ} (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N)
    (x : Model.Vector N) : Model.normalize (U x) = U (Model.normalize x) := by
  simp [Model.normalize]

/-- Exact orthogonal invariance of the actual probability law. -/
theorem spherePrior_rotation_invariant {N : ℕ}
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) :
    (Model.spherePrior N).map U = Model.spherePrior N := by
  unfold Model.spherePrior
  calc
    ((stdGaussian (Model.Vector N)).map Model.normalize).map U =
        ((stdGaussian (Model.Vector N)).map U).map Model.normalize := by
      rw [Measure.map_map U.continuous.measurable (Model.measurable_normalize N),
        Measure.map_map (Model.measurable_normalize N) U.continuous.measurable]
      congr 1
      funext x
      exact (normalize_isometry U x).symm
    _ = _ := by rw [stdGaussian_map U]

/-- The physical sphere is nonempty in every positive dimension. -/
theorem unitSphere_nonempty {N : ℕ} (hN : 0 < N) : (Model.unitSphere N).Nonempty := by
  refine ⟨(EuclideanSpace.basisFun (Fin N) ℝ) ⟨0, hN⟩, ?_⟩
  exact (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one _

theorem unitSphere_isCompact (N : ℕ) : IsCompact (Model.unitSphere N) := by
  simpa only [Model.unitSphere, Metric.sphere, dist_zero_right] using
    isCompact_sphere (0 : Model.Vector N) 1

/-- Every likelihood score image has a concrete upper bound. -/
theorem score_image_bddAbove {N k : ℕ} (y : Model.Tensor N k) :
    BddAbove (Model.score y '' Model.unitSphere N) := by
  refine ⟨‖y‖, ?_⟩
  rintro b ⟨x, hx, rfl⟩
  calc
    Model.score y x ≤ |Model.score y x| := le_abs_self _
    _ ≤ ‖Model.feature k x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ = ‖y‖ := by rw [feature_unit_norm x hx, one_mul]

/-- The actual unnormalized maximum is attained, with no uniqueness premise. -/
theorem exists_maximizer {N k : ℕ} (hN : 0 < N) (y : Model.Tensor N k) :
    ∃ x ∈ Model.unitSphere N, ∀ z ∈ Model.unitSphere N, Model.score y z ≤ Model.score y x := by
  have hc : Continuous (Model.score y) :=
    (Model.continuous_feature N k).inner continuous_const
  exact (unitSphere_isCompact N).exists_isMaxOn (unitSphere_nonempty hN) hc.continuousOn

/-- Common Lipschitz control passes through the genuine sphere supremum. -/
theorem score_sup_compare {N k : ℕ} (hN : 0 < N) (y z : Model.Tensor N k) :
    sSup (Model.score y '' Model.unitSphere N) ≤
      sSup (Model.score z '' Model.unitSphere N) + ‖y-z‖ := by
  apply csSup_le ((unitSphere_nonempty hN).image _)
  rintro b ⟨x, hx, rfl⟩
  have hclose : Model.score y x ≤ Model.score z x + ‖y-z‖ :=
    sub_le_iff_le_add'.mp ((le_abs_self _).trans (score_sub_le x hx y z))
  have hs := le_csSup (score_image_bddAbove z) ⟨x, hx, rfl⟩
  linarith

/-- Normalized maximum at a zero observation. -/
theorem normalizedMaximum_zero {N k : ℕ} (hN : 0 < N) :
    Model.normalizedMaximum (0 : Model.Tensor N k) = 0 := by
  have hf : Model.score (0 : Model.Tensor N k) = (fun _ : Model.Vector N ↦ (0 : ℝ)) := by
    funext x
    change inner ℝ (Model.feature k x) 0 = 0
    exact inner_zero_right _
  unfold Model.normalizedMaximum
  rw [hf, (unitSphere_nonempty hN).image_const (0 : ℝ), csSup_singleton, zero_div]

/-- The actual normalized maximum is 1/sqrt(N)-Lipschitz. -/
theorem normalizedMaximum_lipschitz {N k : ℕ} (hN : 0 < N) :
    LipschitzWith ((Real.sqrt N)⁻¹).toNNReal
      (Model.normalizedMaximum (N := N) (k := k)) := by
  apply LipschitzWith.of_le_add_mul' ((Real.sqrt N)⁻¹)
  intro y z
  calc
    Model.normalizedMaximum y ≤
        (sSup (Model.score z '' Model.unitSphere N) + ‖y-z‖) / Real.sqrt N :=
      div_le_div_of_nonneg_right (score_sup_compare hN y z) (Real.sqrt_nonneg _)
    _ = Model.normalizedMaximum z + (Real.sqrt N)⁻¹ * dist y z := by
      rw [Model.normalizedMaximum, add_div, dist_eq_norm]
      ring

/-- Translation by an arbitrary deterministic planted tensor preserves the bound. -/
theorem shiftedMaximum_lipschitz {N k : ℕ} (hN : 0 < N) (shift : Model.Tensor N k) :
    LipschitzWith ((Real.sqrt N)⁻¹).toNNReal
      (fun w : Model.Tensor N k ↦ Model.normalizedMaximum (shift+w)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simpa only [dist_add_left] using
    (normalizedMaximum_lipschitz (k := k) hN).dist_le_mul (shift+y) (shift+z)

/-- All finite moments of the null maximum are genuine Gaussian integrals. -/
theorem normalizedMaximum_memLp {N k : ℕ} (hN : 0 < N)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (Model.normalizedMaximum (N := N) (k := k)) p (Model.noiseLaw N k) := by
  simpa only [Function.comp_def, id_eq, Model.noiseLaw] using
    (normalizedMaximum_lipschitz (k := k) hN).comp_memLp (normalizedMaximum_zero hN)
      (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp)

/-- All finite moments also exist after an arbitrary deterministic signal shift. -/
theorem shiftedMaximum_memLp {N k : ℕ} (hN : 0 < N) (shift : Model.Tensor N k)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w : Model.Tensor N k ↦ Model.normalizedMaximum (shift+w)) p
      (Model.noiseLaw N k) := by
  have hW : MemLp (fun w : Model.Tensor N k ↦ shift+w) p (Model.noiseLaw N k) :=
    (memLp_const shift).add (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp)
  simpa only [Function.comp_def] using
    (normalizedMaximum_lipschitz (k := k) hN).comp_memLp (normalizedMaximum_zero hN) hW

/-- Exact Gaussian concentration for the genuine maximum after any fixed
signal shift. This applies to the null shift and to conditioning on a planted
vector; identification of conditional and annealed means is separate. -/
theorem shiftedMaximum_gaussian_tail {N k : ℕ} (hN : 0 < N) (shift : Model.Tensor N k)
    (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w | |Model.normalizedMaximum (shift+w) -
      ∫ v, Model.normalizedMaximum (shift+v) ∂Model.noiseLaw N k| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ) * t^2 / 2)) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (fun w : Model.Tensor N k ↦ Model.normalizedMaximum (shift+w))
    ((Real.sqrt N)⁻¹) t (inv_pos.mpr hs) ht (shiftedMaximum_lipschitz hN shift)
  have he : -t^2 / (2 * ((Real.sqrt N)⁻¹)^2) = -(N : ℝ)*t^2/2 := by
    field_simp [hs.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  simpa only [Model.noiseLaw, he] using hb

/-- Every continuous scalar observable has every moment under the actual sphere
prior, including essential boundedness. The bound comes from the compact sphere,
not a global boundedness assumption on the observable. -/
theorem spherePrior_continuous_memLp {N : ℕ} (hN : 0 < N)
    (F : Model.Vector N → ℝ) (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp F p (Model.spherePrior N) := by
  obtain ⟨C, hC⟩ := (unitSphere_isCompact N).bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  exact (spherePrior_norm_ae hN).mono (fun x hx ↦ hC ⟨x, hx, rfl⟩)

/-- Integrals of continuous scalar observables respect the proved orthogonal law. -/
theorem spherePrior_integral_comp_isometry {N : ℕ}
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (F : Model.Vector N → ℝ)
    (hF : Continuous F) :
    (∫ x, F (U x) ∂Model.spherePrior N) = ∫ x, F x ∂Model.spherePrior N := by
  have hm := integral_map (μ := Model.spherePrior N)
    U.continuous.measurable.aemeasurable hF.aestronglyMeasurable
  rw [spherePrior_rotation_invariant U] at hm
  exact hm.symm

/-- Equal-norm directions have identical projection moments under the actual
prior. Reflection supplies the orthogonal transformation, including u=v. -/
theorem projection_moment_eq_of_norm_eq {N : ℕ} (p : ℕ)
    (u v : Model.Vector N) (huv : ‖u‖ = ‖v‖) :
    (∫ x, (inner ℝ u x)^p ∂Model.spherePrior N) =
      ∫ x, (inner ℝ v x)^p ∂Model.spherePrior N := by
  let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (u-v))ᗮ.reflection
  have hu : U u = v := Submodule.reflection_sub huv
  have hi := spherePrior_integral_comp_isometry U (fun x ↦ (inner ℝ v x)^p)
    (by fun_prop)
  calc
    _ = ∫ x, (inner ℝ v (U x))^p ∂Model.spherePrior N := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← hu, U.inner_map_map]
    _ = _ := hi

theorem spherePrior_continuous_integrable {N : ℕ} (hN : 0 < N)
    (F : Model.Vector N → ℝ) (hF : Continuous F) : Integrable F (Model.spherePrior N) :=
  (spherePrior_continuous_memLp hN F hF 1).integrable le_rfl

/-- Coordinate moments do not depend on the selected coordinate. -/
theorem coordinate_moment_eq {N : ℕ} (p : ℕ) (i j : Fin N) :
    (∫ x : Model.Vector N, (x i)^p ∂Model.spherePrior N) =
      ∫ x : Model.Vector N, (x j)^p ∂Model.spherePrior N := by
  have h := projection_moment_eq_of_norm_eq p
    ((EuclideanSpace.basisFun (Fin N) ℝ) i) ((EuclideanSpace.basisFun (Fin N) ℝ) j)
    (by rw [(EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i,
      (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one j])
  simpa only [EuclideanSpace.basisFun_inner] using h

/-- Exact spherical coordinate second moment, proved from norm support and
orthogonal invariance rather than postulated as a prior property. -/
theorem coordinate_second_moment {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (∫ x : Model.Vector N, (x i)^2 ∂Model.spherePrior N) = 1 / (N : ℝ) := by
  let j : Fin N := ⟨0, hN⟩
  let A : ℝ := ∫ x : Model.Vector N, (x j)^2 ∂Model.spherePrior N
  have heq (i : Fin N) : (∫ x : Model.Vector N, (x i)^2 ∂Model.spherePrior N) = A :=
    coordinate_moment_eq 2 i j
  have hs := integral_finsetSum (μ := Model.spherePrior N) (s := Finset.univ)
    (f := fun (i : Fin N) (x : Model.Vector N) ↦ (x i)^2)
    (fun i _ ↦ spherePrior_continuous_integrable hN _ (by fun_prop))
  have hn : (∫ x : Model.Vector N, ∑ i : Fin N, (x i)^2 ∂Model.spherePrior N) = 1 := by
    calc
      _ = ∫ x : Model.Vector N, ‖x‖^2 ∂Model.spherePrior N := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (EuclideanSpace.real_norm_sq_eq x).symm
      _ = ∫ _x : Model.Vector N, (1 : ℝ) ∂Model.spherePrior N :=
        integral_congr_ae ((spherePrior_norm_ae hN).mono (fun x hx ↦ by dsimp; rw [hx, one_pow]))
      _ = 1 := by simp
  have hm : (N : ℝ)*A = 1 := by
    simpa only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      hs.symm.trans hn
  rw [heq i]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))).mpr
  simpa only [mul_comm] using hm

/-- Exact second moment for any deterministic unit direction. -/
theorem unit_projection_second_moment {N : ℕ} (hN : 0 < N)
    (u : Model.Vector N) (hu : ‖u‖ = 1) :
    (∫ x, (inner ℝ u x)^2 ∂Model.spherePrior N) = 1 / (N : ℝ) := by
  let i : Fin N := ⟨0, hN⟩
  have h := projection_moment_eq_of_norm_eq 2 u ((EuclideanSpace.basisFun (Fin N) ℝ) i)
    (by rw [hu, (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i])
  rw [h]
  simpa only [EuclideanSpace.basisFun_inner] using coordinate_second_moment hN i

/-- Mixed spherical fourth moments follow by comparing the fourth moments of
orthogonal coordinate sums and differences with a scaled coordinate. -/
theorem coordinate_mixed_fourth_moment {N : ℕ} (hN : 0 < N) (i j : Fin N)
    (hij : i ≠ j) :
    (∫ x : Model.Vector N, (x i)^2 * (x j)^2 ∂Model.spherePrior N) =
      (∫ x : Model.Vector N, (x i)^4 ∂Model.spherePrior N) / 3 := by
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  have he (q : Fin N) : ‖e q‖ = 1 := e.orthonormal.norm_eq_one q
  have hij' : inner ℝ (e i) (e j) = 0 := e.orthonormal.inner_eq_zero hij
  have hnplus : ‖e i + e j‖ = ‖Real.sqrt 2 • e i‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_add_sq_real, he i, he j, hij', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), he i, mul_one,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hnminus : ‖e i - e j‖ = ‖Real.sqrt 2 • e i‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, he i, he j, hij', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), he i, mul_one,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hp := projection_moment_eq_of_norm_eq 4 (e i + e j) (Real.sqrt 2 • e i) hnplus
  have hm := projection_moment_eq_of_norm_eq 4 (e i - e j) (Real.sqrt 2 • e i) hnminus
  have hs : (Real.sqrt 2)^4 = (4 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
    EuclideanSpace.basisFun_inner, e, mul_pow, hs, integral_const_mul] at hp hm
  have hall (F : Model.Vector N → ℝ) (hF : Continuous F) :
      Integrable F (Model.spherePrior N) := spherePrior_continuous_integrable hN F hF
  have hpoly : (∫ x : Model.Vector N, (x i+x j)^4 + (x i-x j)^4 ∂Model.spherePrior N) =
      ∫ x : Model.Vector N, 2*(x i)^4 + 12*((x i)^2*(x j)^2) + 2*(x j)^4
        ∂Model.spherePrior N := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [integral_add (hall _ (by fun_prop)) (hall _ (by fun_prop)),
    integral_add (hall _ (by fun_prop)) (hall _ (by fun_prop)),
    integral_add (hall _ (by fun_prop)) (hall _ (by fun_prop))] at hpoly
  simp only [integral_const_mul] at hpoly
  rw [coordinate_moment_eq 4 j i] at hpoly
  linarith

/-- Exact spherical fourth moment, including one-dimensional spheres. -/
theorem coordinate_fourth_moment {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (∫ x : Model.Vector N, (x i)^4 ∂Model.spherePrior N) =
      3 / ((N : ℝ)*((N : ℝ)+2)) := by
  classical
  let A : ℝ := ∫ x : Model.Vector N, (x i)^4 ∂Model.spherePrior N
  have hpair (j l : Fin N) :
      (∫ x : Model.Vector N, (x j)^2*(x l)^2 ∂Model.spherePrior N) =
        A/3 + (if j=l then 2*A/3 else 0) := by
    by_cases hjl : j=l
    · subst l
      have he : (∫ x : Model.Vector N, (x j)^2*(x j)^2 ∂Model.spherePrior N) = A := by
        calc
          _ = ∫ x : Model.Vector N, (x j)^4 ∂Model.spherePrior N := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
          _ = A := coordinate_moment_eq 4 j i
      rw [he, ite_eq_left rfl]
      ring
    · rw [coordinate_mixed_fourth_moment hN j l hjl, coordinate_moment_eq 4 j i,
        ite_eq_right hjl]
      simp only [A, add_zero]
  have htrace : (∫ x : Model.Vector N, ∑ j : Fin N, ∑ l : Fin N,
      (x j)^2*(x l)^2 ∂Model.spherePrior N) = 1 := by
    calc
      _ = ∫ x : Model.Vector N, ‖x‖^4 ∂Model.spherePrior N := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← Finset.sum_mul_sum, ← pow_two, ← EuclideanSpace.real_norm_sq_eq]
        ring
      _ = ∫ _x : Model.Vector N, (1 : ℝ) ∂Model.spherePrior N :=
        integral_congr_ae ((spherePrior_norm_ae hN).mono
          (fun x hx ↦ by dsimp; rw [hx, one_pow]))
      _ = 1 := by simp
  have hs : (∫ x : Model.Vector N, ∑ j : Fin N, ∑ l : Fin N,
      (x j)^2*(x l)^2 ∂Model.spherePrior N) =
      ∑ j : Fin N, ∑ l : Fin N, ∫ x : Model.Vector N,
        (x j)^2*(x l)^2 ∂Model.spherePrior N := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      apply integral_finsetSum
      intro l _
      exact spherePrior_continuous_integrable hN _ (by fun_prop)
    · intro j _
      exact spherePrior_continuous_integrable hN _ (by fun_prop)
  have hsum : (N : ℝ)*((N : ℝ)*(A/3)+2*A/3)=1 := by
    rw [hs] at htrace
    simp only [hpair, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htrace
    nlinarith [htrace]
  have hden : (N : ℝ)*((N : ℝ)+2) ≠ 0 := by positivity
  apply (eq_div_iff hden).mpr
  change A * ((N : ℝ)*((N : ℝ)+2)) = 3
  nlinarith [hsum]

/-- Exact fourth moment for any deterministic unit direction. -/
theorem unit_projection_fourth_moment {N : ℕ} (hN : 0 < N)
    (u : Model.Vector N) (hu : ‖u‖ = 1) :
    (∫ x, (inner ℝ u x)^4 ∂Model.spherePrior N) =
      3 / ((N : ℝ)*((N : ℝ)+2)) := by
  let i : Fin N := ⟨0, hN⟩
  have h := projection_moment_eq_of_norm_eq 4 u ((EuclideanSpace.basisFun (Fin N) ℝ) i)
    (by rw [hu, (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal.norm_eq_one i])
  rw [h]
  simpa only [EuclideanSpace.basisFun_inner] using coordinate_fourth_moment hN i

/-- Every finite overlap power of a measurable unit estimator is integrable
under the actual planted experiment with independent auxiliary randomness. -/
theorem estimator_overlap_power_integrable {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (hN : 0 < N)
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) (lam : ℝ) (p : ℕ) :
    Integrable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|^p)
      ((Model.experimentLaw N k).prod ν) := by
  have hm : Measurable (fun z : (Model.Vector N × Model.Tensor N k) × A ↦
      |inner ℝ (est (Model.observation lam z.1) z.2) z.1.1|^p) := by
    apply Measurable.pow_const
    exact continuous_abs.measurable.comp (continuous_inner.measurable.comp
      ((hest.1.comp (((Model.measurable_observation N k lam).comp measurable_fst).prodMk
        measurable_snd)).prodMk (measurable_fst.comp measurable_fst)))
  have hs : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖=1 :=
    (Measure.quasiMeasurePreserving_fst).ae
      ((Measure.quasiMeasurePreserving_fst).ae (spherePrior_norm_ae hN))
  apply (MemLp.of_bound hm.aestronglyMeasurable 1 _ : MemLp _ 1 _).integrable le_rfl
  filter_upwards [hs] with z hz
  simp only [Real.norm_eq_abs, abs_pow, abs_abs]
  apply pow_le_one₀ (abs_nonneg _)
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [hest.2 _ _, hz, one_mul])

/-- At zero signal, arbitrary independent estimator randomization can be
integrated after the planted vector. The deterministic spherical moment is the
only input; all product integrability is proved from unit-vector bounds. -/
private theorem expectedOverlapPower_zero_of_spherical_moment
    {N k : ℕ} {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [IsProbabilityMeasure ν] (hN : 0 < N) (est : Model.Estimator N k A)
    (hest : Model.IsUnitEstimator est) (p : ℕ) (C : ℝ)
    (hmoment : ∀ u : Model.Vector N, ‖u‖ = 1 →
      (∫ x, |inner ℝ u x|^p ∂Model.spherePrior N) = C) :
    Model.expectedOverlapPower N k 0 est ν p = C := by
  have hb (u x : Model.Vector N) (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
      ‖|inner ℝ u x|^p‖ ≤ (1 : ℝ) := by
    simp only [Real.norm_eq_abs, abs_pow, abs_abs]
    apply pow_le_one₀ (abs_nonneg _)
    exact (abs_real_inner_le_norm u x).trans_eq (by rw [hu, hx, one_mul])
  have hs : ∀ᵐ z ∂Model.experimentLaw N k, ‖z.1‖ = 1 :=
    (Measure.quasiMeasurePreserving_fst).ae (spherePrior_norm_ae hN)
  have hi (a : A) : Integrable (fun z : Model.Vector N × Model.Tensor N k ↦
      |inner ℝ (est z.2 a) z.1|^p) (Model.experimentLaw N k) := by
    have hm : Measurable (fun z : Model.Vector N × Model.Tensor N k ↦
        |inner ℝ (est z.2 a) z.1|^p) := by
      apply Measurable.pow_const
      exact continuous_abs.measurable.comp (continuous_inner.measurable.comp
        ((hest.1.comp (measurable_snd.prodMk measurable_const)).prodMk measurable_fst))
    exact (MemLp.of_bound hm.aestronglyMeasurable 1
      (hs.mono (fun z hz ↦ hb _ _ (hest.2 _ _) hz)) : MemLp _ 1 _).integrable le_rfl
  have hglobal := estimator_overlap_power_integrable ν hN est hest 0 p
  simp only [Model.observation, zero_mul, zero_smul, zero_add] at hglobal
  simp only [Model.expectedOverlapPower, Model.observation, zero_mul, zero_smul, zero_add]
  rw [integral_prod_symm _ hglobal]
  calc
    _ = ∫ a, ∫ w, ∫ x, |inner ℝ (est w a) x|^p ∂Model.spherePrior N
        ∂Model.noiseLaw N k ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with a
      exact integral_prod_symm _ (hi a)
    _ = C := by simp_rw [hmoment _ (hest.2 _ _)]; simp

/-- Exact zero-signal second moment for every independent randomized unit
estimator. No MLE property or sign convention is needed. -/
theorem zeroSignal_estimator_second_moment {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (hN : 0 < N)
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k 0 est ν 2 = 1 / (N : ℝ) := by
  apply expectedOverlapPower_zero_of_spherical_moment ν hN est hest
  intro u hu
  simpa only [sq_abs] using unit_projection_second_moment hN u hu

/-- Exact zero-signal fourth moment, uniformly for arbitrary independent
randomized unit estimators, in the manuscript's actual experiment law. -/
theorem zeroSignal_estimator_fourth_moment {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (hN : 0 < N)
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est) :
    Model.expectedOverlapPower N k 0 est ν 4 = 3 / ((N : ℝ)*((N : ℝ)+2)) := by
  apply expectedOverlapPower_zero_of_spherical_moment ν hN est hest
  intro u hu
  simpa only [(show Even 4 by decide).pow_abs] using unit_projection_fourth_moment hN u hu

/-- The zero-signal kth moment is bounded by 1/N for every exponent at least
two, since the absolute overlap lies in [0,1]. -/
theorem zeroSignal_estimator_power_bound {N k : ℕ} {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (hN : 0 < N)
    (est : Model.Estimator N k A) (hest : Model.IsUnitEstimator est)
    (p : ℕ) (hp : 2 ≤ p) :
    Model.expectedOverlapPower N k 0 est ν p ≤ 1 / (N : ℝ) := by
  rw [← zeroSignal_estimator_second_moment ν hN est hest]
  unfold Model.expectedOverlapPower
  apply integral_mono_ae (estimator_overlap_power_integrable ν hN est hest 0 p)
    (estimator_overlap_power_integrable ν hN est hest 0 2)
  have hs : ∀ᵐ z ∂(Model.experimentLaw N k).prod ν, ‖z.1.1‖ = 1 :=
    (Measure.quasiMeasurePreserving_fst).ae
      ((Measure.quasiMeasurePreserving_fst).ae (spherePrior_norm_ae hN))
  filter_upwards [hs] with z hz
  apply pow_le_pow_of_le_one (abs_nonneg _) _ hp
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [hest.2 _ _, hz, one_mul])

/-- A finite ordered tensor product of possibly different vectors in each
slot. This auxiliary definition uses the same full ordered coordinates as feature. -/
noncomputable def productTensor {N k : ℕ} (v : Fin k → Model.Vector N) : Model.Tensor N k :=
  WithLp.toLp 2 (fun i ↦ ∏ j, v j (i j))

/-- Inner products of finite ordered tensor products factor slot by slot. -/
theorem productTensor_inner {N k : ℕ} (v w : Fin k → Model.Vector N) :
    inner ℝ (productTensor v) (productTensor w) = ∏ j, inner ℝ (v j) (w j) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ i : Fin k → Fin N, (∏ j, w j (i j))*(∏ j, v j (i j))) =
    ∏ j : Fin k, ∑ i : Fin N, w j i * v j i
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : Fin k) (i : Fin N) ↦ w j i * v j i)).symm

theorem rotatedTensor_orthonormal {N k : ℕ}
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) :
    Orthonormal ℝ (fun i : Fin k → Fin N ↦
      productTensor (fun r ↦ U ((EuclideanSpace.basisFun (Fin N) ℝ) (i r)))) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [productTensor_inner]
  simp only [U.inner_map_map, (EuclideanSpace.basisFun (Fin N) ℝ).inner_eq_ite]
  by_cases hij : i=j
  · subst j
    simp
  · rw [ite_eq_right hij]
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hij
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])

noncomputable def rotatedTensorBasis {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) :
    OrthonormalBasis (Fin k → Fin N) ℝ (Model.Tensor N k) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let B := basisOfOrthonormalOfCardEqFinrank (rotatedTensor_orthonormal (k := k) U)
    (by simp)
  exact B.toOrthonormalBasis (by simpa only [B,
    coe_basisOfOrthonormalOfCardEqFinrank] using rotatedTensor_orthonormal (k := k) U)

/-- The genuine orthogonal action on all ordered tensor coordinates induced by
an orthogonal transformation of the physical vectors. -/
noncomputable def tensorRotation {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) :
    Model.Tensor N k ≃ₗᵢ[ℝ] Model.Tensor N k :=
  (rotatedTensorBasis (k := k) hN U).repr.symm

/-- The induced full tensor isometry has the intended action on every genuine
rank-one feature tensor. -/
theorem tensorRotation_feature {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (x : Model.Vector N) :
    tensorRotation (k := k) hN U (Model.feature k x) = Model.feature k (U x) := by
  have hb (i : Fin k → Fin N) : rotatedTensorBasis (k := k) hN U i =
      productTensor (fun r ↦ U ((EuclideanSpace.basisFun (Fin N) ℝ) (i r))) := by
    simp [rotatedTensorBasis, Module.Basis.coe_toOrthonormalBasis,
      coe_basisOfOrthonormalOfCardEqFinrank]
  apply (rotatedTensorBasis (k := k) hN U).repr.injective
  change (rotatedTensorBasis (k := k) hN U).repr
    ((rotatedTensorBasis (k := k) hN U).repr.symm (Model.feature k x)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  rw [OrthonormalBasis.repr_apply_apply, hb]
  change (∏ r, x (i r)) =
    inner ℝ (productTensor (fun r ↦ U ((EuclideanSpace.basisFun (Fin N) ℝ) (i r))))
      (productTensor (fun _ : Fin k ↦ U x))
  rw [productTensor_inner]
  simp only [U.inner_map_map, EuclideanSpace.basisFun_inner]

/-- Simultaneous vector and tensor rotations preserve the actual score. -/
theorem score_tensorRotation {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (y : Model.Tensor N k) (x : Model.Vector N) :
    Model.score (tensorRotation hN U y) (U x) = Model.score y x := by
  change inner ℝ (Model.feature k (U x)) (tensorRotation hN U y) = _
  rw [← tensorRotation_feature hN U x]
  exact (tensorRotation (k := k) hN U).inner_map_map _ _

/-- The actual normalized maximum is unchanged by the induced tensor rotation. -/
theorem normalizedMaximum_tensorRotation {N k : ℕ} (hN : 0 < N)
    (U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N) (y : Model.Tensor N k) :
    Model.normalizedMaximum (tensorRotation (k := k) hN U y) = Model.normalizedMaximum y := by
  have he : Model.score (tensorRotation hN U y) '' Model.unitSphere N =
      Model.score y '' Model.unitSphere N := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨U.symm x, ?_, ?_⟩
      · change ‖U.symm x‖ = 1
        simpa using (show ‖x‖ = 1 from hx)
      · simpa only [U.apply_symm_apply] using (score_tensorRotation hN U y (U.symm x)).symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨U x, ?_, score_tensorRotation hN U y x⟩
      change ‖U x‖ = 1
      simpa using (show ‖x‖ = 1 from hx)
  simp only [Model.normalizedMaximum, he]

/-- Gaussian averaging of the planted maximum depends only on the unit length
of the planted direction. This is a finite-dimensional law fact, with no
asymptotic ground-state input. -/
theorem plantedMaximum_mean_eq_of_unit {N k : ℕ} (hN : 0 < N)
    (x v : Model.Vector N) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) (lam : ℝ) :
    (∫ w, Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k x+w)
      ∂Model.noiseLaw N k) =
      ∫ w, Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+w)
        ∂Model.noiseLaw N k := by
  let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (x-v))ᗮ.reflection
  have hu : U x = v := Submodule.reflection_sub (hx.trans hv.symm)
  let T := tensorRotation (k := k) hN U
  have hshift (w : Model.Tensor N k) :
      Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v + T w) =
        Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k x+w) := by
    rw [← hu, ← tensorRotation_feature hN U x, ← T.map_smul, ← T.map_add]
    exact normalizedMaximum_tensorRotation hN U _
  have hmap : (Model.noiseLaw N k).map T = Model.noiseLaw N k := stdGaussian_map T
  have hF : Continuous (fun w : Model.Tensor N k ↦
      Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+w)) :=
    (shiftedMaximum_lipschitz hN _).continuous
  have hi := integral_map (μ := Model.noiseLaw N k) T.continuous.measurable.aemeasurable
    hF.aestronglyMeasurable
  rw [hmap] at hi
  calc
    _ = ∫ w, Model.normalizedMaximum ((lam*Real.sqrt N) • Model.feature k v+T w)
        ∂Model.noiseLaw N k := by
      apply integral_congr_ae
      filter_upwards [] with w
      exact (hshift w).symm
    _ = _ := hi.symm

/-- Every physical overlap slice is nonempty in ambient dimension at least
two, including the endpoint overlaps ±1. -/
theorem sphereSlice_nonempty {N : ℕ} (hN : 2 ≤ N) (x : Model.Vector N)
    (hx : ‖x‖ = 1) (m : ℝ) (hm : |m| ≤ 1) :
    {v ∈ Model.unitSphere N | inner ℝ v x = m}.Nonempty := by
  let i : Fin N := ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hN⟩
  let j : Fin N := ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 2) hN⟩
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  let U : Model.Vector N ≃ₗᵢ[ℝ] Model.Vector N := (ℝ ∙ (x-e i))ᗮ.reflection
  have hu : U x = e i :=
    Submodule.reflection_sub (hx.trans (e.orthonormal.norm_eq_one i).symm)
  have hij : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  have heij : inner ℝ (e i) (e j) = 0 := e.orthonormal.inner_eq_zero hij
  have heji : inner ℝ (e j) (e i) = 0 := e.orthonormal.inner_eq_zero hij.symm
  have hm2 : m^2 ≤ 1 := (sq_le_one_iff_abs_le_one m).mpr hm
  let v : Model.Vector N := m • e i + Real.sqrt (1-m^2) • e j
  refine ⟨U.symm v, ?_, ?_⟩
  · change ‖U.symm v‖ = 1
    rw [U.symm.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    dsimp [v]
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, e.orthonormal.norm_eq_one, mul_one,
      sq_abs, real_inner_smul_left, inner_smul_right, heij, mul_zero,
      add_zero, Real.sq_sqrt (sub_nonneg.mpr hm2), one_pow]
    ring
  · rw [← U.inner_map_map, U.apply_symm_apply, hu]
    dsimp [v]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      heji, mul_zero, add_zero]
    have hei : inner ℝ (e i) (e i) = 1 := e.inner_eq_one i
    rw [hei, mul_one]

/-- An overlap slice is a closed subset of the compact physical sphere. -/
theorem sphereSlice_isCompact {N : ℕ} (x : Model.Vector N) (m : ℝ) :
    IsCompact {v ∈ Model.unitSphere N | inner ℝ v x = m} :=
  (unitSphere_isCompact N).inter_right (isClosed_eq (by fun_prop) continuous_const)

/-- Every nonempty physical slice has a genuine attained constrained maximum. -/
theorem exists_constrainedMaximizer {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    (x : Model.Vector N) (hx : ‖x‖ = 1) (w : Model.Tensor N k) (m : ℝ) (hm : |m| ≤ 1) :
    ∃ v ∈ {v ∈ Model.unitSphere N | inner ℝ v x = m},
      Model.constrainedMaximum lam x w m = lam*m^k + Model.score w v / Real.sqrt N := by
  have hc : Continuous (fun v : Model.Vector N ↦ lam*m^k + Model.score w v / Real.sqrt N) :=
    continuous_const.add (((Model.continuous_feature N k).inner continuous_const).div_const _)
  obtain ⟨v, hv, hle⟩ := (sphereSlice_isCompact x m).exists_isMaxOn
    (sphereSlice_nonempty hN x hx m hm) hc.continuousOn
  refine ⟨v, hv, ?_⟩
  apply IsGreatest.csSup_eq
  refine ⟨⟨v, hv, rfl⟩, ?_⟩
  rintro a ⟨u, hu, rfl⟩
  exact hle hu

/-- Restricting the actual planted objective to a physical overlap slice can
only decrease the genuine unconstrained maximum. -/
theorem constrainedMaximum_le_normalizedMaximum {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (x : Model.Vector N) (hx : ‖x‖ = 1) (w : Model.Tensor N k)
    (m : ℝ) (hm : |m| ≤ 1) :
    Model.constrainedMaximum lam x w m ≤
      Model.normalizedMaximum (Model.observation lam (x, w)) := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  obtain ⟨v, hv, hmax⟩ := exists_constrainedMaximizer hN lam x hx w m hm
  rw [hmax]
  have hscore : Model.score (Model.observation lam (x, w)) v / Real.sqrt N =
      lam*m^k + Model.score w v / Real.sqrt N := by
    change inner ℝ (Model.feature k v)
      ((lam*Real.sqrt N) • Model.feature k x+w) / Real.sqrt N =
      lam*m^k + inner ℝ (Model.feature k v) w / Real.sqrt N
    rw [inner_add_right, inner_smul_right, feature_inner, hv.2]
    field_simp [hs.ne']
  rw [← hscore]
  exact div_le_div_of_nonneg_right (le_csSup (score_image_bddAbove _)
    ⟨v, hv.1, rfl⟩) hs.le

/-- Fixed physical-slice maxima have the same 1/sqrt(N) Gaussian Lipschitz
constant as the unconstrained maximum. -/
theorem constrainedMaximum_lipschitz {N k : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (x : Model.Vector N) (hx : ‖x‖ = 1) (m : ℝ) (hm : |m| ≤ 1) :
    LipschitzWith ((Real.sqrt N)⁻¹).toNNReal
      (fun w : Model.Tensor N k ↦ Model.constrainedMaximum lam x w m) := by
  apply LipschitzWith.of_le_add_mul' ((Real.sqrt N)⁻¹)
  intro y z
  obtain ⟨v, hv, hmax⟩ := exists_constrainedMaximizer hN lam x hx y m hm
  have hc : Continuous (fun v : Model.Vector N ↦ lam*m^k + Model.score z v/Real.sqrt N) :=
    continuous_const.add (((Model.continuous_feature N k).inner continuous_const).div_const _)
  have hb := (sphereSlice_isCompact x m).bddAbove_image hc.continuousOn
  have hsup : lam*m^k + Model.score z v/Real.sqrt N ≤ Model.constrainedMaximum lam x z m :=
    le_csSup hb ⟨v, hv, rfl⟩
  have hclose : Model.score y v ≤ Model.score z v+‖y-z‖ :=
    sub_le_iff_le_add'.mp ((le_abs_self _).trans (score_sub_le v hv.1 y z))
  rw [hmax]
  calc
    _ ≤ lam*m^k+(Model.score z v+‖y-z‖)/Real.sqrt N :=
      add_le_add_right (div_le_div_of_nonneg_right hclose (Real.sqrt_nonneg _)) _
    _ = (lam*m^k+Model.score z v/Real.sqrt N) + ‖y-z‖/Real.sqrt N := by ring
    _ ≤ Model.constrainedMaximum lam x z m+‖y-z‖/Real.sqrt N := by linarith
    _ = _ := by rw [dist_eq_norm]; ring

/-- Every finite Gaussian moment of a fixed constrained maximum exists. -/
theorem constrainedMaximum_memLp {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    (x : Model.Vector N) (hx : ‖x‖ = 1) (m : ℝ) (hm : |m| ≤ 1)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun w : Model.Tensor N k ↦ Model.constrainedMaximum lam x w m) p
      (Model.noiseLaw N k) := by
  let F : Model.Tensor N k → ℝ := fun w ↦ Model.constrainedMaximum lam x w m
  let G : Model.Tensor N k → ℝ := fun w ↦ F w-F 0
  have hLip := constrainedMaximum_lipschitz (k := k) hN lam x hx m hm
  have hG : LipschitzWith ((Real.sqrt N)⁻¹).toNNReal G := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [G, dist_sub_right] using hLip.dist_le_mul y z
  have hG0 : G 0 = 0 := sub_self _
  have H := hG.comp_memLp hG0 (IsGaussian.memLp_id (stdGaussian (Model.Tensor N k)) p hp)
  have H2 : MemLp (fun w : Model.Tensor N k ↦ (F w-F 0)+F 0) p
      (stdGaussian (Model.Tensor N k)) := H.add (memLp_const (F 0))
  simpa only [sub_add_cancel, F, Model.noiseLaw] using H2

/-- Exact Gaussian concentration of the genuine fixed-direction constrained
maximum, centered at its actual Gaussian expectation. -/
theorem constrainedMaximum_gaussian_tail {N k : ℕ} (hN : 2 ≤ N) (lam : ℝ)
    (x : Model.Vector N) (hx : ‖x‖ = 1) (m : ℝ) (hm : |m| ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    Model.noiseLaw N k {w | |Model.constrainedMaximum lam x w m -
      ∫ v, Model.constrainedMaximum lam x v m ∂Model.noiseLaw N k| > t} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ) * t^2 / 2)) := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  have hb := GaussianConcentrationBridge.stdGaussian_lipschitz_tail
    (fun w : Model.Tensor N k ↦ Model.constrainedMaximum lam x w m)
    ((Real.sqrt N)⁻¹) t (inv_pos.mpr hs) ht (constrainedMaximum_lipschitz hN lam x hx m hm)
  have he : -t^2 / (2 * ((Real.sqrt N)⁻¹)^2) = -(N : ℝ)*t^2/2 := by
    field_simp [hs.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  simpa only [Model.noiseLaw, he] using hb

end TensorPCA.Geometry
