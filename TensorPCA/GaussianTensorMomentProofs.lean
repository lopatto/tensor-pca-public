-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianCoordinateProjectionProofs
public import TensorPCA.SphericalGaussianTransferProofs

/-!
# Uniform Gaussian tensor-coordinate moments

Repeated index tuples need moments up to order 2k. Each coordinate has
the canonical real Gaussian law. A maximum-coordinate product bound gives a
dimension-independent integrable majorant, including all repeated tuples.
-/
@[expose] public section

namespace TensorPCA.GaussianTensorMomentProofs

open MeasureTheory ProbabilityTheory GaussianCoordinateProjectionProofs SphericalGaussianTransferProofs
open scoped ENNReal RealInnerProductSpace Classical

noncomputable def coordinateLine {N : ℕ} (i : Fin N) : ℝ →ₗᵢ[ℝ] Model.Vector N where
  toFun r := r • EuclideanSpace.single i 1
  map_add' r t := add_smul r t _
  map_smul' r t := mul_smul r t _
  norm_map' r := by simp [norm_smul]

theorem coordinateLine_adjoint {N : ℕ} (i : Fin N) (g : Model.Vector N) :
    (coordinateLine i).toContinuousLinearMap.adjoint g = g i := by
  calc
    _ = inner ℝ (1 : ℝ) ((coordinateLine i).toContinuousLinearMap.adjoint g) := by
      rw [Real.inner_apply, one_mul]
    _ = inner ℝ (coordinateLine i 1) g := (coordinateLine i).toContinuousLinearMap.adjoint_inner_right _ _
    _ = _ := by simp [coordinateLine, EuclideanSpace.inner_single_left]

theorem gaussian_coordinate_law {N : ℕ} (i : Fin N) :
    (stdGaussian (Model.Vector N)).map (fun g ↦ g i) = stdGaussian ℝ := by
  have h := stdGaussian_map_adjoint (coordinateLine i)
  have heq : (fun g : Model.Vector N ↦ g i) = (coordinateLine i).toContinuousLinearMap.adjoint := by
    funext g
    exact (coordinateLine_adjoint i g).symm
  rw [heq]
  exact h

theorem integrable_scalar_even_power (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ (2*k)) (stdGaussian ℝ) := by
  by_cases hk : k = 0
  · subst k
    simp
  · have h := (IsGaussian.memLp_id (stdGaussian ℝ) ((2*k : ℕ) : ℝ≥0∞)
      (ENNReal.natCast_ne_top (2*k))).integrable_norm_pow
      (by omega : 2*k ≠ 0)
    simpa only [id_eq, Real.norm_eq_abs, pow_abs_two_mul] using h

theorem integral_scalar_even_power (k : ℕ) :
    (∫ x : ℝ, x ^ (2*k) ∂stdGaussian ℝ) = GaussianMomentProofs.radialMomentProduct 1 k := by
  simpa only [Real.norm_eq_abs, pow_abs_two_mul, Module.finrank_self] using
    GaussianMomentProofs.gaussian_radius_even_moment (E := ℝ) k

theorem integrable_gaussian_coordinate_even_power {N : ℕ} (i : Fin N) (k : ℕ) :
    Integrable (fun g : Model.Vector N ↦ g i ^ (2*k)) (stdGaussian (Model.Vector N)) := by
  have h := integrable_scalar_even_power k
  rw [← gaussian_coordinate_law i] at h
  exact (integrable_map_measure (measurable_id.pow_const (2*k)).aestronglyMeasurable
    (PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable.aemeasurable).mp h

theorem integral_gaussian_coordinate_even_power {N : ℕ} (i : Fin N) (k : ℕ) :
    (∫ g : Model.Vector N, g i ^ (2*k) ∂stdGaussian (Model.Vector N)) =
      GaussianMomentProofs.radialMomentProduct 1 k := by
  have h := integral_map (μ := stdGaussian (Model.Vector N))
    (PiLp.continuous_apply 2 (fun _ : Fin N ↦ ℝ) i).measurable.aemeasurable
    (measurable_id.pow_const (2*k)).aestronglyMeasurable
  rw [gaussian_coordinate_law i] at h
  exact h.symm.trans (integral_scalar_even_power k)

theorem prod_le_sum_pow_card {alpha : Type*} [Fintype alpha] [Nonempty alpha]
    (f : alpha → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (∏ a, f a) ≤ ∑ a, f a ^ Fintype.card alpha := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  calc
    _ ≤ ∏ _b : alpha, f a := Finset.prod_le_prod₀ (fun b _ ↦ hf b) ha
    _ = f a ^ Fintype.card alpha := by simp
    _ ≤ _ := Finset.single_le_sum (fun b _ ↦ pow_nonneg (hf b) _) (Finset.mem_univ a)

theorem tensor_coordinate_sq_le {N k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) (g : Model.Vector N) :
    (Model.feature k g i) ^ 2 ≤ ∑ j : Fin k, g (i j) ^ (2*k) := by
  have : NeZero k := ⟨hk.ne'⟩
  have h := prod_le_sum_pow_card (fun j : Fin k ↦ g (i j) ^ 2) (fun _ ↦ sq_nonneg _)
  simpa only [Model.feature, PiLp.toLp_apply, ← Finset.prod_pow, Fintype.card_fin, ← pow_mul] using h

theorem integrable_tensor_coordinate_sq {N k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) :
    Integrable (fun g : Model.Vector N ↦ (Model.feature k g i) ^ 2) (stdGaussian (Model.Vector N)) := by
  have hsum := integrable_finsetSum Finset.univ (fun j _ ↦ integrable_gaussian_coordinate_even_power (i j) k)
  have hmeas : Measurable (fun g : Model.Vector N ↦ (Model.feature k g i) ^ 2) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin k → Fin N ↦ ℝ) i).comp (Model.continuous_feature N k)).measurable.pow_const 2
  apply hsum.mono' hmeas.aestronglyMeasurable
  exact .of_forall fun g ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact tensor_coordinate_sq_le hk i g

theorem integral_tensor_coordinate_sq_le {N k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) :
    (∫ g : Model.Vector N, (Model.feature k g i) ^ 2 ∂stdGaussian (Model.Vector N)) ≤
      (k : ℝ) * GaussianMomentProofs.radialMomentProduct 1 k := by
  apply (integral_mono_ae (integrable_tensor_coordinate_sq hk i)
    (integrable_finsetSum Finset.univ (fun j _ ↦ integrable_gaussian_coordinate_even_power (i j) k))
    (.of_forall fun g ↦ tensor_coordinate_sq_le hk i g)).trans_eq
  rw [integral_finsetSum Finset.univ (fun j _ ↦ integrable_gaussian_coordinate_even_power (i j) k)]
  simp only [integral_gaussian_coordinate_even_power, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem gaussianFeature_coordinate_sq (N k : ℕ) (i : Fin k → Fin N) (g : Model.Vector N) :
    gaussianFeature N k g i ^ 2 = (Model.feature k g i) ^ 2 / (N : ℝ) ^ k := by
  rw [gaussianFeature, Geometry.feature_smul]
  change (((Real.sqrt N)⁻¹ ^ k) * Model.feature k g i) ^ 2 = _
  have hc : ((Real.sqrt N)⁻¹ ^ k) ^ 2 = ((N : ℝ) ^ k)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N), inv_pow]
  rw [mul_pow, hc, div_eq_mul_inv, mul_comm]

theorem integrable_gaussianFeature_coordinate_sq {N k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) :
    Integrable (fun g : Model.Vector N ↦ gaussianFeature N k g i ^ 2) (stdGaussian (Model.Vector N)) := by
  simp_rw [gaussianFeature_coordinate_sq]
  exact (integrable_tensor_coordinate_sq hk i).div_const _

theorem integral_gaussianFeature_coordinate_sq_le {N k : ℕ} (hk : 0 < k) (i : Fin k → Fin N) :
    (∫ g : Model.Vector N, gaussianFeature N k g i ^ 2 ∂stdGaussian (Model.Vector N)) ≤
      (k : ℝ) * GaussianMomentProofs.radialMomentProduct 1 k / (N : ℝ) ^ k := by
  simp_rw [gaussianFeature_coordinate_sq]
  rw [integral_div]
  exact div_le_div_of_nonneg_right (integral_tensor_coordinate_sq_le hk i)
    (pow_nonneg (Nat.cast_nonneg N) k)

theorem integral_gaussianFeature_coordinate_sum_le {N k : ℕ} (hk : 0 < k)
    (J : Finset (Fin k → Fin N)) :
    (∫ g : Model.Vector N, ∑ i ∈ J, gaussianFeature N k g i ^ 2 ∂stdGaussian (Model.Vector N)) ≤
      (J.card : ℝ) * ((k : ℝ) * GaussianMomentProofs.radialMomentProduct 1 k / (N : ℝ) ^ k) := by
  rw [integral_finsetSum J (fun i _ ↦ integrable_gaussianFeature_coordinate_sq hk i)]
  apply (Finset.sum_le_sum (fun i _ ↦ integral_gaussianFeature_coordinate_sq_le hk i)).trans_eq
  simp only [Finset.sum_const, nsmul_eq_mul]


end TensorPCA.GaussianTensorMomentProofs
