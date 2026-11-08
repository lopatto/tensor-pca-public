-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.CoupledGaussianKernelProofs

/-! Ordinary expectation identities for the finite coordinate covariance.
The probability law may be a Gibbs law; its bounded measurable field supplies
every required product integrability statement. -/
@[expose] public section
namespace TensorPCA.CoupledKernelExpectationProofs
open Set Filter MeasureTheory ProbabilityTheory CoupledGaussianKernelProofs
open scoped Topology RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem clm_coordinate_abs_le (A : EuclideanSpace ℝ ι →L[ℝ] ℝ) (i : ι) :
    |A (EuclideanSpace.single i 1)| ≤ ‖A‖ := by
  simpa only [Real.norm_eq_abs,PiLp.norm_single,Real.norm_eq_abs,
    abs_one,mul_one] using A.le_opNorm (EuclideanSpace.single i 1)

theorem clm_coordinate_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) (i : ι) :
    Integrable (fun v => A v (EuclideanSpace.single i 1)) μ := by
  apply (integrable_const K).mono'
    (((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hA).aestronglyMeasurable)
  filter_upwards [hb] with v hv
  exact (clm_coordinate_abs_le (A v) i).trans hv

theorem clm_coordinate_square_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) (i : ι) :
    Integrable (fun v => (A v (EuclideanSpace.single i 1))^2) μ := by
  have hm : Measurable (fun v => (A v (EuclideanSpace.single i 1))^2) :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.measurable.comp hA).pow_const 2
  apply (integrable_const (K^2)).mono' hm.aestronglyMeasurable
  filter_upwards [hb] with v hv
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have H := (sq_le_sq₀ (abs_nonneg (A v (EuclideanSpace.single i 1))) hK).mpr
    ((clm_coordinate_abs_le (A v) i).trans hv)
  simpa only [sq_abs] using H

theorem coordinateCovariance_diagonal_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) :
    Integrable (fun v => coordinateCovariance (A v) (A v)) μ := by
  simp_rw [coordinateCovariance,← pow_two]
  exact integrable_finsetSum _ (fun i _ => clm_coordinate_square_integrable μ A hA hK hb i)

theorem sum_integral_coordinate_square (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) :
    (∑ i, ∫ v, (A v (EuclideanSpace.single i 1))^2 ∂μ) =
      ∫ v, coordinateCovariance (A v) (A v) ∂μ := by
  simp_rw [coordinateCovariance,← pow_two]
  exact (integral_finsetSum _ (fun i _ => clm_coordinate_square_integrable μ A hA hK hb i)).symm

theorem coordinateCovariance_product_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) :
    Integrable (fun vu : V × V => coordinateCovariance (A vu.1) (A vu.2)) (μ.prod μ) := by
  unfold coordinateCovariance
  exact integrable_finsetSum _ (fun i _ =>
    (clm_coordinate_integrable μ A hA hb i).mul_prod (clm_coordinate_integrable μ A hA hb i))

theorem sum_square_integral_coordinate (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hA : Measurable A)
    {K : ℝ} (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ K) :
    (∑ i, (∫ v, A v (EuclideanSpace.single i 1) ∂μ)^2) =
      ∫ vu : V × V, coordinateCovariance (A vu.1) (A vu.2) ∂μ.prod μ := by
  unfold coordinateCovariance
  rw [integral_finsetSum _ (fun i _ =>
    (clm_coordinate_integrable μ A hA hb i).mul_prod (clm_coordinate_integrable μ A hA hb i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod_mul (fun v => A v (EuclideanSpace.single i 1))
    (fun v => A v (EuclideanSpace.single i 1))]
  ring

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem covariance_difference_diagonal_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hL : Measurable L) (hA : Measurable A) {KL KA : ℝ} (hKL : 0 ≤ KL) (hKA : 0 ≤ KA)
    (hbL : ∀ᵐ v ∂μ, ‖L v‖ ≤ KL) (hbA : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA) :
    Integrable (fun v => coordinateCovariance (L v) (L v)-coordinateCovariance (A v) (A v)) μ :=
  (coordinateCovariance_diagonal_integrable μ L hL hKL hbL).sub
    (coordinateCovariance_diagonal_integrable μ A hA hKA hbA)

theorem covariance_difference_product_integrable (μ : Measure V) [IsProbabilityMeasure μ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hL : Measurable L) (hA : Measurable A) {KL KA : ℝ}
    (hbL : ∀ᵐ v ∂μ, ‖L v‖ ≤ KL) (hbA : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA) :
    Integrable (fun vu : V × V => coordinateCovariance (L vu.1) (L vu.2)-
      coordinateCovariance (A vu.1) (A vu.2)) (μ.prod μ) :=
  (coordinateCovariance_product_integrable μ L hL hbL).sub
    (coordinateCovariance_product_integrable μ A hA hbA)

theorem sum_integral_coordinate_square_difference (μ : Measure V) [IsProbabilityMeasure μ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hL : Measurable L) (hA : Measurable A) {KL KA : ℝ} (hKL : 0 ≤ KL) (hKA : 0 ≤ KA)
    (hbL : ∀ᵐ v ∂μ, ‖L v‖ ≤ KL) (hbA : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA) :
    (∑ i, ∫ v, (L v (EuclideanSpace.single i 1))^2 ∂μ)-
      (∑ j, ∫ v, (A v (EuclideanSpace.single j 1))^2 ∂μ) =
      ∫ v, coordinateCovariance (L v) (L v)-coordinateCovariance (A v) (A v) ∂μ := by
  rw [sum_integral_coordinate_square μ L hL hKL hbL,
    sum_integral_coordinate_square μ A hA hKA hbA]
  exact (integral_sub (coordinateCovariance_diagonal_integrable μ L hL hKL hbL)
    (coordinateCovariance_diagonal_integrable μ A hA hKA hbA)).symm

theorem sum_square_integral_coordinate_difference (μ : Measure V) [IsProbabilityMeasure μ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hL : Measurable L) (hA : Measurable A) {KL KA : ℝ}
    (hbL : ∀ᵐ v ∂μ, ‖L v‖ ≤ KL) (hbA : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA) :
    (∑ i, (∫ v, L v (EuclideanSpace.single i 1) ∂μ)^2)-
      (∑ j, (∫ v, A v (EuclideanSpace.single j 1) ∂μ)^2) =
      ∫ vu : V × V, coordinateCovariance (L vu.1) (L vu.2)-
        coordinateCovariance (A vu.1) (A vu.2) ∂μ.prod μ := by
  rw [sum_square_integral_coordinate μ L hL hbL,
    sum_square_integral_coordinate μ A hA hbA]
  exact (integral_sub (coordinateCovariance_product_integrable μ L hL hbL)
    (coordinateCovariance_product_integrable μ A hA hbA)).symm


end
end TensorPCA.CoupledKernelExpectationProofs
