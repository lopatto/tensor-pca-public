-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianAngularExpectationProofs

/-! Outer physical Gaussian differentiation of the angular nested pressure. -/
@[expose] public section
namespace TensorPCA.GaussianAngularOuterProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianPowerMomentBounds
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open GaussianAngularPressureProofs GaussianAngularExpectationProofs
open Filter
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem shiftedSpinMoment_scaled (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (a b : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    shiftedSpinMoment ν ρ (scaledLinear A a) (scaledLinear L b) w g =
      shiftedSpinMoment ν ρ A L (a • w) (b • g) := by
  simp only [shiftedSpinMoment, GaussianSpinInterpolation.moment, weight, scaledLinear,
    smul_apply, map_smul, smul_eq_mul]

theorem angularPower_eq_scaled_nested (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta w g = nestedIntegrand ν (fun _ ↦ 1)
      (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta)) p w g := by
  have hc := scaledLinear_bound_one ν A (hb.mono (fun _ hv ↦ hv.1)) _ (Real.abs_cos_le_one theta)
  have hs := scaledLinear_bound_one ν L (hb.mono (fun _ hv ↦ hv.2)) _ (Real.abs_sin_le_one theta)
  rw [nestedIntegrand_one_exp ν _ _ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    (hc.and hs), shiftedSpinMoment_scaled]
  unfold angularPower powerWeight logPartition
  rw [angularMoment_eq_shift]

theorem angularNormalizer_eq_scaled_nested (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularNormalizer ν A L p theta w = nestedNumerator ν (fun _ ↦ 1)
      (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta)) p w := by
  unfold angularNormalizer nestedNumerator
  apply integral_congr_ae
  exact Eventually.of_forall (angularPower_eq_scaled_nested ν A L hA hL hb p theta w)

theorem angularNormalizer_continuous_physical (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Continuous (angularNormalizer ν A L p theta) := by
  have hc := scaledLinear_bound_one ν A (hb.mono (fun _ hv ↦ hv.1)) _ (Real.abs_cos_le_one theta)
  have hs := scaledLinear_bound_one ν L (hb.mono (fun _ hv ↦ hv.2)) _ (Real.abs_sin_le_one theta)
  have heq : angularNormalizer ν A L p theta = nestedNumerator ν (fun _ ↦ 1)
      (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta)) p :=
    funext (angularNormalizer_eq_scaled_nested ν A L hA hL hb p theta)
  rw [heq]
  exact (nestedNumerator_contDiff ν (fun _ ↦ 1) _ _ measurable_const
    (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _) zero_le_one hKA hKL
      ((hc.and hs).mono (fun _ hv ↦ ⟨by norm_num,hv⟩)) p).continuous

theorem angularLogPressure_continuous_physical (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Continuous (angularLogPressure ν A L p theta) := by
  exact ((angularNormalizer_continuous_physical ν A L hA hL hKA hKL hb p theta).log
    (fun w ↦ (angularNormalizer_pos ν A L hA hL hKA hKL hb p theta w).ne')).div_const p

theorem powerWeight_zero (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (p : ℝ) : powerWeight ν A p 0 = 1 := by
  simp [powerWeight, logPartition, GaussianSpinInterpolation.moment, weight]

theorem angularPower_common_factor (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta w g = powerWeight ν L p (Real.sin theta • g)*
      powerWeight (gibbsMeasure ν L (Real.sin theta • g)) A p (Real.cos theta • w) := by
  rw [angularPower_eq_nested ν A L hA hL hb, nestedIntegrand_one_eq ν A L hA hL hb]

theorem angularPower_zero_physical (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta 0 g = powerWeight ν L p (Real.sin theta • g) := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2)) (Real.sin theta • g)
  rw [angularPower_common_factor ν A L hA hL hb]
  simp only [smul_zero, powerWeight_zero, mul_one]

theorem angularPower_compare_zero (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    Real.exp (-((|p| *KA)*‖w‖))*angularPower ν A L p theta 0 g ≤ angularPower ν A L p theta w g ∧
      angularPower ν A L p theta w g ≤ Real.exp ((|p| *KA)*‖w‖)*angularPower ν A L p theta 0 g := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2)) (Real.sin theta • g)
  have hAg := (gibbsMeasure_absolutelyContinuous ν L (Real.sin theta • g)).ae_le
    (hb.mono (fun _ hv ↦ hv.1))
  have hc : ‖Real.cos theta • w‖ ≤ ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one theta) (norm_nonneg _)).trans_eq (one_mul _)
  have hcoef := mul_nonneg (abs_nonneg p) hKA
  have hlo : Real.exp (-((|p| *KA)*‖w‖)) ≤
      powerWeight (gibbsMeasure ν L (Real.sin theta • g)) A p (Real.cos theta • w) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hc hcoef))).trans
    simpa only [neg_mul] using powerWeight_ge_exp_neg_norm
      (gibbsMeasure ν L (Real.sin theta • g)) A hA hAg p (Real.cos theta • w)
  have hhi := (powerWeight_le_exp_norm (gibbsMeasure ν L (Real.sin theta • g)) A hA hAg p
    (Real.cos theta • w)).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc hcoef))
  rw [angularPower_common_factor ν A L hA hL hb p theta w g,
    angularPower_zero_physical ν A L hA hL hb p theta g]
  constructor
  · calc
      _ = powerWeight ν L p (Real.sin theta • g)*Real.exp (-((|p| *KA)*‖w‖)) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (powerWeight_pos ν L p _).le
  · exact (mul_le_mul_of_nonneg_left hhi (powerWeight_pos ν L p _).le).trans_eq (mul_comm _ _)

theorem angularNormalizer_compare_zero (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Real.exp (-((|p| *KA)*‖w‖))*angularNormalizer ν A L p theta 0 ≤ angularNormalizer ν A L p theta w ∧
      angularNormalizer ν A L p theta w ≤ Real.exp ((|p| *KA)*‖w‖)*angularNormalizer ν A L p theta 0 := by
  have hi := angularPower_integrable ν A L hA hL hKA hKL hb p theta w
  have hi0 := angularPower_integrable ν A L hA hL hKA hKL hb p theta 0
  constructor
  · have H := integral_mono_ae (hi0.const_mul _) hi (Eventually.of_forall (fun g ↦
      (angularPower_compare_zero ν A L hA hL hKA hb p theta w g).1))
    rw [integral_const_mul] at H
    exact H
  · have H := integral_mono_ae hi (hi0.const_mul _) (Eventually.of_forall (fun g ↦
      (angularPower_compare_zero ν A L hA hL hKA hb p theta w g).2))
    rw [integral_const_mul] at H
    exact H

theorem angularLogPressure_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (hp : p ≠ 0) (theta : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖angularLogPressure ν A L p theta w‖ ≤ ‖angularLogPressure ν A L p theta 0‖+KA*‖w‖ := by
  have hz0 := angularNormalizer_pos ν A L hA hL hKA hKL hb p theta 0
  have hzw := angularNormalizer_pos ν A L hA hL hKA hKL hb p theta w
  have hcmp := angularNormalizer_compare_zero ν A L hA hL hKA hKL hb p theta w
  have hlo := Real.log_le_log (mul_pos (Real.exp_pos _) hz0) hcmp.1
  have hhi := Real.log_le_log hzw hcmp.2
  rw [Real.log_mul (Real.exp_pos _).ne' hz0.ne', Real.log_exp] at hlo hhi
  have ha : |Real.log (angularNormalizer ν A L p theta w)| ≤
      |Real.log (angularNormalizer ν A L p theta 0)|+(|p| *KA)*‖w‖ := abs_le.mpr ⟨by
    linarith [neg_abs_le (Real.log (angularNormalizer ν A L p theta 0))], by
    linarith [le_abs_self (Real.log (angularNormalizer ν A L p theta 0))]⟩
  change |Real.log (angularNormalizer ν A L p theta w)/p| ≤
    |Real.log (angularNormalizer ν A L p theta 0)/p|+KA*‖w‖
  rw [abs_div, abs_div]
  apply (div_le_div_of_nonneg_right ha (abs_nonneg p)).trans_eq
  have hpabs : |p| ≠ 0 := abs_ne_zero.mpr hp
  field_simp

theorem angularLogPressure_integrable_physical (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≠ 0) (theta : ℝ) :
    Integrable (angularLogPressure ν A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  apply ((integrable_const ‖angularLogPressure ν A L p theta 0‖).add
    ((gaussian_norm_integrable (ι := κ)).const_mul KA)).mono'
      (angularLogPressure_continuous_physical ν A L hA hL hKA hKL hb p theta).aestronglyMeasurable
  exact Eventually.of_forall (angularLogPressure_norm_le ν A L hA hL hKA hKL hb p hp theta)

theorem angularDerivative_measurable_physical (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Measurable (fun w ↦ angularNormalizerDerivative ν A L p theta w/
      (p*angularNormalizer ν A L p theta w)) := by
  let step := fun n : ℕ ↦ (1 : ℝ)/((n : ℝ)+1)
  have hzero : Tendsto step atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hgt : Tendsto step atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hzero, Eventually.of_forall (fun n ↦ by change 0 < (1 : ℝ)/((n : ℝ)+1); positivity)⟩
  apply measurable_of_tendsto_metrizable (f := fun n w ↦
    (angularLogPressure ν A L p (theta+step n) w-angularLogPressure ν A L p theta w)/step n)
  · intro n
    exact ((angularLogPressure_continuous_physical ν A L hA hL hKA hKL hb p _).measurable.sub
      (angularLogPressure_continuous_physical ν A L hA hL hKA hKL hb p theta).measurable).div_const _
  · apply tendsto_pi_nhds.mpr
    intro w
    simpa only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (angularLogPressure_hasDerivAt ν A L hA hL hKA hKL hb p theta w).tendsto_slope_zero_right.comp hgt

def averagedAngularPressure (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) : ℝ :=
  ∫ w, angularLogPressure ν A L p theta w ∂SYK.standardGaussianMeasureOnEuclidean κ

def averagedAngularDerivative (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) : ℝ :=
  ∫ w, angularNormalizerDerivative ν A L p theta w/(p*angularNormalizer ν A L p theta w)
    ∂SYK.standardGaussianMeasureOnEuclidean κ

/-- Theta differentiation through both Gaussian stages. The nested derivative is dominated uniformly in theta by an integrable affine
function of the physical Gaussian norm. -/
theorem averagedAngularPressure_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≠ 0) (theta : ℝ) :
    HasDerivAt (averagedAngularPressure ν A L p) (averagedAngularDerivative ν A L p theta) theta := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean κ) (s := Set.univ)
    (F := fun t w ↦ angularLogPressure ν A L p t w)
    (F' := fun t w ↦ angularNormalizerDerivative ν A L p t w/(p*angularNormalizer ν A L p t w))
    (bound := fun w ↦ KA*‖w‖+KL*gaussianTiltNormBound ι (|p| *KL)) (by simp)
    (Eventually.of_forall (fun t ↦
      (angularLogPressure_integrable_physical ν A L hA hL hKA hKL hb p hp t).aestronglyMeasurable))
    (angularLogPressure_integrable_physical ν A L hA hL hKA hKL hb p hp theta)
    (angularDerivative_measurable_physical ν A L hA hL hKA hKL hb p theta).aestronglyMeasurable
    (Eventually.of_forall (fun w t _ ↦ angularLogPressure_derivative_norm_le ν A L hA hL hKA hKL hb p hp t w))
    (((gaussian_norm_integrable (ι := κ)).const_mul KA).add (integrable_const _))
    (Eventually.of_forall (fun w t _ ↦ angularLogPressure_hasDerivAt ν A L hA hL hKA hKL hb p t w))).2

end
end TensorPCA.GaussianAngularOuterProofs
