-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianAngularPressureProofs
public import TensorPCA.GaussianPowerMomentBounds

/-! Angular common-disorder tilt and bounds for outer Gaussian differentiation. -/
@[expose] public section
namespace TensorPCA.GaussianAngularExpectationProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianPowerMomentBounds
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open GaussianAngularPressureProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem scaledLinear_bound_one (ν : Measure V)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) (ht : |t| ≤ 1) :
    ∀ᵐ v ∂ν, ‖scaledLinear L t v‖ ≤ K := by
  filter_upwards [hb] with v hv
  rw [scaledLinear, norm_smul, Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans_eq (one_mul _)).trans hv

theorem powerWeight_scaledLinear (ν : Measure V)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (t p : ℝ) (g : EuclideanSpace ℝ ι) :
    powerWeight ν (scaledLinear L t) p g = powerWeight ν L p (t • g) := by
  simp only [powerWeight, logPartition, GaussianSpinInterpolation.moment, weight, scaledLinear,
    smul_apply, map_smul, smul_eq_mul]

def angularTilt (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : Measure (EuclideanSpace ℝ ι) :=
  powerTilt (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p

theorem angularTilt_probability (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : IsProbabilityMeasure (angularTilt ν A L p theta w) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  exact powerTilt_probability (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta))
    (scaledLinear_measurable L hL _) hKL (scaledLinear_bound_one _ L hLg _ (Real.abs_sin_le_one _)) p

theorem angularTilt_norm_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (fun g ↦ ‖g‖) (angularTilt ν A L p theta w) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  exact powerTilt_norm_integrable (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta))
    (scaledLinear_measurable L hL _) hKL (scaledLinear_bound_one _ L hLg _ (Real.abs_sin_le_one _)) p

theorem angularTilt_norm_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    (∫ g, ‖g‖ ∂angularTilt ν A L p theta w) ≤ gaussianTiltNormBound ι (|p| *KL) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  exact powerTilt_norm_integral_le (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta))
    (scaledLinear_measurable L hL _) hKL (scaledLinear_bound_one _ L hLg _ (Real.abs_sin_le_one _)) p

theorem angularPower_factor_scaled (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta w g = powerWeight ν A p (Real.cos theta • w)*
      powerWeight (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p g := by
  rw [angularPower_factor ν A L hA hL hb, powerWeight_scaledLinear]

theorem angularNormalizer_factor (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularNormalizer ν A L p theta w = powerWeight ν A p (Real.cos theta • w)*
      ∫ g, powerWeight (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p g
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  unfold angularNormalizer
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (angularPower_factor_scaled ν A L hA hL hb p theta w)

theorem angularTilt_integral_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ g, f g ∂angularTilt ν A L p theta w) =
      (∫ g, angularPower ν A L p theta w g*f g ∂SYK.standardGaussianMeasureOnEuclidean ι) /
        angularNormalizer ν A L p theta w := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  have hLs := scaledLinear_bound_one _ L hLg _ (Real.abs_sin_le_one theta)
  have hz := powerWeight_integral_pos (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta))
    (scaledLinear_measurable L hL _) hKL hLs p
  have hc := powerWeight_pos ν A p (Real.cos theta • w)
  rw [angularTilt, powerTilt_integral_eq _ _ (scaledLinear_measurable L hL _) hKL hLs p]
  have hnum : (∫ g, angularPower ν A L p theta w g*f g ∂SYK.standardGaussianMeasureOnEuclidean ι) =
      powerWeight ν A p (Real.cos theta • w)*
        ∫ g, powerWeight (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p g*f g
          ∂SYK.standardGaussianMeasureOnEuclidean ι := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g ↦ by
      change angularPower ν A L p theta w g*f g = powerWeight ν A p (Real.cos theta • w)*
        (powerWeight (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p g*f g)
      rw [angularPower_factor_scaled ν A L hA hL hb]
      ring)
  rw [hnum, angularNormalizer_factor ν A L hA hL hb]
  field_simp

def angularResponse (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  -Real.sin theta*expectation (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L (Real.sin theta • g)+
    Real.cos theta*score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g

theorem angularResponse_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) : Continuous (angularResponse ν A L theta w) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  have hρ : Measurable (fun v ↦ A v w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hA
  have hρb : ∀ᵐ v ∂gibbsMeasure ν A (Real.cos theta • w), |A v w| ≤ KA*‖w‖ ∧ ‖L v‖ ≤ KL :=
    (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le (hb.mono (fun v hv ↦
      ⟨((A v).le_opNorm w).trans (mul_le_mul_of_nonneg_right hv.1 (norm_nonneg _)),hv.2⟩))
  have hE := (expectation_contDiff (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L hρ hL
    (mul_nonneg hKA (norm_nonneg _)) hKL hρb).continuous.comp (continuous_const_smul (Real.sin theta))
  have hS := ((score_continuous (gibbsMeasure ν A (Real.cos theta • w)) L hL hKL hLg).comp
    (continuous_const_smul (Real.sin theta))).clm_apply continuous_id
  exact (continuous_const.mul hE).add (continuous_const.mul hS)

theorem angularResponse_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖angularResponse ν A L theta w g‖ ≤ KA*‖w‖+KL*‖g‖ := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  have hρ : Measurable (fun v ↦ A v w) :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hA
  have hρb : ∀ᵐ v ∂gibbsMeasure ν A (Real.cos theta • w), |A v w| ≤ KA*‖w‖ ∧ ‖L v‖ ≤ KL :=
    (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le (hb.mono (fun v hv ↦
      ⟨((A v).le_opNorm w).trans (mul_le_mul_of_nonneg_right hv.1 (norm_nonneg _)),hv.2⟩))
  have hE := norm_expectation_le (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L hρ hL
    (mul_nonneg hKA (norm_nonneg _)) hρb (Real.sin theta • g)
  have hS : |score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g| ≤ KL*‖g‖ :=
    ((score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g)).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (norm_score_le _ L hL hKL hLg _) (norm_nonneg _))
  rw [angularResponse, Real.norm_eq_abs]
  calc
    _ ≤ |Real.sin theta| *|expectation (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L (Real.sin theta • g)|+
        |Real.cos theta| *|score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g| := by
      simpa only [abs_mul, abs_neg] using abs_add_le
        (-Real.sin theta*expectation (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L (Real.sin theta • g))
        (Real.cos theta*score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g)
    _ ≤ 1*(KA*‖w‖)+1*(KL*‖g‖) := add_le_add
      (mul_le_mul (Real.abs_sin_le_one theta) hE (abs_nonneg _) zero_le_one)
      (mul_le_mul (Real.abs_cos_le_one theta) hS (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem angularResponse_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (angularResponse ν A L theta w) (angularTilt ν A L p theta w) := by
  letI := angularTilt_probability ν A L hA hL hKL hb p theta w
  apply ((integrable_const (KA*‖w‖)).add
    ((angularTilt_norm_integrable ν A L hA hL hKL hb p theta w).const_mul KL)).mono'
      (angularResponse_continuous ν A L hA hL hKA hKL hb theta w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (angularResponse_norm_le ν A L hA hL hKA hKL hb theta w)

theorem angularResponse_integral_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖∫ g, angularResponse ν A L theta w g ∂angularTilt ν A L p theta w‖ ≤
      KA*‖w‖+KL*gaussianTiltNormBound ι (|p| *KL) := by
  letI := angularTilt_probability ν A L hA hL hKL hb p theta w
  have hi := angularResponse_integrable ν A L hA hL hKA hKL hb p theta w
  have hin := (angularTilt_norm_integrable ν A L hA hL hKL hb p theta w).const_mul KL
  calc
    _ ≤ ∫ g, ‖angularResponse ν A L theta w g‖ ∂angularTilt ν A L p theta w :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g, KA*‖w‖+KL*‖g‖ ∂angularTilt ν A L p theta w :=
      integral_mono_ae hi.norm ((integrable_const _).add hin)
        (Filter.Eventually.of_forall (angularResponse_norm_le ν A L hA hL hKA hKL hb theta w))
    _ = KA*‖w‖+KL*(∫ g, ‖g‖ ∂angularTilt ν A L p theta w) := by
      rw [integral_add (integrable_const _) hin, integral_const_mul KL (fun g ↦ ‖g‖)]
      simp only [integral_const, probReal_univ, one_smul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (angularTilt_norm_integral_le ν A L hA hL hKL hb p theta w) hKL)

theorem angularLogPressure_derivative_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (hp : p ≠ 0) (theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularNormalizerDerivative ν A L p theta w/(p*angularNormalizer ν A L p theta w) =
      ∫ g, angularResponse ν A L theta w g ∂angularTilt ν A L p theta w := by
  have hD : angularNormalizerDerivative ν A L p theta w = p*
      ∫ g, angularPower ν A L p theta w g*angularResponse ν A L theta w g
        ∂SYK.standardGaussianMeasureOnEuclidean ι := by
    unfold angularNormalizerDerivative
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g ↦ by
      change angularPowerDerivative ν A L p theta w g = p*(angularPower ν A L p theta w g*
        angularResponse ν A L theta w g)
      rw [angularPowerDerivative_eq ν A L hA hL hKA hKL hb]
      unfold angularResponse
      ring)
  have hz := angularNormalizer_pos ν A L hA hL hKA hKL hb p theta w
  rw [hD, angularTilt_integral_eq ν A L hA hL hKL hb]
  field_simp

theorem angularLogPressure_derivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (hp : p ≠ 0) (theta : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖angularNormalizerDerivative ν A L p theta w/(p*angularNormalizer ν A L p theta w)‖ ≤
      KA*‖w‖+KL*gaussianTiltNormBound ι (|p| *KL) := by
  rw [angularLogPressure_derivative_eq ν A L hA hL hKA hKL hb p hp]
  exact angularResponse_integral_norm_le ν A L hA hL hKA hKL hb p theta w

end
end TensorPCA.GaussianAngularExpectationProofs
