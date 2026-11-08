-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianSpinInterpolationProofs

/-! Gaussian power tilts of bounded Gibbs partition functions.
These weights supply the common-field response in one-step interpolation. -/
@[expose] public section
namespace TensorPCA.GaussianPowerGibbsProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι]

def powerWeight (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ ι) : ℝ := Real.exp (p*logPartition ν L w)

def powerWeightDerivative (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  powerWeight ν L p w • (p • score ν L w)

theorem powerWeight_pos (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ ι) : 0 < powerWeight ν L p w := Real.exp_pos _

theorem powerWeight_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    HasFDerivAt (powerWeight ν L p) (powerWeightDerivative ν L p w) w := by
  exact ((logPartition_hasFDerivAt ν L hL hK hb w).const_mul p).exp

theorem powerWeight_contDiff (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    ContDiff ℝ 1 (powerWeight ν L p) := by
  exact Real.contDiff_exp.comp (contDiff_const.mul (logPartition_contDiff ν L hL hK hb))

theorem powerWeight_le_exp_norm (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    powerWeight ν L p w ≤ Real.exp ((|p| *K)*‖w‖) := by
  apply Real.exp_le_exp.mpr
  calc
    p*logPartition ν L w ≤ |p| *|logPartition ν L w| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |p| *(K*‖w‖) := mul_le_mul_of_nonneg_left (abs_logPartition_le ν L hL hb w) (abs_nonneg p)
    _ = _ := by ring

theorem powerWeightDerivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖powerWeightDerivative ν L p w‖ ≤ (|p| *K)*Real.exp ((|p| *K)*‖w‖) := by
  calc
    _ = powerWeight ν L p w*(|p| *‖score ν L w‖) := by
      rw [powerWeightDerivative, norm_smul, norm_smul,
        Real.norm_of_nonneg (powerWeight_pos ν L p w).le, Real.norm_eq_abs]
    _ ≤ powerWeight ν L p w*(|p| *K) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_score_le ν L hL hK hb w) (abs_nonneg _))
        (powerWeight_pos ν L p w).le
    _ ≤ Real.exp ((|p| *K)*‖w‖)*(|p| *K) := mul_le_mul_of_nonneg_right
      (powerWeight_le_exp_norm ν L hL hb p w) (mul_nonneg (abs_nonneg p) hK)
    _ = _ := mul_comm _ _

theorem powerWeight_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    Integrable (powerWeight ν L p) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply (SYK.integrable_exp_mul_norm (|p| *K)).mono'
    (powerWeight_contDiff ν L hL hK hb p).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w ↦ by
    rw [Real.norm_of_nonneg (powerWeight_pos ν L p w).le]
    exact powerWeight_le_exp_norm ν L hL hb p w)

def powerObservable (ν : Measure V) (ρ : V → ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (p : ℝ) (w : EuclideanSpace ℝ ι) : ℝ :=
  powerWeight ν L p w*expectation ν ρ L w

def powerObservableDerivative (ν : Measure V) (ρ : V → ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  powerWeight ν L p w • expectationDerivative ν ρ L w+
    expectation ν ρ L w • powerWeightDerivative ν L p w

theorem powerObservable_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    HasFDerivAt (powerObservable ν ρ L p) (powerObservableDerivative ν ρ L p w) w := by
  exact (powerWeight_hasFDerivAt ν L hL hK (hb.mono (fun _ hv ↦ hv.2)) p w).mul
    (expectation_hasFDerivAt ν ρ L hρ hL hC hK hb w)

theorem powerObservable_contDiff (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) :
    ContDiff ℝ 1 (powerObservable ν ρ L p) := by
  exact (powerWeight_contDiff ν L hL hK (hb.mono (fun _ hv ↦ hv.2)) p).mul
    (expectation_contDiff ν ρ L hρ hL hC hK hb)

theorem powerObservable_abs_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    |powerObservable ν ρ L p w| ≤ C*Real.exp ((|p| *K)*‖w‖) := by
  rw [powerObservable, abs_mul, abs_of_pos (powerWeight_pos ν L p w)]
  calc
    _ ≤ powerWeight ν L p w*C := mul_le_mul_of_nonneg_left
      (norm_expectation_le ν ρ L hρ hL hC hb w) (powerWeight_pos ν L p w).le
    _ ≤ Real.exp ((|p| *K)*‖w‖)*C := mul_le_mul_of_nonneg_right
      (powerWeight_le_exp_norm ν L hL (hb.mono (fun _ hv ↦ hv.2)) p w) hC
    _ = _ := mul_comm _ _

theorem powerObservableDerivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (w : EuclideanSpace ℝ ι) :
    ‖powerObservableDerivative ν ρ L p w‖ ≤
      ((2+|p|)*C*K)*Real.exp ((|p| *K)*‖w‖) := by
  have hw := powerWeight_le_exp_norm ν L hL (hb.mono (fun _ hv ↦ hv.2)) p w
  have hwd := powerWeightDerivative_norm_le ν L hL hK (hb.mono (fun _ hv ↦ hv.2)) p w
  have he := norm_expectation_le ν ρ L hρ hL hC hb w
  have hed := norm_expectationDerivative_le ν ρ L hρ hL hC hK hb w
  calc
    _ ≤ ‖powerWeight ν L p w • expectationDerivative ν ρ L w‖+
        ‖expectation ν ρ L w • powerWeightDerivative ν L p w‖ := norm_add_le _ _
    _ = powerWeight ν L p w*‖expectationDerivative ν ρ L w‖+
        ‖expectation ν ρ L w‖*‖powerWeightDerivative ν L p w‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (powerWeight_pos ν L p w).le]
    _ ≤ Real.exp ((|p| *K)*‖w‖)*(2*C*K)+C*((|p| *K)*Real.exp ((|p| *K)*‖w‖)) :=
      add_le_add (mul_le_mul hw hed (norm_nonneg _) (Real.exp_pos _).le)
        (mul_le_mul he hwd (norm_nonneg _) hC)
    _ = _ := by ring

theorem powerObservableDerivative_apply (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ}
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (w d : EuclideanSpace ℝ ι) :
    powerObservableDerivative ν ρ L p w d = powerWeight ν L p w*
      (expectation ν (fun v ↦ ρ v*L v d) L w+
        (p-1)*expectation ν ρ L w*expectation ν (fun v ↦ L v d) L w) := by
  rw [powerObservableDerivative, ContinuousLinearMap.add_apply, smul_apply, smul_apply,
    powerWeightDerivative, smul_apply, smul_apply, expectationDerivative_apply ν ρ L hρ hL hb,
    score_apply ν L hL (hb.mono (fun _ hv ↦ hv.2))]
  simp only [smul_eq_mul]
  ring

/-- Exact common-Gaussian power response. The term p-1 comes from differentiation of the power tilt and the Gibbs normalization. -/
theorem gaussian_power_response (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (d : EuclideanSpace ℝ ι) :
    (∫ w, inner ℝ d w*powerWeight ν L p w*expectation ν ρ L w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
        ∫ w, powerWeight ν L p w*(expectation ν (fun v ↦ ρ v*L v d) L w+
          (p-1)*expectation ν ρ L w*expectation ν (fun v ↦ L v d) L w)
            ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let B := max C ((2+|p|)*C*K)
  have hd (w : EuclideanSpace ℝ ι) := powerObservable_hasFDerivAt ν ρ L hρ hL hC hK hb p w
  have hval (w : EuclideanSpace ℝ ι) :
      |powerObservable ν ρ L p w| ≤ B*Real.exp ((|p| *K)*‖w‖) :=
    (powerObservable_abs_le ν ρ L hρ hL hC hb p w).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hgrad (w : EuclideanSpace ℝ ι) :
      ‖gradient (powerObservable ν ρ L p) w‖ ≤ B*Real.exp ((|p| *K)*‖w‖) := by
    rw [gradient, (hd w).fderiv, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
    exact (powerObservableDerivative_norm_le ν ρ L hρ hL hC hK hb p w).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have H := SYK.gaussian_ibp (powerObservable ν ρ L p) d
    (powerObservable_contDiff ν ρ L hρ hL hC hK hb p) B (|p| *K) hval hgrad
  have hpoint (w : EuclideanSpace ℝ ι) :
      inner ℝ d (gradient (powerObservable ν ρ L p) w) =
        powerWeight ν L p w*(expectation ν (fun v ↦ ρ v*L v d) L w+
          (p-1)*expectation ν ρ L w*expectation ν (fun v ↦ L v d) L w) := by
    rw [real_inner_comm, gradient, (hd w).fderiv, InnerProductSpace.toDual_symm_apply,
      powerObservableDerivative_apply ν ρ L hρ hL hb]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)] at H
  simpa only [powerObservable, mul_assoc] using H

def powerTilt (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (p : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (SYK.standardGaussianMeasureOnEuclidean ι).withDensity (fun w ↦ ENNReal.ofReal
    (powerWeight ν L p w/(∫ g, powerWeight ν L p g ∂SYK.standardGaussianMeasureOnEuclidean ι)))

theorem powerWeight_integral_pos (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    0 < ∫ w, powerWeight ν L p w ∂SYK.standardGaussianMeasureOnEuclidean ι :=
  integral_exp_pos (powerWeight_integrable ν L hL hK hb p)

theorem powerTilt_probability (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ) :
    IsProbabilityMeasure (powerTilt ν L p) := by
  have hi := powerWeight_integrable ν L hL hK hb p
  have hz := powerWeight_integral_pos ν L hL hK hb p
  constructor
  rw [powerTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Filter.Eventually.of_forall (fun w ↦ (div_pos (powerWeight_pos ν L p w) hz).le)),
    integral_div, div_self hz.ne', ENNReal.ofReal_one]

theorem powerTilt_integral_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (p : ℝ)
    (f : EuclideanSpace ℝ ι → ℝ) :
    (∫ w, f w ∂powerTilt ν L p) =
      (∫ w, powerWeight ν L p w*f w ∂SYK.standardGaussianMeasureOnEuclidean ι) /
        (∫ w, powerWeight ν L p w ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hz := powerWeight_integral_pos ν L hL hK hb p
  have hm := ((powerWeight_contDiff ν L hL hK hb p).continuous.measurable.div_const
    (∫ w, powerWeight ν L p w ∂SYK.standardGaussianMeasureOnEuclidean ι)).ennreal_ofReal
  rw [powerTilt, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_pos (powerWeight_pos ν L p _) hz).le, smul_eq_mul]
  rw [← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w ↦ by ring)

theorem gaussian_power_response_tilt (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (p : ℝ) (d : EuclideanSpace ℝ ι) :
    (∫ w, inner ℝ d w*expectation ν ρ L w ∂powerTilt ν L p) =
      ∫ w, expectation ν (fun v ↦ ρ v*L v d) L w+
        (p-1)*expectation ν ρ L w*expectation ν (fun v ↦ L v d) L w ∂powerTilt ν L p := by
  rw [powerTilt_integral_eq ν L hL hK (hb.mono (fun _ hv ↦ hv.2)),
    powerTilt_integral_eq ν L hL hK (hb.mono (fun _ hv ↦ hv.2))]
  congr 1
  have H := gaussian_power_response ν ρ L hρ hL hC hK hb p d
  convert H using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w ↦ by ring)

end
end TensorPCA.GaussianPowerGibbsProofs
