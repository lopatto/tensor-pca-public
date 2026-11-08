-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianCoordinateResponseProofs

/-! Finite coordinate covariance trace of the angular one-step pressure. -/
@[expose] public section
namespace TensorPCA.GaussianAngularTraceProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianSpinComparison
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open GaussianNestedQuadraticProofs GaussianAngularPressureProofs GaussianAngularExpectationProofs GaussianAngularOuterProofs
open GaussianCoordinateResponseProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem gibbsMeasure_scaledLinear (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (c : ℝ) (w : EuclideanSpace ℝ κ) :
    gibbsMeasure ν (scaledLinear A c) w = gibbsMeasure ν A (c • w) := by
  simp only [gibbsMeasure, GaussianSpinInterpolation.moment, weight, scaledLinear,
    smul_apply, map_smul, smul_eq_mul]

theorem angular_fields_bound (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {KA KL : ℝ} (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (theta : ℝ) :
    ∀ᵐ v ∂ν, ‖scaledLinear A (Real.cos theta) v‖ ≤ KA ∧ ‖scaledLinear L (Real.sin theta) v‖ ≤ KL :=
  (scaledLinear_bound_one ν A (hb.mono (fun _ hv ↦ hv.1)) _ (Real.abs_cos_le_one theta)).and
    (scaledLinear_bound_one ν L (hb.mono (fun _ hv ↦ hv.2)) _ (Real.abs_sin_le_one theta))

theorem angularTilt_eq_nestedTilt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularTilt ν A L p theta w = nestedTilt ν (scaledLinear A (Real.cos theta))
      (scaledLinear L (Real.sin theta)) p w := by
  rw [nestedTilt_eq_powerTilt ν _ _ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hKA hKL (angular_fields_bound ν A L hb theta), gibbsMeasure_scaledLinear]
  rfl

def angularMean (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  nestedExpectation ν ρ (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta)) p w

def angularSquareMean (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  nestedSquareMean ν ρ (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta)) p w

theorem angularMean_eq_common_integral (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularMean ν ρ A L p theta w = ∫ g,
      expectation (gibbsMeasure ν (scaledLinear L (Real.sin theta)) g) ρ
        (scaledLinear A (Real.cos theta)) w ∂angularTilt ν A L p theta w := by
  rw [angularTilt_eq_nestedTilt ν A L hA hL hKA hKL hb]
  exact nestedExpectation_eq_integral ν ρ _ _ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hKA hKL (angular_fields_bound ν A L hb theta) p w

theorem angularInnerMean_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation (gibbsMeasure ν (scaledLinear L (Real.sin theta)) g) ρ (scaledLinear A (Real.cos theta)) w =
      expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g) := by
  rw [expectation_gibbs_swap ν ρ _ _ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    (angular_fields_bound ν A L hb theta), gibbsMeasure_scaledLinear, expectation_scaledLinear]

theorem angularMean_eq_physical_integral (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularMean ν ρ A L p theta w = ∫ g,
      expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g)
        ∂angularTilt ν A L p theta w := by
  rw [angularMean_eq_common_integral ν ρ A L hA hL hKA hKL hb]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (angularInnerMean_eq ν ρ A L hA hL hb theta w)

theorem angularSquareMean_eq_physical_integral (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    angularSquareMean ν ρ A L p theta w = ∫ g,
      (expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g))^2
        ∂angularTilt ν A L p theta w := by
  rw [angularTilt_eq_nestedTilt ν A L hA hL hKA hKL hb]
  unfold angularSquareMean
  rw [nestedSquareMean_eq_integral ν ρ _ _ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hKA hKL (angular_fields_bound ν A L hb theta)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g ↦ congrArg (fun r : ℝ ↦ r^2) (angularInnerMean_eq ν ρ A L hA hL hb theta w g))

theorem angularMean_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (angularMean ν ρ A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) :=
  nestedExpectation_integrable ν ρ _ _ hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hC hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p

theorem angularSquareMean_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (angularSquareMean ν ρ A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) :=
  nestedSquareMean_integrable ν ρ _ _ hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hC hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p

theorem angularMean_square_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (fun w ↦ (angularMean ν ρ A L p theta w)^2) (SYK.standardGaussianMeasureOnEuclidean κ) :=
  nestedExpectation_square_integrable ν ρ _ _ hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hC hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p

theorem angular_physical_coordinate [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (i : κ) :
    (∫ w, inner ℝ (EuclideanSpace.single i 1) w*angularMean ν (coordinateObservable A i) A L p theta w
      ∂SYK.standardGaussianMeasureOnEuclidean κ) = Real.cos theta*
      ∫ w, angularMean ν (fun v ↦ (coordinateObservable A i v)^2) A L p theta w+
        (p-1)*angularSquareMean ν (coordinateObservable A i) A L p theta w-
        p*(angularMean ν (coordinateObservable A i) A L p theta w)^2
          ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  exact gaussian_physical_coordinate_response ν A (scaledLinear L (Real.sin theta)) hA (scaledLinear_measurable L hL _)
    hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and
      (scaledLinear_bound_one ν L (hb.mono (fun _ hv ↦ hv.2)) _ (Real.abs_sin_le_one theta)))
    (Real.cos theta) (Real.abs_cos_le_one theta) p i

theorem angular_inner_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (fun g ↦ expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g))
      (angularTilt ν A L p theta w) := by
  rw [angularTilt_eq_nestedTilt ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2))]
  have H := innerExpectation_integrable ν ρ (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta))
    hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _) hC hKA hKL
    ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p w
  simpa only [angularInnerMean_eq ν ρ A L hA hL (hb.mono (fun _ hv ↦ hv.2)) theta w] using H

theorem angular_inner_square_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (fun g ↦ (expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g))^2)
      (angularTilt ν A L p theta w) := by
  rw [angularTilt_eq_nestedTilt ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2))]
  have H := innerExpectation_square_integrable ν ρ (scaledLinear A (Real.cos theta)) (scaledLinear L (Real.sin theta))
    hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _) hC hKA hKL
    ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p w
  simpa only [angularInnerMean_eq ν ρ A L hA hL (hb.mono (fun _ hv ↦ hv.2)) theta w] using H

theorem angular_common_coordinate [DecidableEq ι] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) (i : ι) :
    (∫ g, inner ℝ (EuclideanSpace.single i 1) g*
      expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable L i) L (Real.sin theta • g)
        ∂angularTilt ν A L p theta w) = Real.sin theta*
      (angularMean ν (fun v ↦ (coordinateObservable L i v)^2) A L p theta w+
        (p-1)*angularSquareMean ν (coordinateObservable L i) A L p theta w) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le (hb.mono (fun _ hv ↦ hv.2))
  have H := gaussian_common_coordinate_response (gibbsMeasure ν A (Real.cos theta • w)) L hL hKL hLg
    (Real.sin theta) (Real.abs_sin_le_one theta) p i
  simp only [expectation_scaledLinear] at H
  have hρ := coordinateObservable_measurable L hL i
  have hρb := coordinateObservable_bound ν L (hb.mono (fun _ hv ↦ hv.2)) i
  have hbr := hρb.and hb
  have hb2 : ∀ᵐ v ∂ν, |(coordinateObservable L i v)^2| ≤ KL^2 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
    filter_upwards [hbr] with v hv
    exact ⟨by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv.1 2,hv.2⟩
  have hi2 := angular_inner_integrable ν _ A L (hρ.pow_const 2) hA hL (sq_nonneg KL) hKA hKL hb2 p theta w
  have hisq := angular_inner_square_integrable ν _ A L hρ hA hL hKL hKA hKL hbr p theta w
  change (∫ g, inner ℝ (EuclideanSpace.single i 1) g*
      expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable L i) L (Real.sin theta • g)
        ∂powerTilt (gibbsMeasure ν A (Real.cos theta • w)) (scaledLinear L (Real.sin theta)) p) = _
  rw [H]
  change Real.sin theta*(∫ g, expectation (gibbsMeasure ν A (Real.cos theta • w))
      (fun v ↦ (coordinateObservable L i v)^2) L (Real.sin theta • g)+
      (p-1)*(expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable L i) L (Real.sin theta • g))^2
      ∂angularTilt ν A L p theta w) = _
  rw [integral_add hi2 (hisq.const_mul (p-1)), integral_const_mul,
    ← angularMean_eq_physical_integral ν _ A L hA hL hKA hKL hb,
    ← angularSquareMean_eq_physical_integral ν _ A L hA hL hKA hKL hb]

theorem angularMean_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Continuous (angularMean ν ρ A L p theta) :=
  (nestedExpectation_contDiff ν ρ _ _ hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hC hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p).continuous

theorem angularMean_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖angularMean ν ρ A L p theta w‖ ≤ C :=
  nestedExpectation_norm_le ν ρ _ _ hρ (scaledLinear_measurable A hA _) (scaledLinear_measurable L hL _)
    hC hKA hKL ((hb.mono (fun _ hv ↦ hv.1)).and (angular_fields_bound ν A L (hb.mono (fun _ hv ↦ hv.2)) theta)) p w

theorem angular_physical_product_integrable [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (i : κ) :
    Integrable (fun w ↦ inner ℝ (EuclideanSpace.single i 1) w*angularMean ν (coordinateObservable A i) A L p theta w)
      (SYK.standardGaussianMeasureOnEuclidean κ) := by
  have hρ := coordinateObservable_measurable A hA i
  have hbr := (coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb
  have hc : Continuous (fun w ↦ inner ℝ (EuclideanSpace.single i 1) w*angularMean ν (coordinateObservable A i) A L p theta w) :=
    (continuous_const.inner continuous_id).mul
    (angularMean_continuous ν _ A L hρ hA hL hKA hKA hKL hbr p theta)
  apply ((gaussian_norm_integrable (ι := κ)).const_mul KA).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro w
  rw [norm_mul]
  have he : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ κ)‖ = 1 := by simp
  have hi : ‖inner ℝ (EuclideanSpace.single i 1) w‖ ≤ ‖w‖ := by
    simpa only [he,one_mul] using norm_inner_le_norm (EuclideanSpace.single i 1) w
  exact (mul_le_mul hi (angularMean_norm_le ν _ A L hρ hA hL hKA hKA hKL hbr p theta w)
    (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem angular_common_product_integrable [DecidableEq ι] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) (i : ι) :
    Integrable (fun g ↦ inner ℝ (EuclideanSpace.single i 1) g*
      expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable L i) L (Real.sin theta • g))
      (angularTilt ν A L p theta w) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hρ := coordinateObservable_measurable L hL i
  have hbr := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    ((coordinateObservable_bound ν L (hb.mono (fun _ hv ↦ hv.2)) i).and (hb.mono (fun _ hv ↦ hv.2)))
  have hc : Continuous (fun g ↦ inner ℝ (EuclideanSpace.single i 1) g*
      expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable L i) L (Real.sin theta • g)) :=
    (continuous_const.inner continuous_id).mul
    ((expectation_contDiff _ _ L hρ hL hKL hKL hbr).continuous.comp (continuous_const_smul (Real.sin theta)))
  apply ((angularTilt_norm_integrable ν A L hA hL hKL hb p theta w).const_mul KL).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  rw [norm_mul]
  have he : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ ι)‖ = 1 := by simp
  have hi : ‖inner ℝ (EuclideanSpace.single i 1) g‖ ≤ ‖g‖ := by
    simpa only [he,one_mul] using norm_inner_le_norm (EuclideanSpace.single i 1) g
  exact (mul_le_mul hi (norm_expectation_le _ _ L hρ hL hKL hbr (Real.sin theta • g))
    (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem angular_physical_score_eq_sum [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L (Real.sin theta • g) =
      ∑ i, inner ℝ (EuclideanSpace.single i 1) w*
        expectation (gibbsMeasure ν A (Real.cos theta • w)) (coordinateObservable A i) L (Real.sin theta • g) := by
  letI := gibbsMeasure_probability ν (scaledLinear L (Real.sin theta)) (scaledLinear_measurable L hL _)
    (scaledLinear_bound_one ν L (hb.mono (fun _ hv ↦ hv.2)) _ (Real.abs_sin_le_one theta)) g
  have hAg := (gibbsMeasure_absolutelyContinuous ν (scaledLinear L (Real.sin theta)) g).ae_le (hb.mono (fun _ hv ↦ hv.1))
  rw [← angularInnerMean_eq ν _ A L hA hL hb theta w g, expectation_scaledLinear,
    ← score_apply _ A hA hAg, score_eq_coordinate_sum _ A hA hAg]
  apply Finset.sum_congr rfl
  intro i _
  rw [← expectation_scaledLinear _ _ A (Real.cos theta) w,
    angularInnerMean_eq ν _ A L hA hL hb theta w g]
  simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul]
  rfl

def physicalTrace [DecidableEq κ] (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∑ i, (angularMean ν (fun v ↦ (coordinateObservable A i v)^2) A L p theta w+
    (p-1)*angularSquareMean ν (coordinateObservable A i) A L p theta w-
    p*(angularMean ν (coordinateObservable A i) A L p theta w)^2)

def commonTrace [DecidableEq ι] (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∑ i, (angularMean ν (fun v ↦ (coordinateObservable L i v)^2) A L p theta w+
    (p-1)*angularSquareMean ν (coordinateObservable L i) A L p theta w)

theorem angular_response_integral_eq [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    (∫ g, angularResponse ν A L theta w g ∂angularTilt ν A L p theta w) =
      -Real.sin theta*(∑ i, inner ℝ (EuclideanSpace.single i 1) w*
        angularMean ν (coordinateObservable A i) A L p theta w)+
      Real.cos theta*Real.sin theta*commonTrace ν A L p theta w := by
  let μ := gibbsMeasure ν A (Real.cos theta • w)
  let τ := angularTilt ν A L p theta w
  let F : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i, inner ℝ (EuclideanSpace.single i 1) w*
    expectation μ (coordinateObservable A i) L (Real.sin theta • g)
  let G : EuclideanSpace ℝ ι → ℝ := fun g ↦ ∑ i, inner ℝ (EuclideanSpace.single i 1) g*
    expectation μ (coordinateObservable L i) L (Real.sin theta • g)
  have hFi (i : κ) : Integrable (fun g ↦ inner ℝ (EuclideanSpace.single i 1) w*
      expectation μ (coordinateObservable A i) L (Real.sin theta • g)) τ :=
    (angular_inner_integrable ν _ A L (coordinateObservable_measurable A hA i) hA hL hKA hKA hKL
      ((coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb) p theta w).const_mul _
  have hGi (i : ι) : Integrable (fun g ↦ inner ℝ (EuclideanSpace.single i 1) g*
      expectation μ (coordinateObservable L i) L (Real.sin theta • g)) τ :=
    angular_common_product_integrable ν A L hA hL hKA hKL hb p theta w i
  have hF : Integrable F τ := integrable_finset_sum _ (fun i _ ↦ hFi i)
  have hG : Integrable G τ := integrable_finset_sum _ (fun i _ ↦ hGi i)
  have hEq : angularResponse ν A L theta w = fun g ↦ -Real.sin theta*F g+Real.cos theta*G g := by
    funext g
    letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
    have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le (hb.mono (fun _ hv ↦ hv.2))
    dsimp only [angularResponse,F,G,μ]
    rw [angular_physical_score_eq_sum ν A L hA hL hb,
      score_eq_coordinate_sum _ L hL hLg]
    simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul]
    rfl
  rw [hEq,integral_add (hF.const_mul _) (hG.const_mul _),integral_const_mul,integral_const_mul]
  have hFint : (∫ g, F g ∂τ) = ∑ i, inner ℝ (EuclideanSpace.single i 1) w*
      angularMean ν (coordinateObservable A i) A L p theta w := by
    rw [show F = fun g ↦ ∑ i, inner ℝ (EuclideanSpace.single i 1) w*
      expectation μ (coordinateObservable A i) L (Real.sin theta • g) from rfl,
      integral_finset_sum _ (fun i _ ↦ hFi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, ← angularMean_eq_physical_integral ν _ A L hA hL hKA hKL hb]
  have hGint : (∫ g, G g ∂τ) = Real.sin theta*commonTrace ν A L p theta w := by
    rw [show G = fun g ↦ ∑ i, inner ℝ (EuclideanSpace.single i 1) g*
      expectation μ (coordinateObservable L i) L (Real.sin theta • g) from rfl,
      integral_finset_sum _ (fun i _ ↦ hGi i)]
    dsimp only [μ,τ]
    simp_rw [angular_common_coordinate ν A L hA hL hKA hKL hb p theta w]
    exact (Finset.mul_sum _ _ _).symm
  rw [hFint,hGint]
  ring

theorem angular_moments_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (angularMean ν (fun v ↦ (ρ v)^2) A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) ∧
    Integrable (angularSquareMean ν ρ A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) ∧
    Integrable (fun w ↦ (angularMean ν ρ A L p theta w)^2) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  have hb2 : ∀ᵐ v ∂ν, |(ρ v)^2| ≤ C^2 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
    filter_upwards [hb] with v hv
    exact ⟨by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv.1 2,hv.2⟩
  exact ⟨angularMean_integrable ν _ A L (hρ.pow_const 2) hA hL (sq_nonneg C) hKA hKL hb2 p theta,
    angularSquareMean_integrable ν ρ A L hρ hA hL hC hKA hKL hb p theta,
    angularMean_square_integrable ν ρ A L hρ hA hL hC hKA hKL hb p theta⟩

theorem physical_trace_integrable [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (physicalTrace ν A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  apply integrable_finset_sum
  intro i _
  have H := angular_moments_integrable ν (coordinateObservable A i) A L
    (coordinateObservable_measurable A hA i) hA hL hKA hKA hKL
    ((coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb) p theta
  exact (H.1.add (H.2.1.const_mul (p-1))).sub (H.2.2.const_mul p)

theorem common_trace_integrable [DecidableEq ι] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    Integrable (commonTrace ν A L p theta) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  apply integrable_finset_sum
  intro i _
  have H := angular_moments_integrable ν (coordinateObservable L i) A L
    (coordinateObservable_measurable L hL i) hA hL hKL hKA hKL
    ((coordinateObservable_bound ν L (hb.mono (fun _ hv ↦ hv.2)) i).and hb) p theta
  exact H.1.add (H.2.1.const_mul (p-1))

theorem integral_physical_field_eq [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p theta : ℝ) :
    (∫ w, ∑ i, inner ℝ (EuclideanSpace.single i 1) w*angularMean ν (coordinateObservable A i) A L p theta w
      ∂SYK.standardGaussianMeasureOnEuclidean κ) = Real.cos theta*
        ∫ w, physicalTrace ν A L p theta w ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  have hi (i : κ) : Integrable (fun w ↦ angularMean ν (fun v ↦ (coordinateObservable A i v)^2) A L p theta w+
      (p-1)*angularSquareMean ν (coordinateObservable A i) A L p theta w-
      p*(angularMean ν (coordinateObservable A i) A L p theta w)^2) (SYK.standardGaussianMeasureOnEuclidean κ) := by
    have H := angular_moments_integrable ν (coordinateObservable A i) A L
      (coordinateObservable_measurable A hA i) hA hL hKA hKA hKL
      ((coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i).and hb) p theta
    exact (H.1.add (H.2.1.const_mul (p-1))).sub (H.2.2.const_mul p)
  rw [integral_finset_sum _ (fun i _ ↦ angular_physical_product_integrable ν A L hA hL hKA hKL hb p theta i)]
  simp_rw [angular_physical_coordinate ν A L hA hL hKA hKL hb p theta]
  rw [← Finset.mul_sum]
  congr 1
  exact (integral_finset_sum _ (fun i _ ↦ hi i)).symm

theorem averagedAngularDerivative_eq_trace [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≠ 0) (theta : ℝ) :
    averagedAngularDerivative ν A L p theta = Real.sin theta*Real.cos theta*
      ∫ w, commonTrace ν A L p theta w-physicalTrace ν A L p theta w
        ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  have hiF := integrable_finset_sum Finset.univ
    (fun i _ ↦ angular_physical_product_integrable ν A L hA hL hKA hKL hb p theta i)
  have hiC := common_trace_integrable ν A L hA hL hKA hKL hb p theta
  have hiP := physical_trace_integrable ν A L hA hL hKA hKL hb p theta
  unfold averagedAngularDerivative
  simp_rw [angularLogPressure_derivative_eq ν A L hA hL hKA hKL hb p hp,
    angular_response_integral_eq ν A L hA hL hKA hKL hb p theta]
  rw [integral_add (hiF.const_mul _) (hiC.const_mul _),integral_const_mul,integral_const_mul,
    integral_physical_field_eq ν A L hA hL hKA hKL hb p theta, integral_sub hiC hiP]
  ring

theorem averagedAngularPressure_hasDerivAt_trace [DecidableEq ι] [DecidableEq κ]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (hp : p ≠ 0) (theta : ℝ) :
    HasDerivAt (averagedAngularPressure ν A L p)
      (Real.sin theta*Real.cos theta*∫ w, commonTrace ν A L p theta w-physicalTrace ν A L p theta w
        ∂SYK.standardGaussianMeasureOnEuclidean κ) theta := by
  rw [← averagedAngularDerivative_eq_trace ν A L hA hL hKA hKL hb p hp theta]
  exact averagedAngularPressure_hasDerivAt ν A L hA hL hKA hKL hb p hp theta

end
end TensorPCA.GaussianAngularTraceProofs
