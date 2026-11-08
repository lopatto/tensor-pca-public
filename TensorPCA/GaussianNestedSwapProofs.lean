-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianNestedTiltProofs

/-! Commuting physical/common Gibbs tilts and the nested common-noise response. -/
@[expose] public section
namespace TensorPCA.GaussianNestedSwapProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem shiftedSpinMoment_swap (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    shiftedSpinMoment ν ρ A L w g = shiftedSpinMoment ν ρ L A g w := by
  unfold shiftedSpinMoment GaussianSpinInterpolation.moment weight
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun _ ↦ by ring)

theorem expectation_gibbs_swap (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation (gibbsMeasure ν L g) ρ A w = expectation (gibbsMeasure ν A w) ρ L g := by
  rw [expectation_gibbs_shift_eq ν ρ A L hA hL hb,
    expectation_gibbs_shift_eq ν ρ L A hL hA (hb.mono (fun _ hv ↦ hv.symm)),
    shiftedSpinMoment_swap ν ρ A L w g, shiftedSpinMoment_swap ν (fun _ ↦ 1) A L w g]

theorem nestedIntegrand_one_exp (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    nestedIntegrand ν (fun _ ↦ 1) A L p w g =
      Real.exp (p*Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g)) := by
  rw [nestedIntegrand_eq ν (fun _ ↦ 1) A L hA hL hb]
  have hz := shiftedSpinMoment_one_pos ν A L hA hL hb w g
  nth_rw 2 [← Real.exp_log hz]
  rw [← Real.exp_add]
  congr 1
  ring

theorem nestedIntegrand_one_factor (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    nestedIntegrand ν (fun _ ↦ 1) A L p w g =
      powerWeight ν A p w*powerWeight (gibbsMeasure ν A w) L p g := by
  have hm := moment_gibbs_shift_eq ν (fun _ ↦ 1) L A hA (hb.mono (fun _ hv ↦ hv.1)) g w
  rw [← shiftedSpinMoment_swap ν (fun _ ↦ 1) A L w g] at hm
  have hz := moment_one_pos ν A hA (hb.mono (fun _ hv ↦ hv.1)) w
  have hs := shiftedSpinMoment_one_pos ν A L hA hL hb w g
  rw [nestedIntegrand_one_exp ν A L hA hL hb]
  unfold powerWeight logPartition
  rw [hm, Real.log_div hs.ne' hz.ne', ← Real.exp_add]
  congr 1
  ring

theorem nestedNumerator_one_factor (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    nestedNumerator ν (fun _ ↦ 1) A L p w = powerWeight ν A p w*
      ∫ g, powerWeight (gibbsMeasure ν A w) L p g ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  unfold nestedNumerator
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (nestedIntegrand_one_factor ν A L hA hL hb p w)

theorem nestedTilt_eq_powerTilt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hKA : 0 ≤ KA) (hKL : 0 ≤ KL) (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    nestedTilt ν A L p w = powerTilt (gibbsMeasure ν A w) L p := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) w
  have hLg : ∀ᵐ v ∂gibbsMeasure ν A w, ‖L v‖ ≤ KL :=
    (gibbsMeasure_absolutelyContinuous ν A w).ae_le (hb.mono (fun _ hv ↦ hv.2))
  have hz := powerWeight_integral_pos (gibbsMeasure ν A w) L hL hKL hLg p
  have hc := powerWeight_pos ν A p w
  unfold nestedTilt powerTilt
  congr 1
  funext g
  rw [nestedIntegrand_one_factor ν A L hA hL hb, nestedNumerator_one_factor ν A L hA hL hb]
  congr 1
  field_simp

/-- The common-noise response in the very same two-stage probability law as
the physical response. Swapping the Gibbs bases is proved, not assumed. -/
theorem gaussian_nested_common_response (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (d : EuclideanSpace ℝ ι) :
    (∫ g, inner ℝ d g*expectation (gibbsMeasure ν L g) ρ A w ∂nestedTilt ν A L p w) =
      ∫ g, expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*L v d) A w+
        (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
          expectation (gibbsMeasure ν L g) (fun v ↦ L v d) A w ∂nestedTilt ν A L p w := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  letI := gibbsMeasure_probability ν A hA (hf.mono (fun _ hv ↦ hv.1)) w
  have hbg : ∀ᵐ v ∂gibbsMeasure ν A w, |ρ v| ≤ C ∧ ‖L v‖ ≤ KL :=
    (gibbsMeasure_absolutelyContinuous ν A w).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.2⟩))
  have H := gaussian_power_response_tilt (gibbsMeasure ν A w) ρ L hρ hL hC hKL hbg p d
  rw [nestedTilt_eq_powerTilt ν A L hA hL hKA hKL hf]
  simpa only [expectation_gibbs_swap ν ρ A L hA hL hf w,
    expectation_gibbs_swap ν (fun v ↦ ρ v*L v d) A L hA hL hf w,
    expectation_gibbs_swap ν (fun v ↦ L v d) A L hA hL hf w] using H

end
end TensorPCA.GaussianNestedSwapProofs
