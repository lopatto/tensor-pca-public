-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianAngularOuterProofs
public import TensorPCA.GaussianNestedQuadraticProofs
public import TensorPCA.GaussianSpinComparisonProofs

/-! Exact coordinate responses for the two distinct noises of a one-step Gibbs interpolation. -/
@[expose] public section
namespace TensorPCA.GaussianCoordinateResponseProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianSpinComparison
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open GaussianNestedQuadraticProofs GaussianAngularExpectationProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem innerExpectation_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (fun g ↦ expectation (gibbsMeasure ν L g) ρ A w) (nestedTilt ν A L p w) := by
  letI := nestedTilt_probability ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  apply Integrable.of_bound (innerExpectation_continuous_common ν ρ A L hρ hA hL hC hKA hKL hb w).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro g
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  exact norm_expectation_le _ ρ A hρ hA hC hbg w

theorem physical_coordinate_derivative [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (c : ℝ) (hc : |c| ≤ 1)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (i : κ) :
    nestedExpectationDerivative ν (coordinateObservable A i) (scaledLinear A c) L p w
      (EuclideanSpace.single i 1) = c*
        (nestedExpectation ν (fun v ↦ (coordinateObservable A i v)^2) (scaledLinear A c) L p w+
          (p-1)*nestedSquareMean ν (coordinateObservable A i) (scaledLinear A c) L p w-
          p*(nestedExpectation ν (coordinateObservable A i) (scaledLinear A c) L p w)^2) := by
  let ρ := coordinateObservable A i
  have hρ := coordinateObservable_measurable A hA i
  have hρb := coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i
  have hAc := scaledLinear_measurable A hA c
  have hf := (scaledLinear_bound_one ν A (hb.mono (fun _ hv ↦ hv.1)) c hc).and
    (hb.mono (fun _ hv ↦ hv.2))
  have hbr : ∀ᵐ v ∂ν, |ρ v| ≤ KA ∧ ‖scaledLinear A c v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hρb.and hf
  have hb2 : ∀ᵐ v ∂ν, |(ρ v)^2| ≤ KA^2 ∧ ‖scaledLinear A c v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
    filter_upwards [hbr] with v hv
    exact ⟨by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hv.1 2,hv.2⟩
  have hi2 := innerExpectation_integrable ν (fun v ↦ (ρ v)^2) (scaledLinear A c) L
    (hρ.pow_const 2) hAc hL (sq_nonneg KA) hKA hKL hb2 p w
  have hisq := innerExpectation_square_integrable ν ρ (scaledLinear A c) L hρ hAc hL hKA hKA hKL hbr p w
  have hdir : (fun v ↦ scaledLinear A c v (EuclideanSpace.single i 1)) = (fun v ↦ c*ρ v) := rfl
  have hprod : (fun v ↦ ρ v*scaledLinear A c v (EuclideanSpace.single i 1)) = (fun v ↦ c*(ρ v)^2) := by
    funext v
    simp only [scaledLinear, smul_apply, smul_eq_mul, ρ, coordinateObservable]
    ring
  rw [nestedExpectationDerivative_apply ν ρ (scaledLinear A c) L hρ hAc hL hKA hKA hKL hbr,
    hprod,hdir]
  simp_rw [expectation_const_mul]
  have hmain : (∫ g, c*expectation (gibbsMeasure ν L g) (fun v ↦ (ρ v)^2) (scaledLinear A c) w+
      (p-1)*expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w*
        (c*expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w)
          ∂nestedTilt ν (scaledLinear A c) L p w) = c*
      (nestedExpectation ν (fun v ↦ (ρ v)^2) (scaledLinear A c) L p w+
        (p-1)*nestedSquareMean ν ρ (scaledLinear A c) L p w) := by
    have heq : (fun g ↦ c*expectation (gibbsMeasure ν L g) (fun v ↦ (ρ v)^2) (scaledLinear A c) w+
        (p-1)*expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w*
          (c*expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w)) =
        (fun g ↦ c*(expectation (gibbsMeasure ν L g) (fun v ↦ (ρ v)^2) (scaledLinear A c) w+
          (p-1)*(expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w)^2)) := by funext g; ring
    rw [heq, integral_const_mul, integral_add hi2 (hisq.const_mul (p-1)),
      integral_const_mul (p-1) (fun g ↦ (expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w)^2),
      ← nestedExpectation_eq_integral ν (fun v ↦ (ρ v)^2) (scaledLinear A c) L hAc hL hKA hKL hf,
      ← nestedSquareMean_eq_integral ν ρ (scaledLinear A c) L hAc hL hKA hKL hf]
  rw [hmain, integral_const_mul c (fun g ↦ expectation (gibbsMeasure ν L g) ρ (scaledLinear A c) w),
    ← nestedExpectation_eq_integral ν ρ (scaledLinear A c) L hAc hL hKA hKL hf]
  ring

theorem nestedExpectation_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    Integrable (nestedExpectation ν ρ A L p) (SYK.standardGaussianMeasureOnEuclidean κ) :=
  Integrable.of_bound (nestedExpectation_contDiff ν ρ A L hρ hA hL hC hKA hKL hb p).continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall (nestedExpectation_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p))

theorem nestedExpectation_square_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    Integrable (fun w ↦ (nestedExpectation ν ρ A L p w)^2) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  apply Integrable.of_bound ((nestedExpectation_contDiff ν ρ A L hρ hA hL hC hKA hKL hb p).continuous.pow 2).aestronglyMeasurable (C^2)
  apply Filter.Eventually.of_forall
  intro w
  change ‖(nestedExpectation ν ρ A L p w)^2‖ ≤ C^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (nestedExpectation_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p w) 2

theorem gaussian_physical_coordinate_response [DecidableEq κ] (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (c : ℝ) (hc : |c| ≤ 1) (p : ℝ) (i : κ) :
    (∫ w, inner ℝ (EuclideanSpace.single i 1) w*
      nestedExpectation ν (coordinateObservable A i) (scaledLinear A c) L p w
        ∂SYK.standardGaussianMeasureOnEuclidean κ) = c*
      ∫ w, nestedExpectation ν (fun v ↦ (coordinateObservable A i v)^2) (scaledLinear A c) L p w+
        (p-1)*nestedSquareMean ν (coordinateObservable A i) (scaledLinear A c) L p w-
        p*(nestedExpectation ν (coordinateObservable A i) (scaledLinear A c) L p w)^2
          ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  have hρ := coordinateObservable_measurable A hA i
  have hρb := coordinateObservable_bound ν A (hb.mono (fun _ hv ↦ hv.1)) i
  have hf := (scaledLinear_bound_one ν A (hb.mono (fun _ hv ↦ hv.1)) c hc).and
    (hb.mono (fun _ hv ↦ hv.2))
  have hbr : ∀ᵐ v ∂ν, |coordinateObservable A i v| ≤ KA ∧ ‖scaledLinear A c v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hρb.and hf
  have H := gaussian_nested_expectation_ibp ν (coordinateObservable A i) (scaledLinear A c) L hρ
    (scaledLinear_measurable A hA _) hL hKA hKA hKL hbr p (EuclideanSpace.single i 1)
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (fun w ↦ physical_coordinate_derivative ν A L hA hL hKA hKL hb c hc p w i)), integral_const_mul] at H
  exact H

theorem gaussian_common_coordinate_response [DecidableEq ι] (μ : Measure V) [IsProbabilityMeasure μ]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L) {KL : ℝ} (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂μ, ‖L v‖ ≤ KL) (s : ℝ) (hs : |s| ≤ 1) (p : ℝ) (i : ι) :
    (∫ g, inner ℝ (EuclideanSpace.single i 1) g*expectation μ (coordinateObservable L i) (scaledLinear L s) g
      ∂powerTilt μ (scaledLinear L s) p) = s*
      ∫ g, expectation μ (fun v ↦ (coordinateObservable L i v)^2) (scaledLinear L s) g+
        (p-1)*(expectation μ (coordinateObservable L i) (scaledLinear L s) g)^2
          ∂powerTilt μ (scaledLinear L s) p := by
  let ρ := coordinateObservable L i
  have hρ := coordinateObservable_measurable L hL i
  have hρb := coordinateObservable_bound μ L hb i
  have hLs := scaledLinear_measurable L hL s
  have hbs := hρb.and (scaledLinear_bound_one μ L hb s hs)
  have H := gaussian_power_response_tilt μ ρ (scaledLinear L s) hρ hLs hKL hKL hbs p (EuclideanSpace.single i 1)
  have hdir : (fun v ↦ scaledLinear L s v (EuclideanSpace.single i 1)) = (fun v ↦ s*ρ v) := rfl
  have hprod : (fun v ↦ ρ v*scaledLinear L s v (EuclideanSpace.single i 1)) = (fun v ↦ s*(ρ v)^2) := by
    funext v
    simp only [scaledLinear, smul_apply, smul_eq_mul, ρ, coordinateObservable]
    ring
  rw [hdir,hprod] at H
  simp_rw [expectation_const_mul] at H
  rw [H, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g ↦ by
    change s*expectation μ (fun v ↦ (ρ v)^2) (scaledLinear L s) g+
      (p-1)*expectation μ ρ (scaledLinear L s) g*(s*expectation μ ρ (scaledLinear L s) g) =
      s*(expectation μ (fun v ↦ (ρ v)^2) (scaledLinear L s) g+
        (p-1)*(expectation μ ρ (scaledLinear L s) g)^2)
    ring)

end
end TensorPCA.GaussianCoordinateResponseProofs
