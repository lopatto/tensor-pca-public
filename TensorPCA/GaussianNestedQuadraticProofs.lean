-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianNestedTiltProofs

/-! Same-common-disorder quadratic Gibbs means used in the covariance trace. -/
@[expose] public section
namespace TensorPCA.GaussianNestedQuadraticProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem innerExpectation_continuous_common (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (w : EuclideanSpace ℝ κ) :
    Continuous (fun g ↦ expectation (gibbsMeasure ν L g) ρ A w) := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hM := shiftedSpinMoment_continuous ν ρ A L hρ hA hL hC hKA hKL hb w
  have hZ := shiftedSpinMoment_continuous ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL h1 w
  have heq : (fun g ↦ expectation (gibbsMeasure ν L g) ρ A w) =
      (fun g ↦ shiftedSpinMoment ν ρ A L w g/shiftedSpinMoment ν (fun _ ↦ 1) A L w g) :=
    funext (expectation_gibbs_shift_eq ν ρ A L hA hL hf w)
  rw [heq]
  exact hM.div hZ (fun g ↦ (shiftedSpinMoment_one_pos ν A L hA hL hf w g).ne')

def squareIntegrand (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  nestedIntegrand ν (fun _ ↦ 1) A L p w g*(expectation (gibbsMeasure ν L g) ρ A w)^2

theorem squareIntegrand_continuous_common (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Continuous (squareIntegrand ν ρ A L p w) := by
  exact (nestedIntegrand_continuous ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p w).mul
      ((innerExpectation_continuous_common ν ρ A L hρ hA hL hC hKA hKL hb w).pow 2)

theorem squareIntegrand_norm_le_one (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖squareIntegrand ν ρ A L p w g‖ ≤ C^2*nestedIntegrand ν (fun _ ↦ 1) A L p w g := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  have hE := norm_expectation_le (gibbsMeasure ν L g) ρ A hρ hA hC hbg w
  have hU := (nestedIntegrand_one_pos ν A L hA hL (hb.mono (fun _ hv ↦ hv.2)) p w g).le
  rw [squareIntegrand, norm_mul, Real.norm_of_nonneg hU, norm_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hE 2) hU).trans_eq (mul_comm _ _)

theorem squareIntegrand_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖squareIntegrand ν ρ A L p w g‖ ≤ (C^2*Real.exp ((|p| *KA)*‖w‖))*powerWeight ν L p g := by
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have H := nestedIntegrand_norm_le ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one h1 p w g
  rw [Real.norm_of_nonneg (nestedIntegrand_one_pos ν A L hA hL (hb.mono (fun _ hv ↦ hv.2)) p w g).le] at H
  exact (squareIntegrand_norm_le_one ν ρ A L hρ hA hL hC hb p w g).trans
    ((mul_le_mul_of_nonneg_left H (sq_nonneg C)).trans_eq (by simp only [one_mul]; ring))

theorem squareIntegrand_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (squareIntegrand ν ρ A L p w) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul
    (C^2*Real.exp ((|p| *KA)*‖w‖))).mono'
      (squareIntegrand_continuous_common ν ρ A L hρ hA hL hC hKA hKL hb p w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (squareIntegrand_norm_le ν ρ A L hρ hA hL hC hb p w)

def squareNumerator (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∫ g, squareIntegrand ν ρ A L p w g ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem squareNumerator_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    Continuous (squareNumerator ν ρ A L p) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  let B := C^2*Real.exp ((|p| *KA)*(‖w‖+1))
  apply continuousAt_of_dominated (bound := fun g ↦ B*powerWeight ν L p g)
  · exact Filter.Eventually.of_forall (fun z ↦
      (squareIntegrand_integrable ν ρ A L hρ hA hL hC hKA hKL hb p z).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds w zero_lt_one] with z hz
    exact Filter.Eventually.of_forall (fun g ↦
      (squareIntegrand_norm_le ν ρ A L hρ hA hL hC hb p z g).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (norm_le_of_mem_ball hz) (mul_nonneg (abs_nonneg p) hKA)))
            (sq_nonneg C)) (powerWeight_pos ν L p g).le))
  · exact (powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul B
  · apply Filter.Eventually.of_forall
    intro g
    letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
    have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
      (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
    have hc := (powerWeight_contDiff (gibbsMeasure ν L g) A hA hKA (hbg.mono (fun _ hv ↦ hv.2)) p).continuous
    have he := (expectation_contDiff (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg).continuous
    have heq : (fun z ↦ squareIntegrand ν ρ A L p z g) = (fun z ↦
        powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p z*(expectation (gibbsMeasure ν L g) ρ A z)^2) := by
      funext z
      rw [squareIntegrand, nestedIntegrand_one_eq ν A L hA hL (hb.mono (fun _ hv ↦ hv.2))]
    rw [heq]
    exact ((continuous_const.mul hc).mul (he.pow 2)).continuousAt

def nestedSquareMean (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  squareNumerator ν ρ A L p w/nestedNumerator ν (fun _ ↦ 1) A L p w

theorem nestedSquareMean_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    Continuous (nestedSquareMean ν ρ A L p) := by
  exact (squareNumerator_continuous ν ρ A L hρ hA hL hC hKA hKL hb p).div
    (nestedNumerator_contDiff ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
      (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p).continuous
    (fun w ↦ (nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w).ne')

theorem nestedSquareMean_eq_integral (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    nestedSquareMean ν ρ A L p w =
      ∫ g, (expectation (gibbsMeasure ν L g) ρ A w)^2 ∂nestedTilt ν A L p w := by
  rw [nestedTilt_integral_eq ν A L hA hL hKA hKL hb]
  rfl

theorem innerExpectation_square_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (fun g ↦ (expectation (gibbsMeasure ν L g) ρ A w)^2) (nestedTilt ν A L p w) := by
  letI := nestedTilt_probability ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  apply Integrable.of_bound ((innerExpectation_continuous_common ν ρ A L hρ hA hL hC hKA hKL hb w).pow 2).aestronglyMeasurable (C^2)
  apply Filter.Eventually.of_forall
  intro g
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  change ‖(expectation (gibbsMeasure ν L g) ρ A w)^2‖ ≤ C^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_expectation_le _ ρ A hρ hA hC hbg w) 2

theorem nestedSquareMean_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖nestedSquareMean ν ρ A L p w‖ ≤ C^2 := by
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  have hi := squareIntegrand_integrable ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hi1 := nestedIntegrand_integrable ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p w
  have hn : ‖squareNumerator ν ρ A L p w‖ ≤ C^2*nestedNumerator ν (fun _ ↦ 1) A L p w := by
    calc
      _ ≤ ∫ g, ‖squareIntegrand ν ρ A L p w g‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ g, C^2*nestedIntegrand ν (fun _ ↦ 1) A L p w g ∂SYK.standardGaussianMeasureOnEuclidean ι :=
        integral_mono_ae hi.norm (hi1.const_mul _) (Filter.Eventually.of_forall
          (squareIntegrand_norm_le_one ν ρ A L hρ hA hL hC hb p w))
      _ = _ := integral_const_mul _ _
  rw [nestedSquareMean, norm_div, Real.norm_of_nonneg hz.le]
  exact (div_le_iff₀ hz).mpr hn

theorem nestedSquareMean_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    Integrable (nestedSquareMean ν ρ A L p) (SYK.standardGaussianMeasureOnEuclidean κ) := by
  exact Integrable.of_bound (nestedSquareMean_continuous ν ρ A L hρ hA hL hC hKA hKL hb p).aestronglyMeasurable
    (C^2) (Filter.Eventually.of_forall (nestedSquareMean_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p))

end
end TensorPCA.GaussianNestedQuadraticProofs
