-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPowerGibbsProofs

/-! Two-stage Gaussian Gibbs integrals with a full external Euclidean
parameter. No nested response identity is assumed. -/
@[expose] public section
namespace TensorPCA.GaussianNestedGibbsProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

def shiftedSpinMoment (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  moment ν (fun v ↦ ρ v*Real.exp (A v w)) L g

theorem shiftedSpinMoment_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (w : EuclideanSpace ℝ κ) :
    Continuous (shiftedSpinMoment ν ρ A L w) := by
  have hw : ∀ᵐ v ∂ν, |ρ v*Real.exp (A v w)| ≤ C*Real.exp (KA*‖w‖) ∧ ‖L v‖ ≤ KL := by
    filter_upwards [hb] with v hv
    refine ⟨?_,hv.2.2⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hav : A v w ≤ KA*‖w‖ := (le_abs_self _).trans
      (((A v).le_opNorm w).trans (mul_le_mul_of_nonneg_right hv.2.1 (norm_nonneg _)))
    exact mul_le_mul hv.1 (Real.exp_le_exp.mpr hav) (Real.exp_pos _).le hC
  have hm : Measurable (fun v ↦ ρ v*Real.exp (A v w)) :=
    hρ.mul (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hA).exp)
  exact (moment_contDiff ν (fun v ↦ ρ v*Real.exp (A v w)) L hm hL
    (mul_nonneg hC (Real.exp_pos _).le) hKL hw).continuous

theorem moment_gibbs_shift_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {KL : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    moment (gibbsMeasure ν L g) ρ A w =
      shiftedSpinMoment ν ρ A L w g/moment ν (fun _ ↦ 1) L g := by
  change (∫ v, ρ v*Real.exp (A v w) ∂gibbsMeasure ν L g) = _
  rw [integral_gibbsMeasure ν L hL hb]
  rfl

theorem shiftedSpinMoment_one_pos (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    0 < shiftedSpinMoment ν (fun _ ↦ 1) A L w g := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  letI := gibbsMeasure_probability ν L hL hf g
  have hAb : ∀ᵐ v ∂gibbsMeasure ν L g, ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ hv.1))
  have hp := moment_one_pos (gibbsMeasure ν L g) A hA hAb w
  rw [moment_gibbs_shift_eq ν (fun _ ↦ 1) A L hL hf] at hp
  have H := mul_pos hp (moment_one_pos ν L hL hf g)
  simpa only [div_mul_cancel₀ _ (moment_one_pos ν L hL hf g).ne'] using H

def nestedIntegrand (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  powerWeight ν L p g*powerObservable (gibbsMeasure ν L g) ρ A p w

theorem nestedIntegrand_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    nestedIntegrand ν ρ A L p w g =
      Real.exp ((p-1)*Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g))*
        shiftedSpinMoment ν ρ A L w g := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  have hz := moment_one_pos ν L hL hf g
  have hs := shiftedSpinMoment_one_pos ν A L hA hL hb w g
  unfold nestedIntegrand powerObservable powerWeight logPartition expectation
  rw [moment_gibbs_shift_eq ν (fun _ ↦ 1) A L hL hf,
    moment_gibbs_shift_eq ν ρ A L hL hf, Real.log_div hs.ne' hz.ne']
  rw [← mul_assoc, ← Real.exp_add]
  have he : p*Real.log (moment ν (fun _ ↦ 1) L g)+
      p*(Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g)-
        Real.log (moment ν (fun _ ↦ 1) L g)) =
      (p-1)*Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g)+
        Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g) := by ring
  rw [he, Real.exp_add, Real.exp_log hs]
  field_simp

theorem nestedIntegrand_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : Continuous (nestedIntegrand ν ρ A L p w) := by
  have hf := hb.mono (fun _ hv ↦ hv.2)
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hZ := shiftedSpinMoment_continuous ν (fun _ ↦ 1) A L measurable_const hA hL
    zero_le_one hKA hKL h1 w
  have hM := shiftedSpinMoment_continuous ν ρ A L hρ hA hL hC hKA hKL hb w
  have heq : nestedIntegrand ν ρ A L p w = (fun g ↦
      Real.exp ((p-1)*Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g))*
        shiftedSpinMoment ν ρ A L w g) := funext (nestedIntegrand_eq ν ρ A L hA hL hf p w)
  rw [heq]
  exact (Real.continuous_exp.comp (continuous_const.mul (hZ.log
    (fun g ↦ (shiftedSpinMoment_one_pos ν A L hA hL hf w g).ne')))).mul hM

def nestedIntegrandDerivative (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ κ →L[ℝ] ℝ :=
  powerWeight ν L p g • powerObservableDerivative (gibbsMeasure ν L g) ρ A p w

theorem nestedIntegrand_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun z ↦ nestedIntegrand ν ρ A L p z g) (nestedIntegrandDerivative ν ρ A L p w g) w := by
  have hf := hb.mono (fun _ hv ↦ hv.2.2)
  letI := gibbsMeasure_probability ν L hL hf g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  exact (powerObservable_hasFDerivAt (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg p w).const_mul
    (powerWeight ν L p g)

theorem nestedIntegrand_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖nestedIntegrand ν ρ A L p w g‖ ≤ (C*Real.exp ((|p| *KA)*‖w‖))*powerWeight ν L p g := by
  have hf := hb.mono (fun _ hv ↦ hv.2.2)
  letI := gibbsMeasure_probability ν L hL hf g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  rw [nestedIntegrand, norm_mul, Real.norm_of_nonneg (powerWeight_pos ν L p g).le, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (powerObservable_abs_le (gibbsMeasure ν L g) ρ A hρ hA hC hbg p w)
    (powerWeight_pos ν L p g).le).trans_eq (mul_comm _ _)

theorem nestedIntegrandDerivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖nestedIntegrandDerivative ν ρ A L p w g‖ ≤
      (((2+|p|)*C*KA)*Real.exp ((|p| *KA)*‖w‖))*powerWeight ν L p g := by
  have hf := hb.mono (fun _ hv ↦ hv.2.2)
  letI := gibbsMeasure_probability ν L hL hf g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  rw [nestedIntegrandDerivative, norm_smul, Real.norm_of_nonneg (powerWeight_pos ν L p g).le]
  exact (mul_le_mul_of_nonneg_left
    (powerObservableDerivative_norm_le (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg p w)
      (powerWeight_pos ν L p g).le).trans_eq (mul_comm _ _)

theorem nestedIntegrand_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (nestedIntegrand ν ρ A L p w) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul
    (C*Real.exp ((|p| *KA)*‖w‖))).mono'
      (nestedIntegrand_continuous ν ρ A L hρ hA hL hC hKA hKL hb p w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (nestedIntegrand_norm_le ν ρ A L hρ hA hL hC hb p w)

theorem expectation_gibbs_shift_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation (gibbsMeasure ν L g) ρ A w =
      shiftedSpinMoment ν ρ A L w g/shiftedSpinMoment ν (fun _ ↦ 1) A L w g := by
  have hz := moment_one_pos ν L hL (hb.mono (fun _ hv ↦ hv.2)) g
  have hs := shiftedSpinMoment_one_pos ν A L hA hL hb w g
  unfold expectation
  rw [moment_gibbs_shift_eq ν ρ A L hL (hb.mono (fun _ hv ↦ hv.2)),
    moment_gibbs_shift_eq ν (fun _ ↦ 1) A L hL (hb.mono (fun _ hv ↦ hv.2))]
  field_simp

theorem nestedIntegrandDerivative_apply_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w d : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    nestedIntegrandDerivative ν ρ A L p w g d =
      nestedIntegrand ν (fun v ↦ ρ v*A v d) A L p w g+
        (p-1)*nestedIntegrand ν ρ A L p w g*
          (shiftedSpinMoment ν (fun v ↦ A v d) A L w g/
            shiftedSpinMoment ν (fun _ ↦ 1) A L w g) := by
  have hf := hb.mono (fun _ hv ↦ hv.2.2)
  letI := gibbsMeasure_probability ν L hL hf g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  rw [nestedIntegrandDerivative, smul_apply,
    powerObservableDerivative_apply (gibbsMeasure ν L g) ρ A hρ hA hbg]
  unfold nestedIntegrand powerObservable
  rw [← expectation_gibbs_shift_eq ν (fun v ↦ A v d) A L hA hL (hb.mono (fun _ hv ↦ hv.2))]
  simp only [smul_eq_mul]
  ring

theorem nestedIntegrandDerivative_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Continuous (nestedIntegrandDerivative ν ρ A L p w) := by
  classical
  have hf := hb.mono (fun _ hv ↦ hv.2)
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hZ := shiftedSpinMoment_continuous ν (fun _ ↦ 1) A L measurable_const hA hL
    zero_le_one hKA hKL h1 w
  have hcoord (d : EuclideanSpace ℝ κ) :
      Continuous (fun g ↦ nestedIntegrandDerivative ν ρ A L p w g d) := by
    have hm : Measurable (fun v ↦ A v d) :=
      (ContinuousLinearMap.apply ℝ ℝ d).continuous.measurable.comp hA
    have hd : ∀ᵐ v ∂ν, |A v d| ≤ KA*‖d‖ ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
      filter_upwards [hb] with v hv
      exact ⟨((A v).le_opNorm d).trans (mul_le_mul_of_nonneg_right hv.2.1 (norm_nonneg _)),hv.2⟩
    have hρd : ∀ᵐ v ∂ν, |ρ v*A v d| ≤ C*(KA*‖d‖) ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL := by
      filter_upwards [hb,hd] with v hv hvd
      exact ⟨by rw [abs_mul]; exact mul_le_mul hv.1 hvd.1 (abs_nonneg _) hC,hv.2⟩
    have hM := shiftedSpinMoment_continuous ν (fun v ↦ A v d) A L hm hA hL
      (mul_nonneg hKA (norm_nonneg _)) hKA hKL hd w
    have hT := nestedIntegrand_continuous ν (fun v ↦ ρ v*A v d) A L (hρ.mul hm) hA hL
      (mul_nonneg hC (mul_nonneg hKA (norm_nonneg _))) hKA hKL hρd p w
    have heq : (fun g ↦ nestedIntegrandDerivative ν ρ A L p w g d) = (fun g ↦
        nestedIntegrand ν (fun v ↦ ρ v*A v d) A L p w g+
          (p-1)*nestedIntegrand ν ρ A L p w g*
            (shiftedSpinMoment ν (fun v ↦ A v d) A L w g/
              shiftedSpinMoment ν (fun _ ↦ 1) A L w g)) :=
      funext (nestedIntegrandDerivative_apply_eq ν ρ A L hρ hA hL hb p w d)
    rw [heq]
    exact hT.add ((continuous_const.mul
      (nestedIntegrand_continuous ν ρ A L hρ hA hL hC hKA hKL hb p w)).mul
        (hM.div hZ (fun g ↦ (shiftedSpinMoment_one_pos ν A L hA hL hf w g).ne')))
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ κ)
  have heq : nestedIntegrandDerivative ν ρ A L p w = (fun g ↦
      ∑ i, nestedIntegrandDerivative ν ρ A L p w g (b i) • innerSL ℝ (b i)) := by
    funext g
    ext d
    simp only [ContinuousLinearMap.sum_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
    have H := congrArg (fun z ↦ nestedIntegrandDerivative ν ρ A L p w g z) (b.sum_repr' d)
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using H.symm
  rw [heq]
  exact continuous_finset_sum Finset.univ (fun i _ ↦ (hcoord (b i)).smul continuous_const)

theorem nestedIntegrandDerivative_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (nestedIntegrandDerivative ν ρ A L p w) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul
    (((2+|p|)*C*KA)*Real.exp ((|p| *KA)*‖w‖))).mono'
      (nestedIntegrandDerivative_continuous ν ρ A L hρ hA hL hC hKA hKL hb p w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (nestedIntegrandDerivative_norm_le ν ρ A L hρ hA hL hC hKA hb p w)

def nestedNumerator (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∫ g, nestedIntegrand ν ρ A L p w g ∂SYK.standardGaussianMeasureOnEuclidean ι

def nestedNumeratorDerivative (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ →L[ℝ] ℝ :=
  ∫ g, nestedIntegrandDerivative ν ρ A L p w g ∂SYK.standardGaussianMeasureOnEuclidean ι

/-- The actual external Frechet derivative is passed through the common
Gaussian integral with a proved locally uniform integrable power-weight bound. -/
theorem nestedNumerator_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    HasFDerivAt (nestedNumerator ν ρ A L p) (nestedNumeratorDerivative ν ρ A L p w) w := by
  let B := ((2+|p|)*C*KA)*Real.exp ((|p| *KA)*(‖w‖+1))
  have hcoef : 0 ≤ |p| *KA := mul_nonneg (abs_nonneg p) hKA
  have hD : 0 ≤ (2+|p|)*C*KA := mul_nonneg (mul_nonneg (by positivity) hC) hKA
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (E := ℝ) (s := Metric.ball w 1)
    (F := fun z g ↦ nestedIntegrand ν ρ A L p z g)
    (F' := fun z g ↦ nestedIntegrandDerivative ν ρ A L p z g)
    (bound := fun g ↦ B*powerWeight ν L p g) (Metric.ball_mem_nhds w zero_lt_one)
  · exact Filter.Eventually.of_forall (fun z ↦
      (nestedIntegrand_integrable ν ρ A L hρ hA hL hC hKA hKL hb p z).aestronglyMeasurable)
  · exact nestedIntegrand_integrable ν ρ A L hρ hA hL hC hKA hKL hb p w
  · exact (nestedIntegrandDerivative_continuous ν ρ A L hρ hA hL hC hKA hKL hb p w).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun g z hz ↦
      (nestedIntegrandDerivative_norm_le ν ρ A L hρ hA hL hC hKA hb p z g).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (norm_le_of_mem_ball hz) hcoef)) hD)
              (powerWeight_pos ν L p g).le))
  · exact (powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul B
  · exact Filter.Eventually.of_forall (fun g z _ ↦
      nestedIntegrand_hasFDerivAt ν ρ A L hρ hA hL hC hKA hb p z g)

theorem nestedNumeratorDerivative_apply (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w d : EuclideanSpace ℝ κ) :
    nestedNumeratorDerivative ν ρ A L p w d = ∫ g,
      powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w*
        (expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
          (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
            expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w)
              ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  rw [nestedNumeratorDerivative, ContinuousLinearMap.integral_apply
    (nestedIntegrandDerivative_integrable ν ρ A L hρ hA hL hC hKA hKL hb p w)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  change nestedIntegrandDerivative ν ρ A L p w g d =
    powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w*
      (expectation (gibbsMeasure ν L g) (fun v ↦ ρ v*A v d) A w+
        (p-1)*expectation (gibbsMeasure ν L g) ρ A w*
          expectation (gibbsMeasure ν L g) (fun v ↦ A v d) A w)
  rw [nestedIntegrandDerivative, smul_apply,
    powerObservableDerivative_apply (gibbsMeasure ν L g) ρ A hρ hA hbg]
  simp only [smul_eq_mul, powerWeight, mul_assoc]

end
end TensorPCA.GaussianNestedGibbsProofs
