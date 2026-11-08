-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianNestedSwapProofs

/-! Angular interpolation of the physical and common Gaussian fields. -/
@[expose] public section
namespace TensorPCA.GaussianAngularPressureProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs
open GaussianNestedGibbsProofs GaussianNestedExpectationProofs GaussianNestedTiltProofs GaussianNestedSwapProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

def anglePoint (theta : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Real.cos theta • EuclideanSpace.single 0 1+Real.sin theta • EuclideanSpace.single 1 1

def angleTangent (theta : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  -Real.sin theta • EuclideanSpace.single 0 1+Real.cos theta • EuclideanSpace.single 1 1

theorem anglePoint_hasDerivAt (theta : ℝ) : HasDerivAt anglePoint (angleTangent theta) theta :=
  ((Real.hasDerivAt_cos theta).smul_const (EuclideanSpace.single 0 1)).add
    ((Real.hasDerivAt_sin theta).smul_const (EuclideanSpace.single 1 1))

theorem two_coordinate_norm_le (a b : ℝ) :
    ‖a • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))+
      b • EuclideanSpace.single 1 1‖ ≤ |a|+|b| := by
  calc
    _ ≤ ‖a • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖+
        ‖b • EuclideanSpace.single 1 1‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul]

theorem anglePoint_norm_le (theta : ℝ) : ‖anglePoint theta‖ ≤ 2 := by
  exact (two_coordinate_norm_le _ _).trans (by linarith [Real.abs_cos_le_one theta, Real.abs_sin_le_one theta])

theorem angleTangent_norm_le (theta : ℝ) : ‖angleTangent theta‖ ≤ 2 := by
  exact (two_coordinate_norm_le _ _).trans (by
    rw [abs_neg]
    linarith [Real.abs_cos_le_one theta, Real.abs_sin_le_one theta])

def angleLinear
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  A v w • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0+
    L v g • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1

theorem angleLinear_apply
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) (z : EuclideanSpace ℝ (Fin 2)) :
    angleLinear A L w g v z = A v w*z 0+L v g*z 1 := rfl

theorem angleLinear_measurable
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    Measurable (angleLinear A L w g) := by
  exact (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hA).smul measurable_const).add
    (((ContinuousLinearMap.apply ℝ ℝ g).continuous.measurable.comp hL).smul measurable_const)

theorem angleLinear_bound (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ∀ᵐ v ∂ν, ‖angleLinear A L w g v‖ ≤ KA*‖w‖+KL*‖g‖ := by
  filter_upwards [hb] with v hv
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg
    (mul_nonneg hKA (norm_nonneg _)) (mul_nonneg hKL (norm_nonneg _)))
  intro z
  rw [Real.norm_eq_abs, angleLinear_apply]
  have haw : |A v w| ≤ KA*‖w‖ :=
    ((A v).le_opNorm w).trans (mul_le_mul_of_nonneg_right hv.1 (norm_nonneg _))
  have hlg : |L v g| ≤ KL*‖g‖ :=
    ((L v).le_opNorm g).trans (mul_le_mul_of_nonneg_right hv.2 (norm_nonneg _))
  calc
    _ ≤ |A v w*z 0|+|L v g*z 1| := abs_add_le _ _
    _ = |A v w| *|z 0|+|L v g| *|z 1| := by rw [abs_mul,abs_mul]
    _ ≤ (KA*‖w‖)*‖z‖+(KL*‖g‖)*‖z‖ := add_le_add
      (mul_le_mul haw (PiLp.norm_apply_le z 0) (abs_nonneg _) (mul_nonneg hKA (norm_nonneg _)))
      (mul_le_mul hlg (PiLp.norm_apply_le z 1) (abs_nonneg _) (mul_nonneg hKL (norm_nonneg _)))
    _ = _ := by ring

theorem angleLinear_anglePoint
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) (theta : ℝ) :
    angleLinear A L w g v (anglePoint theta) = Real.cos theta*A v w+Real.sin theta*L v g := by
  rw [angleLinear_apply]
  simp [anglePoint, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply] <;> ring

theorem angleLinear_angleTangent
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) (theta : ℝ) :
    angleLinear A L w g v (angleTangent theta) = -Real.sin theta*A v w+Real.cos theta*L v g := by
  rw [angleLinear_apply]
  simp [angleTangent, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply] <;> ring

def angularPower (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  powerWeight ν (angleLinear A L w g) p (anglePoint theta)

def angularPowerDerivative (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) : ℝ :=
  powerWeightDerivative ν (angleLinear A L w g) p (anglePoint theta) (angleTangent theta)

theorem angularPower_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t ↦ angularPower ν A L p t w g) (angularPowerDerivative ν A L p theta w g) theta := by
  exact (powerWeight_hasFDerivAt ν (angleLinear A L w g) (angleLinear_measurable A L hA hL w g)
    (add_nonneg (mul_nonneg hKA (norm_nonneg _)) (mul_nonneg hKL (norm_nonneg _)))
      (angleLinear_bound ν A L hKA hKL hb w g) p (anglePoint theta)).comp_hasDerivAt theta
        (anglePoint_hasDerivAt theta)

theorem angularMoment_eq_shift (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    moment ν ρ (angleLinear A L w g) (anglePoint theta) =
      shiftedSpinMoment ν ρ A L (Real.cos theta • w) (Real.sin theta • g) := by
  unfold shiftedSpinMoment GaussianSpinInterpolation.moment weight
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v ↦ by
    change ρ v*Real.exp (angleLinear A L w g v (anglePoint theta)) =
      (ρ v*Real.exp (A v (Real.cos theta • w)))*Real.exp (L v (Real.sin theta • g))
    rw [angleLinear_anglePoint]
    simp only [map_smul, smul_eq_mul, Real.exp_add]
    ring)

theorem angularPower_eq_nested (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta w g =
      nestedIntegrand ν (fun _ ↦ 1) A L p (Real.cos theta • w) (Real.sin theta • g) := by
  rw [nestedIntegrand_one_exp ν A L hA hL hb]
  unfold angularPower powerWeight logPartition
  rw [angularMoment_eq_shift]

theorem angularPower_factor (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPower ν A L p theta w g = powerWeight ν A p (Real.cos theta • w)*
      powerWeight (gibbsMeasure ν A (Real.cos theta • w)) L p (Real.sin theta • g) := by
  rw [angularPower_eq_nested ν A L hA hL hb, nestedIntegrand_one_factor ν A L hA hL hb]

theorem angularExpectation_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    expectation ν ρ (angleLinear A L w g) (anglePoint theta) =
      expectation (gibbsMeasure ν A (Real.cos theta • w)) ρ L (Real.sin theta • g) := by
  rw [expectation_gibbs_shift_eq ν ρ L A hL hA (hb.mono (fun _ hv ↦ hv.symm)),
    shiftedSpinMoment_swap ν ρ L A, shiftedSpinMoment_swap ν (fun _ ↦ 1) L A]
  unfold expectation
  rw [angularMoment_eq_shift, angularMoment_eq_shift]

theorem angularPower_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : Continuous (angularPower ν A L p theta w) := by
  have heq : angularPower ν A L p theta w = (fun g ↦
      nestedIntegrand ν (fun _ ↦ 1) A L p (Real.cos theta • w) (Real.sin theta • g)) :=
    funext (angularPower_eq_nested ν A L hA hL hb p theta w)
  rw [heq]
  exact (nestedIntegrand_continuous ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv⟩)) p (Real.cos theta • w)).comp (continuous_const_smul _)

theorem angleLinear_single_zero
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) :
    angleLinear A L w g v (EuclideanSpace.single 0 1) = A v w := by rw [angleLinear_apply]; simp

theorem angleLinear_single_one
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) (v : V) :
    angleLinear A L w g v (EuclideanSpace.single 1 1) = L v g := by rw [angleLinear_apply]; simp

theorem angleTangent_zero (theta : ℝ) : angleTangent theta 0 = -Real.sin theta := by
  simp [angleTangent, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]

theorem angleTangent_one (theta : ℝ) : angleTangent theta 1 = Real.cos theta := by
  simp [angleTangent, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]

theorem angularPowerDerivative_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    angularPowerDerivative ν A L p theta w g = p*angularPower ν A L p theta w g*
      (-Real.sin theta*expectation (gibbsMeasure ν A (Real.cos theta • w))
        (fun v ↦ A v w) L (Real.sin theta • g)+
        Real.cos theta*score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g) := by
  letI := gibbsMeasure_probability ν A hA (hb.mono (fun _ hv ↦ hv.1)) (Real.cos theta • w)
  have hLg := (gibbsMeasure_absolutelyContinuous ν A (Real.cos theta • w)).ae_le
    (hb.mono (fun _ hv ↦ hv.2))
  rw [angularPowerDerivative, powerWeightDerivative, smul_apply, smul_apply,
    score_eq_coordinate_sum ν (angleLinear A L w g) (angleLinear_measurable A L hA hL w g)
      (angleLinear_bound ν A L hKA hKL hb w g)]
  simp only [Fin.sum_univ_two, angleTangent_zero, angleTangent_one,
    angleLinear_single_zero, angleLinear_single_one, smul_eq_mul]
  rw [angularExpectation_eq ν (fun v ↦ A v w) A L hA hL hb,
    angularExpectation_eq ν (fun v ↦ L v g) A L hA hL hb,
    ← score_apply (gibbsMeasure ν A (Real.cos theta • w)) L hL hLg]
  unfold angularPower
  ring

theorem angularPowerDerivative_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : Continuous (angularPowerDerivative ν A L p theta w) := by
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
  have heq : angularPowerDerivative ν A L p theta w = (fun g ↦ p*angularPower ν A L p theta w g*
      (-Real.sin theta*expectation (gibbsMeasure ν A (Real.cos theta • w)) (fun v ↦ A v w) L (Real.sin theta • g)+
        Real.cos theta*score (gibbsMeasure ν A (Real.cos theta • w)) L (Real.sin theta • g) g)) :=
    funext (angularPowerDerivative_eq ν A L hA hL hKA hKL hb p theta w)
  rw [heq]
  exact (continuous_const.mul (angularPower_continuous ν A L hA hL hKA hKL hb p theta w)).mul
    ((continuous_const.mul hE).add (continuous_const.mul hS))

theorem angularPower_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖angularPower ν A L p theta w g‖ ≤ Real.exp ((2*|p|)*(KA*‖w‖+KL*‖g‖)) := by
  have hn : 0 ≤ angularPower ν A L p theta w g :=
    (powerWeight_pos ν (angleLinear A L w g) p (anglePoint theta)).le
  rw [Real.norm_of_nonneg hn]
  have hK : 0 ≤ KA*‖w‖+KL*‖g‖ := add_nonneg (mul_nonneg hKA (norm_nonneg _))
    (mul_nonneg hKL (norm_nonneg _))
  exact (powerWeight_le_exp_norm ν (angleLinear A L w g) (angleLinear_measurable A L hA hL w g)
    (angleLinear_bound ν A L hKA hKL hb w g) p (anglePoint theta)).trans
      (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (anglePoint_norm_le theta)
        (mul_nonneg (abs_nonneg p) hK)).trans_eq (by ring)))

theorem angularPowerDerivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖angularPowerDerivative ν A L p theta w g‖ ≤
      (2*|p|)*(KA*‖w‖+KL*‖g‖)*Real.exp ((2*|p|)*(KA*‖w‖+KL*‖g‖)) := by
  have hK : 0 ≤ KA*‖w‖+KL*‖g‖ := add_nonneg (mul_nonneg hKA (norm_nonneg _))
    (mul_nonneg hKL (norm_nonneg _))
  have hd := powerWeightDerivative_norm_le_weight ν (angleLinear A L w g)
    (angleLinear_measurable A L hA hL w g) hK (angleLinear_bound ν A L hKA hKL hb w g) p (anglePoint theta)
  have hn : 0 ≤ angularPower ν A L p theta w g :=
    (powerWeight_pos ν (angleLinear A L w g) p (anglePoint theta)).le
  calc
    _ ≤ ‖powerWeightDerivative ν (angleLinear A L w g) p (anglePoint theta)‖*‖angleTangent theta‖ :=
      (powerWeightDerivative ν (angleLinear A L w g) p (anglePoint theta)).le_opNorm _
    _ ≤ ((|p| *(KA*‖w‖+KL*‖g‖))*angularPower ν A L p theta w g)*2 :=
      mul_le_mul hd (angleTangent_norm_le theta) (norm_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg p) hK) hn)
    _ = ((2*|p|)*(KA*‖w‖+KL*‖g‖))*‖angularPower ν A L p theta w g‖ := by
      rw [Real.norm_of_nonneg hn]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (angularPower_norm_le ν A L hA hL hKA hKL hb p theta w g)
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg p)) hK)

theorem affine_exp_bound {q x c r : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    q*(x+c*r)*Real.exp (q*(x+c*r)) ≤
      (q*(x+c)*Real.exp (q*x))*Real.exp ((q*c+1)*r) := by
  have he1 : 1 ≤ Real.exp r := Real.one_le_exp_iff.mpr hr
  have her : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hlin : x+c*r ≤ (x+c)*Real.exp r := by
    nlinarith [mul_le_mul_of_nonneg_left he1 hx, mul_le_mul_of_nonneg_left her hc]
  have he : Real.exp r*Real.exp (q*(x+c*r)) = Real.exp (q*x)*Real.exp ((q*c+1)*r) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ q*((x+c)*Real.exp r)*Real.exp (q*(x+c*r)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hq) (Real.exp_pos _).le
    _ = (q*(x+c))*(Real.exp r*Real.exp (q*(x+c*r))) := by ring
    _ = _ := by rw [he]; ring

theorem angularPower_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    Integrable (angularPower ν A L p theta w) (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((SYK.integrable_exp_mul_norm ((2*|p|)*KL)).const_mul
    (Real.exp ((2*|p|)*(KA*‖w‖)))).mono'
      (angularPower_continuous ν A L hA hL hKA hKL hb p theta w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun g ↦
    (angularPower_norm_le ν A L hA hL hKA hKL hb p theta w g).trans_eq (by
      rw [← Real.exp_add]
      congr 1
      ring))

def angularNormalizer (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∫ g, angularPower ν A L p theta w g ∂SYK.standardGaussianMeasureOnEuclidean ι

def angularNormalizerDerivative (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  ∫ g, angularPowerDerivative ν A L p theta w g ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem angularNormalizer_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    HasDerivAt (fun t ↦ angularNormalizer ν A L p t w)
      (angularNormalizerDerivative ν A L p theta w) theta := by
  let q := 2*|p|
  let B := q*(KA*‖w‖+KL)*Real.exp (q*(KA*‖w‖))
  have hq : 0 ≤ q := mul_nonneg (by norm_num) (abs_nonneg p)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean ι) (s := Set.univ)
    (F := fun t g ↦ angularPower ν A L p t w g)
    (F' := fun t g ↦ angularPowerDerivative ν A L p t w g)
    (bound := fun g ↦ B*Real.exp ((q*KL+1)*‖g‖)) (by simp)
    (Filter.Eventually.of_forall (fun t ↦
      (angularPower_integrable ν A L hA hL hKA hKL hb p t w).aestronglyMeasurable))
    (angularPower_integrable ν A L hA hL hKA hKL hb p theta w)
    (angularPowerDerivative_continuous ν A L hA hL hKA hKL hb p theta w).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g t _ ↦
      (angularPowerDerivative_norm_le ν A L hA hL hKA hKL hb p t w g).trans
        (affine_exp_bound hq (mul_nonneg hKA (norm_nonneg w)) hKL (norm_nonneg g))))
    ((SYK.integrable_exp_mul_norm (q*KL+1)).const_mul B)
    (Filter.Eventually.of_forall (fun g t _ ↦ angularPower_hasDerivAt ν A L hA hL hKA hKL hb p t w g))).2

theorem angularNormalizer_pos (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : 0 < angularNormalizer ν A L p theta w :=
  integral_exp_pos (angularPower_integrable ν A L hA hL hKA hKL hb p theta w)

def angularLogPressure (ν : Measure V)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) : ℝ := Real.log (angularNormalizer ν A L p theta w)/p

theorem angularLogPressure_hasDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ} (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p theta : ℝ) (w : EuclideanSpace ℝ κ) :
    HasDerivAt (fun t ↦ angularLogPressure ν A L p t w)
      (angularNormalizerDerivative ν A L p theta w/(p*angularNormalizer ν A L p theta w)) theta := by
  have H := ((angularNormalizer_hasDerivAt ν A L hA hL hKA hKL hb p theta w).log
    (angularNormalizer_pos ν A L hA hL hKA hKL hb p theta w).ne').div_const p
  convert H using 1
  · rfl
  · simp only [div_div]
    rw [mul_comm]

end
end TensorPCA.GaussianAngularPressureProofs
