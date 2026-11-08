-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianNestedGibbsProofs

/-! Normalization and physical response of two-stage Gaussian Gibbs expectations. -/
@[expose] public section
namespace TensorPCA.GaussianNestedExpectationProofs
open MeasureTheory ProbabilityTheory GaussianSpinInterpolation GaussianPowerGibbsProofs GaussianNestedGibbsProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V ι κ : Type*} [MeasurableSpace V] [Fintype ι] [Fintype κ]

theorem nestedNumeratorDerivative_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) : Continuous (nestedNumeratorDerivative ν ρ A L p) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  let B := ((2+|p|)*C*KA)*Real.exp ((|p| *KA)*(‖w‖+1))
  have hcoef : 0 ≤ |p| *KA := mul_nonneg (abs_nonneg p) hKA
  have hD : 0 ≤ (2+|p|)*C*KA := mul_nonneg (mul_nonneg (by positivity) hC) hKA
  apply continuousAt_of_dominated (bound := fun g ↦ B*powerWeight ν L p g)
  · exact Filter.Eventually.of_forall (fun z ↦
      (nestedIntegrandDerivative_integrable ν ρ A L hρ hA hL hC hKA hKL hb p z).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds w zero_lt_one] with z hz
    exact Filter.Eventually.of_forall (fun g ↦
      (nestedIntegrandDerivative_norm_le ν ρ A L hρ hA hL hC hKA hb p z g).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (norm_le_of_mem_ball hz) hcoef)) hD)
              (powerWeight_pos ν L p g).le))
  · exact (powerWeight_integrable ν L hL hKL (hb.mono (fun _ hv ↦ hv.2.2)) p).const_mul B
  · apply Filter.Eventually.of_forall
    intro g
    letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
    have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
      (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
    have hc := (powerObservable_contDiff (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg p).continuous_fderiv
      (by norm_num)
    have heq : (fun z ↦ nestedIntegrandDerivative ν ρ A L p z g) = (fun z ↦
        powerWeight ν L p g • fderiv ℝ (powerObservable (gibbsMeasure ν L g) ρ A p) z) := by
      funext z
      rw [(powerObservable_hasFDerivAt (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg p z).fderiv]
      rfl
    rw [heq]
    exact ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ κ ↦ powerWeight ν L p g)).smul hc).continuousAt

theorem nestedNumerator_contDiff (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    ContDiff ℝ 1 (nestedNumerator ν ρ A L p) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_,
    nestedNumeratorDerivative_continuous ν ρ A L hρ hA hL hC hKA hKL hb p,
    nestedNumerator_hasFDerivAt ν ρ A L hρ hA hL hC hKA hKL hb p⟩

theorem nestedNumerator_one_pos (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    0 < nestedNumerator ν (fun _ ↦ 1) A L p w := by
  have heq : nestedIntegrand ν (fun _ ↦ 1) A L p w = (fun g ↦
      Real.exp (p*Real.log (shiftedSpinMoment ν (fun _ ↦ 1) A L w g))) := by
    funext g
    rw [nestedIntegrand_eq ν (fun _ ↦ 1) A L hA hL hb]
    have hz := shiftedSpinMoment_one_pos ν A L hA hL hb w g
    nth_rw 2 [← Real.exp_log hz]
    rw [← Real.exp_add]
    congr 1
    ring
  have hi := nestedIntegrand_integrable ν (fun _ ↦ 1) A L measurable_const hA hL
    zero_le_one hKA hKL (hb.mono (fun _ hv ↦ ⟨by norm_num,hv⟩)) p w
  unfold nestedNumerator
  rw [heq]
  exact integral_exp_pos (heq ▸ hi)

def nestedExpectation (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : ℝ :=
  nestedNumerator ν ρ A L p w/nestedNumerator ν (fun _ ↦ 1) A L p w

def nestedExpectationDerivative (ν : Measure V) (ρ : V → ℝ)
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : EuclideanSpace ℝ κ →L[ℝ] ℝ :=
  (nestedNumerator ν (fun _ ↦ 1) A L p w)⁻¹ •
    (nestedNumeratorDerivative ν ρ A L p w-
      nestedExpectation ν ρ A L p w • nestedNumeratorDerivative ν (fun _ ↦ 1) A L p w)

theorem nestedExpectation_hasFDerivAt (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    HasFDerivAt (nestedExpectation ν ρ A L p) (nestedExpectationDerivative ν ρ A L p w) w := by
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  have hd := nestedNumerator_hasFDerivAt ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hd1 := nestedNumerator_hasFDerivAt ν (fun _ ↦ 1) A L measurable_const hA hL
    zero_le_one hKA hKL h1 p w
  have hinv := (hasDerivAt_inv hz.ne').comp_hasFDerivAt w hd1
  convert hd.mul hinv using 1
  · funext z
    simp only [nestedExpectation, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
  · ext d
    simp only [nestedExpectationDerivative, nestedExpectation, add_apply, sub_apply,
      smul_apply, smul_eq_mul, Function.comp_apply]
    field_simp
    ring

theorem nestedExpectation_contDiff (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL) (p : ℝ) :
    ContDiff ℝ 1 (nestedExpectation ν ρ A L p) := by
  exact (nestedNumerator_contDiff ν ρ A L hρ hA hL hC hKA hKL hb p).div
    (nestedNumerator_contDiff ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
      (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p)
    (fun w ↦ (nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w).ne')

theorem powerWeightDerivative_norm_le_weight (μ : Measure V) [IsProbabilityMeasure μ]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (hA : Measurable A) {KA : ℝ}
    (hKA : 0 ≤ KA) (hb : ∀ᵐ v ∂μ, ‖A v‖ ≤ KA) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖powerWeightDerivative μ A p w‖ ≤ (|p| *KA)*powerWeight μ A p w := by
  rw [powerWeightDerivative, norm_smul, norm_smul,
    Real.norm_of_nonneg (powerWeight_pos μ A p w).le, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (norm_score_le μ A hA hKA hb w) (abs_nonneg p))
      (powerWeight_pos μ A p w).le).trans_eq (mul_comm _ _)

theorem powerObservableDerivative_norm_le_weight (μ : Measure V) [IsProbabilityMeasure μ]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) {C KA : ℝ} (hC : 0 ≤ C) (hKA : 0 ≤ KA)
    (hb : ∀ᵐ v ∂μ, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA) (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖powerObservableDerivative μ ρ A p w‖ ≤ ((2+|p|)*C*KA)*powerWeight μ A p w := by
  have he := norm_expectation_le μ ρ A hρ hA hC hb w
  have hed := norm_expectationDerivative_le μ ρ A hρ hA hC hKA hb w
  have hwd := powerWeightDerivative_norm_le_weight μ A hA hKA (hb.mono (fun _ hv ↦ hv.2)) p w
  calc
    _ ≤ ‖powerWeight μ A p w • expectationDerivative μ ρ A w‖+
        ‖expectation μ ρ A w • powerWeightDerivative μ A p w‖ := norm_add_le _ _
    _ = powerWeight μ A p w*‖expectationDerivative μ ρ A w‖+
        ‖expectation μ ρ A w‖*‖powerWeightDerivative μ A p w‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (powerWeight_pos μ A p w).le]
    _ ≤ powerWeight μ A p w*(2*C*KA)+C*((|p| *KA)*powerWeight μ A p w) :=
      add_le_add (mul_le_mul_of_nonneg_left hed (powerWeight_pos μ A p w).le)
        (mul_le_mul he hwd (norm_nonneg _) hC)
    _ = _ := by ring

theorem nestedIntegrand_one_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : Measurable A) (hL : Measurable L) {KA KL : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    nestedIntegrand ν (fun _ ↦ 1) A L p w g =
      powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2)) g
  have hAg : ∀ᵐ v ∂gibbsMeasure ν L g, ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ hv.1))
  have h1 : expectation (gibbsMeasure ν L g) (fun _ ↦ 1) A w = 1 := by
    unfold expectation
    exact div_self (moment_one_pos (gibbsMeasure ν L g) A hA hAg w).ne'
  simp only [nestedIntegrand, powerObservable, h1, mul_one]

theorem nestedIntegrand_norm_le_one (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖nestedIntegrand ν ρ A L p w g‖ ≤ C*nestedIntegrand ν (fun _ ↦ 1) A L p w g := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  rw [nestedIntegrand_one_eq ν A L hA hL (hb.mono (fun _ hv ↦ hv.2))]
  calc
    _ = (powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w)*
        ‖expectation (gibbsMeasure ν L g) ρ A w‖ := by
      rw [nestedIntegrand, powerObservable, norm_mul, norm_mul,
        Real.norm_of_nonneg (powerWeight_pos ν L p g).le,
        Real.norm_of_nonneg (powerWeight_pos (gibbsMeasure ν L g) A p w).le]
      ring
    _ ≤ (powerWeight ν L p g*powerWeight (gibbsMeasure ν L g) A p w)*C :=
      mul_le_mul_of_nonneg_left (norm_expectation_le (gibbsMeasure ν L g) ρ A hρ hA hC hbg w)
        (mul_pos (powerWeight_pos ν L p g) (powerWeight_pos (gibbsMeasure ν L g) A p w)).le
    _ = _ := mul_comm _ _

theorem nestedIntegrandDerivative_norm_le_one (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) (g : EuclideanSpace ℝ ι) :
    ‖nestedIntegrandDerivative ν ρ A L p w g‖ ≤
      ((2+|p|)*C*KA)*nestedIntegrand ν (fun _ ↦ 1) A L p w g := by
  letI := gibbsMeasure_probability ν L hL (hb.mono (fun _ hv ↦ hv.2.2)) g
  have hbg : ∀ᵐ v ∂gibbsMeasure ν L g, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA :=
    (gibbsMeasure_absolutelyContinuous ν L g).ae_le (hb.mono (fun _ hv ↦ ⟨hv.1,hv.2.1⟩))
  rw [nestedIntegrand_one_eq ν A L hA hL (hb.mono (fun _ hv ↦ hv.2)),
    nestedIntegrandDerivative, norm_smul, Real.norm_of_nonneg (powerWeight_pos ν L p g).le]
  exact (mul_le_mul_of_nonneg_left
    (powerObservableDerivative_norm_le_weight (gibbsMeasure ν L g) ρ A hρ hA hC hKA hbg p w)
      (powerWeight_pos ν L p g).le).trans_eq (by ring)

theorem nestedNumerator_norm_le_one (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖nestedNumerator ν ρ A L p w‖ ≤ C*nestedNumerator ν (fun _ ↦ 1) A L p w := by
  have hi := nestedIntegrand_integrable ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hi1 := nestedIntegrand_integrable ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p w
  calc
    _ ≤ ∫ g, ‖nestedIntegrand ν ρ A L p w g‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g, C*nestedIntegrand ν (fun _ ↦ 1) A L p w g ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      integral_mono_ae hi.norm (hi1.const_mul C)
        (Filter.Eventually.of_forall (nestedIntegrand_norm_le_one ν ρ A L hρ hA hL hC hb p w))
    _ = _ := integral_const_mul _ _

theorem nestedNumeratorDerivative_norm_le_one (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖nestedNumeratorDerivative ν ρ A L p w‖ ≤
      ((2+|p|)*C*KA)*nestedNumerator ν (fun _ ↦ 1) A L p w := by
  have hi := nestedIntegrandDerivative_integrable ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hi1 := nestedIntegrand_integrable ν (fun _ ↦ 1) A L measurable_const hA hL zero_le_one hKA hKL
    (hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)) p w
  calc
    _ ≤ ∫ g, ‖nestedIntegrandDerivative ν ρ A L p w g‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g, ((2+|p|)*C*KA)*nestedIntegrand ν (fun _ ↦ 1) A L p w g
        ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      integral_mono_ae hi.norm (hi1.const_mul _)
        (Filter.Eventually.of_forall (nestedIntegrandDerivative_norm_le_one ν ρ A L hρ hA hL hC hKA hb p w))
    _ = _ := integral_const_mul _ _

theorem nestedExpectation_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) : ‖nestedExpectation ν ρ A L p w‖ ≤ C := by
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  rw [nestedExpectation, norm_div, Real.norm_of_nonneg hz.le]
  exact (div_le_iff₀ hz).mpr (nestedNumerator_norm_le_one ν ρ A L hρ hA hL hC hKA hKL hb p w)

theorem nestedExpectationDerivative_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (w : EuclideanSpace ℝ κ) :
    ‖nestedExpectationDerivative ν ρ A L p w‖ ≤ 2*(2+|p|)*C*KA := by
  have h1 : ∀ᵐ v ∂ν, |(1 : ℝ)| ≤ 1 ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL :=
    hb.mono (fun _ hv ↦ ⟨by norm_num,hv.2⟩)
  have hz := nestedNumerator_one_pos ν A L hA hL hKA hKL (hb.mono (fun _ hv ↦ hv.2)) p w
  have he := nestedExpectation_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hd := nestedNumeratorDerivative_norm_le_one ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hd1 : ‖nestedNumeratorDerivative ν (fun _ ↦ 1) A L p w‖ ≤
      ((2+|p|)*KA)*nestedNumerator ν (fun _ ↦ 1) A L p w := by
    simpa only [mul_one] using nestedNumeratorDerivative_norm_le_one ν (fun _ ↦ 1) A L
      measurable_const hA hL zero_le_one hKA hKL h1 p w
  rw [nestedExpectationDerivative, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
  calc
    _ ≤ (nestedNumerator ν (fun _ ↦ 1) A L p w)⁻¹ *
        (‖nestedNumeratorDerivative ν ρ A L p w‖+
          ‖nestedExpectation ν ρ A L p w • nestedNumeratorDerivative ν (fun _ ↦ 1) A L p w‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hz.le)
    _ = (nestedNumerator ν (fun _ ↦ 1) A L p w)⁻¹ *
        (‖nestedNumeratorDerivative ν ρ A L p w‖+
          ‖nestedExpectation ν ρ A L p w‖*‖nestedNumeratorDerivative ν (fun _ ↦ 1) A L p w‖) := by
      rw [norm_smul]
    _ ≤ (nestedNumerator ν (fun _ ↦ 1) A L p w)⁻¹ *
        (((2+|p|)*C*KA)*nestedNumerator ν (fun _ ↦ 1) A L p w+
          C*(((2+|p|)*KA)*nestedNumerator ν (fun _ ↦ 1) A L p w)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd (mul_le_mul he hd1 (norm_nonneg _) hC))
        (inv_nonneg.mpr hz.le)
    _ = _ := by field_simp <;> ring

/-- Physical-noise integration by parts for the normalized nested expectation. Its C1 regularity and uniform value/gradient bounds are proved. -/
theorem gaussian_nested_expectation_ibp (ν : Measure V) [IsProbabilityMeasure ν]
    (ρ : V → ℝ) (A : V → EuclideanSpace ℝ κ →L[ℝ] ℝ)
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hA : Measurable A) (hL : Measurable L) {C KA KL : ℝ}
    (hC : 0 ≤ C) (hKA : 0 ≤ KA) (hKL : 0 ≤ KL)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖A v‖ ≤ KA ∧ ‖L v‖ ≤ KL)
    (p : ℝ) (d : EuclideanSpace ℝ κ) :
    (∫ w, inner ℝ d w*nestedExpectation ν ρ A L p w
      ∂SYK.standardGaussianMeasureOnEuclidean κ) =
        ∫ w, nestedExpectationDerivative ν ρ A L p w d
          ∂SYK.standardGaussianMeasureOnEuclidean κ := by
  let B := max C (2*(2+|p|)*C*KA)
  have hd (w : EuclideanSpace ℝ κ) := nestedExpectation_hasFDerivAt ν ρ A L hρ hA hL hC hKA hKL hb p w
  have hval (w : EuclideanSpace ℝ κ) :
      |nestedExpectation ν ρ A L p w| ≤ B*Real.exp (0*‖w‖) := by
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact (nestedExpectation_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p w).trans (le_max_left _ _)
  have hgrad (w : EuclideanSpace ℝ κ) :
      ‖gradient (nestedExpectation ν ρ A L p) w‖ ≤ B*Real.exp (0*‖w‖) := by
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [gradient, (hd w).fderiv, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ κ)).symm.norm_map]
    exact (nestedExpectationDerivative_norm_le ν ρ A L hρ hA hL hC hKA hKL hb p w).trans (le_max_right _ _)
  have H := SYK.gaussian_ibp (nestedExpectation ν ρ A L p) d
    (nestedExpectation_contDiff ν ρ A L hρ hA hL hC hKA hKL hb p) B 0 hval hgrad
  rw [H]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w ↦ by
    change inner ℝ d (gradient (nestedExpectation ν ρ A L p) w) =
      nestedExpectationDerivative ν ρ A L p w d
    rw [real_inner_comm, gradient, (hd w).fderiv, InnerProductSpace.toDual_symm_apply])

end
end TensorPCA.GaussianNestedExpectationProofs
