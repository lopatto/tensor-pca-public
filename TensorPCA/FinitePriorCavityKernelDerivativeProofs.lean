-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityComparisonProofs

/-! Bayesian interpolation derivative expressed as a posterior cross-kernel. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityKernelDerivativeProofs
open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs GaussianSideChannelProofs
open GaussianTwoChannelFreeEnergyProofs GaussianReplicaTransportProofs GaussianReplicaMomentProofs
open GaussianPosteriorCovarianceProofs FinitePriorCavityComparisonProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega iota kappa : Type*} [MeasurableSpace Omega] [Fintype iota] [Fintype kappa]
    [DecidableEq iota] [DecidableEq kappa]

def kernelDifference (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (p : Omega × Omega) : ℝ := inner ℝ (A p.1) (A p.2)-inner ℝ (B p.1) (B p.2)

def interpolatedSignal (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa) (t : ℝ) :=
  joinedSignal (fun x ↦ Real.sqrt t • A x) (fun x ↦ Real.sqrt (1-t) • B x)

theorem measurable_interpolatedSignal (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) (t : ℝ) : Measurable (interpolatedSignal A B t) :=
  measurable_joinedSignal _ _ ((continuous_const_smul (Real.sqrt t)).measurable.comp hA)
    ((continuous_const_smul (Real.sqrt (1-t))).measurable.comp hB)

theorem interpolatedSignal_norm_le (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Omega) : ‖interpolatedSignal A B t x‖ ≤ CA+CB := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hCA hCB)).mp
  change ‖GaussianCompactFeatureComparison.sumJoin (Real.sqrt t • A x,Real.sqrt (1-t) • B x)‖^2 ≤ _
  rw [norm_sumJoin_sq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs,
    Real.sq_sqrt ht.1,Real.sq_sqrt (sub_nonneg.mpr ht.2)]
  have hA2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbA x) 2) ht.1
  have hB2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbB x) 2) (sub_nonneg.mpr ht.2)
  have hAT := mul_le_of_le_one_left (sq_nonneg CA) ht.2
  have hBT := mul_le_of_le_one_left (sq_nonneg CB) (by linarith [ht.1] : 1-t ≤ 1)
  nlinarith only [hA2,hB2,hAT,hBT,mul_nonneg hCA hCB]

theorem posteriorMean_norm_sq_integrable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → EuclideanSpace ℝ (iota ⊕ kappa)) (hF : Measurable F)
    (C : Omega → V) (hC : StronglyMeasurable C) {K : ℝ} (hbC : ∀ x, ‖C x‖ ≤ K) :
    Integrable (fun y ↦ ‖posteriorMean mu F C y‖^2) (mixtureLaw mu F) := by
  letI := mixtureLaw_probability mu F hF
  apply Integrable.of_bound ((stronglyMeasurable_posteriorMean mu F C hC).norm.pow 2).aestronglyMeasurable (K^2)
  apply Filter.Eventually.of_forall
  intro y
  change ‖‖posteriorMean mu F C y‖^2‖ ≤ K^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_posteriorMean_le mu F hF C (Filter.Eventually.of_forall hbC) y) 2

theorem posterior_kernel_difference (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → EuclideanSpace ℝ (iota ⊕ kappa)) (hF : Measurable F)
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB)
    (y : EuclideanSpace ℝ (iota ⊕ kappa)) :
    ‖posteriorMean mu F A y‖^2-‖posteriorMean mu F B y‖^2 =
      ∫ p, kernelDifference A B p ∂(posteriorKernel mu F y).prod (posteriorKernel mu F y) := by
  letI := posteriorKernel_isMarkov mu F hF
  unfold posteriorMean
  rw [norm_integral_sq_eq_replicaInner _ A hA (Filter.Eventually.of_forall hbA),
    norm_integral_sq_eq_replicaInner _ B hB (Filter.Eventually.of_forall hbB),
    ← integral_sub (replicaInner_integrable _ A hA (Filter.Eventually.of_forall hbA))
      (replicaInner_integrable _ B hB (Filter.Eventually.of_forall hbB))]
  rfl

theorem guerraPath_hasDerivAt_kernel [StandardBorelSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hbA : ∀ x, ‖A x‖ ≤ CA) (hbB : ∀ x, ‖B x‖ ≤ CB)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun u ↦ twoChannelFreeEnergy mu (fun x ↦ Real.sqrt u • A x) (fun x ↦ Real.sqrt (1-u) • B x))
      ((1/2 : ℝ)*∫ y, ∫ p, kernelDifference A B p
        ∂(posteriorKernel mu (interpolatedSignal A B t) y).prod (posteriorKernel mu (interpolatedSignal A B t) y)
        ∂mixtureLaw mu (interpolatedSignal A B t)) t := by
  let At := fun x ↦ Real.sqrt t • A x
  let Bt := fun x ↦ Real.sqrt (1-t) • B x
  have hAt : Measurable At := (continuous_const_smul (Real.sqrt t)).measurable.comp hA
  have hBt : Measurable Bt := (continuous_const_smul (Real.sqrt (1-t))).measurable.comp hB
  have H := hasDerivAt_guerraPath_commonPosterior mu A B hA hB hCA hCB
    (Filter.Eventually.of_forall hbA) (Filter.Eventually.of_forall hbB) ht0 ht1
  rw [combinedMean_secondMoment_join mu At Bt hAt hBt A hA.stronglyMeasurable,
    combinedMean_secondMoment_join mu At Bt hAt hBt B hB.stronglyMeasurable] at H
  have hiA := posteriorMean_norm_sq_integrable mu (interpolatedSignal A B t)
    (measurable_interpolatedSignal A B hA hB t) A hA.stronglyMeasurable hbA
  have hiB := posteriorMean_norm_sq_integrable mu (interpolatedSignal A B t)
    (measurable_interpolatedSignal A B hA hB t) B hB.stronglyMeasurable hbB
  have hEq : ((∫ y, ‖posteriorMean mu (interpolatedSignal A B t) A y‖^2 ∂mixtureLaw mu (interpolatedSignal A B t))-
      ∫ y, ‖posteriorMean mu (interpolatedSignal A B t) B y‖^2 ∂mixtureLaw mu (interpolatedSignal A B t)) =
      ∫ y, ∫ p, kernelDifference A B p
        ∂(posteriorKernel mu (interpolatedSignal A B t) y).prod (posteriorKernel mu (interpolatedSignal A B t) y)
        ∂mixtureLaw mu (interpolatedSignal A B t) := by
    rw [← integral_sub hiA hiB]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (posterior_kernel_difference mu (interpolatedSignal A B t)
      (measurable_interpolatedSignal A B hA hB t) A B hA hB hbA hbB)
  convert H using 1
  rw [← hEq]
  dsimp only [interpolatedSignal,At,Bt]
  ring

end
end TensorPCA.FinitePriorCavityKernelDerivativeProofs
