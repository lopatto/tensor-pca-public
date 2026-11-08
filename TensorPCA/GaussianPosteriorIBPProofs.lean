-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPosteriorProofs
public import TensorPCA.GaussianAffineGibbsProofs
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Posterior covariance integration by parts

The extra real Gibbs parameter retains the full squared-signal normalizer.
No constant-norm assumption on the prior signal is used.
-/
@[expose] public section

namespace TensorPCA.GaussianPosteriorIBPProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSpinInterpolation GaussianAffineGibbsProofs
open scoped RealInnerProductSpace

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def augmentedField (F : Omega → E) (x : Omega) : (E × ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (F x)).comp (ContinuousLinearMap.fst ℝ E ℝ) +
    ‖F x‖ ^ 2 • ContinuousLinearMap.snd ℝ E ℝ

theorem augmentedField_apply (F : Omega → E) (x : Omega) (w : E × ℝ) :
    augmentedField F x w = inner ℝ (F x) w.1 + ‖F x‖ ^ 2 * w.2 := by
  simp [augmentedField]

theorem measurable_augmentedField (F : Omega → E) (hF : Measurable F) :
    Measurable (augmentedField F) := by
  have hi : Continuous (fun v : E ↦
      (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ)) :=
    (innerSL ℝ).continuous.clm_comp continuous_const
  exact (hi.measurable.comp hF).add ((hF.norm.pow_const 2).smul measurable_const)

theorem norm_augmentedField_le (F : Omega → E) (x : Omega) :
    ‖augmentedField F x‖ ≤ ‖F x‖ + ‖F x‖ ^ 2 := by
  unfold augmentedField
  apply (norm_add_le ((innerSL ℝ (F x)).comp (ContinuousLinearMap.fst ℝ E ℝ))
    (‖F x‖ ^ 2 • ContinuousLinearMap.snd ℝ E ℝ)).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
      rw [innerSL_apply_norm]
      exact mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ E ℝ))
  · apply (ContinuousLinearMap.opNorm_smul_le (‖F x‖ ^ 2) (ContinuousLinearMap.snd ℝ E ℝ)).trans
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (sq_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E ℝ)

theorem augmentedField_ae_bound (mu : Measure Omega) (F : Omega → E) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ x ∂mu, ‖F x‖ ≤ K) :
    ∀ᵐ x ∂mu, ‖augmentedField F x‖ ≤ K + K ^ 2 := by
  filter_upwards [hb] with x hx
  exact (norm_augmentedField_le F x).trans (add_le_add hx (pow_le_pow_left₀ (norm_nonneg _) hx 2))

theorem moment_augmentedField (mu : Measure Omega) (F : Omega → E) (y : E) :
    GaussianSpinInterpolation.moment mu (fun _ ↦ 1) (augmentedField F) (y, -(1:ℝ)/2) = mixtureLikelihood mu F y := by
  unfold GaussianSpinInterpolation.moment mixtureLikelihood
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [weight, one_mul, augmentedField_apply, mixtureWeight]
    congr 1
    ring

theorem posteriorKernel_eq_augmentedGibbs (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) :
    posteriorKernel mu F y = gibbsMeasure mu (augmentedField F) (y, -(1:ℝ)/2) := by
  rw [posteriorKernel_apply mu F hF, gibbsMeasure]
  congr 1
  funext x
  rw [moment_augmentedField]
  simp only [posteriorWeight, mixtureWeight, augmentedField_apply]
  congr 1
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  congr 1
  ring

theorem posteriorMean_eq_expectation (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂mu, ‖F x‖ ≤ K) (a : Omega → ℝ) (y : E) :
    posteriorMean mu F a y = expectation mu a (augmentedField F) (y, -(1:ℝ)/2) := by
  rw [posteriorMean, posteriorKernel_eq_augmentedGibbs mu F hF]
  exact integral_gibbsMeasure mu (augmentedField F) (measurable_augmentedField F hF)
    (augmentedField_ae_bound mu F hK hb) (y, -(1:ℝ)/2) a

end TensorPCA.GaussianPosteriorIBPProofs
