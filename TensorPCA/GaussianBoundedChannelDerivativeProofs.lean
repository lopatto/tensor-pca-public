-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianPosteriorCovarianceProofs
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Differentiation of a bounded nonunit Gaussian channel

The planted log likelihood retains the variable squared-signal penalty.
This is the finite-prior calculus used by tensor-plus-scalar interpolation.
-/
@[expose] public section

namespace TensorPCA.GaussianBoundedChannelDerivativeProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianMixtureStabilityProofs
open GaussianSpinInterpolation GaussianPosteriorIBPProofs GaussianPosteriorCovarianceProofs
open scoped RealInnerProductSpace Topology

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def plantedInput (lam : ℝ) (v w : E) : E × ℝ :=
  (lam^2 • v + lam • w, -(lam^2)/2)

noncomputable def plantedInputDerivative (lam : ℝ) (v w : E) : E × ℝ :=
  ((2*lam) • v+w, -lam)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_plantedInput_le (lam : ℝ) (v w : E) :
    ‖plantedInput lam v w‖ ≤ lam^2*‖v‖ + |lam| *‖w‖ + lam^2/2 := by
  rw [plantedInput, Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖lam^2 • v‖ + ‖lam • w‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lam)]
        linarith [sq_nonneg lam]
  · simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (sq_nonneg lam),
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [mul_nonneg (sq_nonneg lam) (norm_nonneg v),
      mul_nonneg (abs_nonneg lam) (norm_nonneg w)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_plantedInputDerivative_le (lam : ℝ) (v w : E) :
    ‖plantedInputDerivative lam v w‖ ≤ 2*|lam| *‖v‖ + ‖w‖ + |lam| := by
  rw [plantedInputDerivative, Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖(2*lam) • v‖ + ‖w‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
        linarith [abs_nonneg lam]
  · simp only [Real.norm_eq_abs, abs_neg]
    have hp : 0 ≤ 2*|lam| *‖v‖ := by positivity
    linarith [norm_nonneg w]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasDerivAt_plantedInput (lam : ℝ) (v w : E) :
    HasDerivAt (fun t ↦ plantedInput t v w) (plantedInputDerivative lam v w) lam := by
  have h1 := ((hasDerivAt_pow 2 lam).smul_const v).fun_add ((hasDerivAt_id lam).smul_const w)
  have h2 := (hasDerivAt_pow 2 lam).neg.div_const 2
  simpa only [plantedInput, plantedInputDerivative, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    one_smul, id_eq, Pi.neg_apply, neg_div,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using h1.prodMk h2

theorem moment_plantedInput (mu : Measure Omega) (A : Omega → E) (lam : ℝ) (v w : E) :
    GaussianSpinInterpolation.moment mu (fun _ ↦ 1) (augmentedField A) (plantedInput lam v w) =
      mixtureLikelihood mu (fun x ↦ lam • A x) (lam • v+w) := by
  unfold GaussianSpinInterpolation.moment mixtureLikelihood
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [weight, one_mul, augmentedField_apply, mixtureWeight, plantedInput,
      inner_add_right, real_inner_smul_left, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    congr 1
    ring

theorem logLikelihood_eq_plantedPartition (mu : Measure Omega) (A : Omega → E)
    (lam : ℝ) (v w : E) :
    Real.log (mixtureLikelihood mu (fun x ↦ lam • A x) (lam • v+w)) =
      logPartition mu (augmentedField A) (plantedInput lam v w) := by
  rw [logPartition, moment_plantedInput]

theorem posteriorKernel_eq_plantedGibbs (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) (lam : ℝ) (v w : E) :
    posteriorKernel mu (fun x ↦ lam • A x) (lam • v+w) =
      gibbsMeasure mu (augmentedField A) (plantedInput lam v w) := by
  rw [posteriorKernel_apply mu (fun x ↦ lam • A x) (measurable_const.smul hA), gibbsMeasure]
  congr 1
  funext x
  rw [moment_plantedInput]
  simp only [posteriorWeight, mixtureWeight, augmentedField_apply, plantedInput,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  congr 1
  ring

theorem posteriorMean_eq_plantedExpectation (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (a : Omega → ℝ) (lam : ℝ) (v w : E) :
    posteriorMean mu (fun x ↦ lam • A x) a (lam • v+w) =
      expectation mu a (augmentedField A) (plantedInput lam v w) := by
  rw [posteriorMean, posteriorKernel_eq_plantedGibbs mu A hA]
  exact integral_gibbsMeasure mu (augmentedField A) (measurable_augmentedField A hA)
    (augmentedField_ae_bound mu A hK hAB) (plantedInput lam v w) a

theorem hasDerivAt_plantedLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v w : E) :
    HasDerivAt (fun t ↦ Real.log (mixtureLikelihood mu (fun x ↦ t • A x) (t • v+w)))
      (score mu (augmentedField A) (plantedInput lam v w) (plantedInputDerivative lam v w)) lam := by
  simp_rw [logLikelihood_eq_plantedPartition]
  exact (logPartition_hasFDerivAt mu (augmentedField A) (measurable_augmentedField A hA)
    (by positivity : 0 ≤ K+K^2) (augmentedField_ae_bound mu A hK hAB)
    (plantedInput lam v w)).comp_hasDerivAt lam (hasDerivAt_plantedInput lam v w)

theorem norm_score_plantedInput_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v w : E) (hv : ‖v‖ ≤ K) :
    ‖score mu (augmentedField A) (plantedInput lam v w) (plantedInputDerivative lam v w)‖ ≤
      (K+K^2) * (2*|lam| *K+‖w‖+|lam|) := by
  have hs := norm_score_le mu (augmentedField A) (measurable_augmentedField A hA)
    (by positivity : 0 ≤ K+K^2) (augmentedField_ae_bound mu A hK hAB) (plantedInput lam v w)
  calc
    _ ≤ ‖score mu (augmentedField A) (plantedInput lam v w)‖ *
        ‖plantedInputDerivative lam v w‖ :=
      (score mu (augmentedField A) (plantedInput lam v w)).le_opNorm _
    _ ≤ (K+K^2) * (2*|lam| *K+‖w‖+|lam|) := by
      apply mul_le_mul hs _ (norm_nonneg _) (by positivity)
      exact (norm_plantedInputDerivative_le lam v w).trans (by gcongr)

theorem score_plantedInput_eq_posteriorMean (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) (v w : E) :
    score mu (augmentedField A) (plantedInput lam v w) (plantedInputDerivative lam v w) =
      posteriorMean mu (fun x ↦ lam • A x)
        (fun x ↦ inner ℝ (A x) ((2*lam) • v+w) - lam*‖A x‖^2) (lam • v+w) := by
  rw [posteriorMean_eq_plantedExpectation mu A hA hK hAB,
    score_apply mu (augmentedField A) (measurable_augmentedField A hA)
      (augmentedField_ae_bound mu A hK hAB)]
  apply congrArg (fun a ↦ expectation mu a (augmentedField A) (plantedInput lam v w))
  funext x
  simp only [augmentedField_apply, plantedInputDerivative]
  ring

noncomputable def plantedLogDerivative (mu : Measure Omega) (A : Omega → E) (lam : ℝ)
    (z : Omega × E) : ℝ :=
  score mu (augmentedField A) (plantedInput lam (A z.1) z.2)
    (plantedInputDerivative lam (A z.1) z.2)

theorem measurable_plantedInput (A : Omega → E) (hA : Measurable A) (lam : ℝ) :
    Measurable (fun z : Omega × E ↦ plantedInput lam (A z.1) z.2) :=
  ((measurable_const.smul (hA.comp measurable_fst)).add
    (measurable_const.smul measurable_snd)).prodMk measurable_const

theorem measurable_plantedInputDerivative (A : Omega → E) (hA : Measurable A) (lam : ℝ) :
    Measurable (fun z : Omega × E ↦ plantedInputDerivative lam (A z.1) z.2) :=
  ((measurable_const.smul (hA.comp measurable_fst)).add measurable_snd).prodMk measurable_const

theorem measurable_plantedLogDerivative (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    Measurable (plantedLogDerivative mu A lam) := by
  have hs := score_continuous mu (augmentedField A) (measurable_augmentedField A hA)
    (by positivity : 0 ≤ K+K^2) (augmentedField_ae_bound mu A hK hAB)
  have heval : Continuous (fun p : ((E × ℝ) →L[ℝ] ℝ) × (E × ℝ) ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp (((hs.measurable.comp (measurable_plantedInput A hA lam))).prodMk
    (measurable_plantedInputDerivative A hA lam))

theorem measurable_plantedLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) (lam : ℝ) :
    Measurable (fun z : Omega × E ↦
      Real.log (mixtureLikelihood mu (fun x ↦ lam • A x) (lam • A z.1+z.2))) :=
  ((measurable_mixtureLikelihood mu (fun x ↦ lam • A x) (measurable_const.smul hA)).log).comp
    ((measurable_const.smul (hA.comp measurable_fst)).add measurable_snd)

theorem integrable_plantedLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ}
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    Integrable (fun z : Omega × E ↦
      Real.log (mixtureLikelihood mu (fun x ↦ lam • A x) (lam • A z.1+z.2)))
      (mu.prod (stdGaussian E)) := by
  have hA2 : MemLp A 2 mu := MemLp.of_bound hA.aestronglyMeasurable K hAB
  have hL : Measurable (fun y ↦ Real.log (mixtureLikelihood mu (fun x ↦ lam • A x) y)) :=
    (measurable_mixtureLikelihood mu (fun x ↦ lam • A x) (measurable_const.smul hA)).log
  have hObs : Measurable (fun z : Omega × E ↦ lam • A z.1+z.2) :=
    (measurable_const.smul (hA.comp measurable_fst)).add measurable_snd
  exact (integrable_map_measure hL.aestronglyMeasurable hObs.aemeasurable).mp
    (integrable_mixtureLogLikelihood mu (fun x ↦ lam • A x)
      (measurable_const.smul hA) (hA2.const_smul lam))

/-- The Gaussian norm is an integrable dominating function for the full actual
planted derivative, uniformly on a neighborhood of any real channel strength. -/
theorem hasDerivAt_integral_plantedLogLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (hA : Measurable A) {K : ℝ} (hK : 0 ≤ K)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    HasDerivAt (fun t ↦ ∫ z : Omega × E,
      Real.log (mixtureLikelihood mu (fun x ↦ t • A x) (t • A z.1+z.2))
      ∂mu.prod (stdGaussian E))
      (∫ z, plantedLogDerivative mu A lam z ∂mu.prod (stdGaussian E)) lam := by
  have hn : Integrable (fun z : Omega × E ↦ ‖z.2‖) (mu.prod (stdGaussian E)) :=
    (show Integrable (fun w : E ↦ ‖w‖) (stdGaussian E) from IsGaussian.integrable_id.norm).comp_snd mu
  have hboundInt : Integrable (fun z : Omega × E ↦
      (K+K^2)*(2*(|lam|+1)*K+‖z.2‖+(|lam|+1))) (mu.prod (stdGaussian E)) :=
    (((integrable_const _).add hn).add (integrable_const _)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu.prod (stdGaussian E)) (s := Metric.ball lam 1)
    (F' := plantedLogDerivative mu A)
    (bound := fun z : Omega × E ↦ (K+K^2)*(2*(|lam|+1)*K+‖z.2‖+(|lam|+1)))
    (Metric.ball_mem_nhds lam zero_lt_one)
    (.of_forall fun t ↦ (measurable_plantedLogLikelihood mu A hA t).aestronglyMeasurable)
    (integrable_plantedLogLikelihood mu A hA hAB lam)
    (measurable_plantedLogDerivative mu A hA hK hAB lam).aestronglyMeasurable ?_ hboundInt
    (.of_forall fun z t _ ↦ hasDerivAt_plantedLogLikelihood mu A hA hK hAB t (A z.1) z.2)).2
  have hz : ∀ᵐ z : Omega × E ∂mu.prod (stdGaussian E), ‖A z.1‖ ≤ K :=
    Measure.quasiMeasurePreserving_fst.ae hAB
  filter_upwards [hz] with z hAz t ht
  exact (norm_score_plantedInput_le mu A hA hK hAB t (A z.1) z.2 hAz).trans (by
    have ht' := norm_le_of_mem_ball ht
    simp only [Real.norm_eq_abs] at ht'
    gcongr)


end TensorPCA.GaussianBoundedChannelDerivativeProofs
