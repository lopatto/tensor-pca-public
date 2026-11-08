-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityLogProofs

/-! Gaussian experiment transports for the exact finite cavity increment. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityLawProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityPartitionProofs FinitePriorCavityNormalizationProofs FinitePriorCavityLogProofs
open GaussianPriorTransferProofs GaussianTwoChannelFreeEnergyProofs TensorOrbitCountProofs TensorOrbitAggregationProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem oldConfiguration_prior_map (p : Measure S) [IsProbabilityMeasure p] (N : ℕ) :
    (configurationPrior p (N+1)).map oldConfiguration = configurationPrior p N := by
  have heq : oldConfiguration = Prod.fst ∘ (configurationSplit (S := S) N) := by
    funext x
    rw [Function.comp_apply,configurationSplit_apply]
  rw [heq,← Measure.map_map measurable_fst (configurationSplit N).measurable,
    (configurationSplit_measurePreserving p N).map_eq,Measure.map_fst_prod]
  simp

theorem oldNoise_gaussian_map {N k : ℕ} (hk : 0 < k) :
    (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).map
      (fun w ↦ (disorderSplit hk w).1) = stdGaussian (EuclideanSpace ℝ (KSubset N k)) := by
  change (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).map (Prod.fst ∘ disorderSplit hk) = _
  rw [← Measure.map_map measurable_fst (disorderSplit hk).continuous.measurable,
    disorderSplit_gaussian_map,Measure.map_fst_prod]
  simp

def recombinedNoise {N k : ℕ} (hk : 0 < k) (gamma : ℝ)
    (z : EuclideanSpace ℝ (KSubset (N+1) k) × EuclideanSpace ℝ (KSubset N k)) :
    EuclideanSpace ℝ (KSubset N k) :=
  gaussianMix (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
    (correctionCoefficient N k gamma/aggregateCoefficient N k gamma) ((disorderSplit hk z.1).1,z.2)

theorem continuous_recombinedNoise {N k : ℕ} (hk : 0 < k) (gamma : ℝ) : Continuous (recombinedNoise (N := N) hk gamma) := by
  unfold recombinedNoise
  exact (gaussianMix _ _).continuous.comp
    ((continuous_fst.comp ((disorderSplit hk).continuous.comp continuous_fst)).prodMk continuous_snd)

theorem recombinedNoise_gaussian_map {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma) :
    ((stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).prod (stdGaussian (EuclideanSpace ℝ (KSubset N k)))).map
      (recombinedNoise hk gamma) = stdGaussian (EuclideanSpace ℝ (KSubset N k)) := by
  change ((stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k))).prod (stdGaussian (EuclideanSpace ℝ (KSubset N k)))).map
    (gaussianMix (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
      (correctionCoefficient N k gamma/aggregateCoefficient N k gamma) ∘
        Prod.map (fun w ↦ (disorderSplit hk w).1) id) = _
  have hOld : Measurable (fun w : EuclideanSpace ℝ (KSubset (N+1) k) ↦ (disorderSplit hk w).1) :=
    measurable_fst.comp (disorderSplit hk).continuous.measurable
  have hMix := (gaussianMix (E := EuclideanSpace ℝ (KSubset N k))
    (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
    (correctionCoefficient N k gamma/aggregateCoefficient N k gamma)).continuous.measurable
  rw [← Measure.map_map hMix (hOld.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hOld measurable_id,
    oldNoise_gaussian_map,Measure.map_id,correction_noise_gaussian_map hN hk hgamma]

def cavityExperimentLaw (p : Measure S) (N k : ℕ) :
    Measure (((Fin (N+1) → S) × EuclideanSpace ℝ (KSubset (N+1) k)) × EuclideanSpace ℝ (KSubset N k)) :=
  ((configurationPrior p (N+1)).prod (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k)))).prod
    (stdGaussian (EuclideanSpace ℝ (KSubset N k)))

def recombinedExperiment {N k : ℕ} (hk : 0 < k) (gamma : ℝ)
    (z : ((Fin (N+1) → S) × EuclideanSpace ℝ (KSubset (N+1) k)) × EuclideanSpace ℝ (KSubset N k)) :
    (Fin N → S) × EuclideanSpace ℝ (KSubset N k) :=
  (oldConfiguration z.1.1,recombinedNoise hk gamma (z.1.2,z.2))

theorem measurable_recombinedExperiment {N k : ℕ} (hk : 0 < k) (gamma : ℝ) :
    Measurable (recombinedExperiment (S := S) (N := N) hk gamma) := by
  unfold recombinedExperiment
  exact ((measurable_of_finite oldConfiguration).comp (measurable_fst.comp measurable_fst)).prodMk
    ((continuous_recombinedNoise hk gamma).measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- Recombining the actual background Gaussian block with the independent y
noise and discarding the planted last coordinate gives exactly the original
N-variable product-prior Gaussian experiment. -/
theorem recombinedExperiment_map (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma) :
    (cavityExperimentLaw p N k).map (recombinedExperiment hk gamma) =
      (configurationPrior p N).prod (stdGaussian (EuclideanSpace ℝ (KSubset N k))) := by
  change (((configurationPrior p (N+1)).prod (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k)))).prod
    (stdGaussian (EuclideanSpace ℝ (KSubset N k)))).map
      (Prod.map oldConfiguration (recombinedNoise hk gamma) ∘ MeasurableEquiv.prodAssoc) = _
  rw [← Measure.map_map ((measurable_of_finite oldConfiguration).prodMap (continuous_recombinedNoise hk gamma).measurable)
      MeasurableEquiv.prodAssoc.measurable,
    (measurePreserving_prodAssoc _ _ _).map_eq,
    ← Measure.map_prod_map _ _ (measurable_of_finite oldConfiguration) (continuous_recombinedNoise hk gamma).measurable,
    oldConfiguration_prior_map,recombinedNoise_gaussian_map hN hk hgamma]

def cavityIncrementIntegrand (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {N k : ℕ} (hk : 0 < k) (gamma : ℝ)
    (z : ((Fin (N+1) → S) × EuclideanSpace ℝ (KSubset (N+1) k)) × EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  Real.log (∫ x, cavityFactor p a N k gamma (oldConfiguration z.1.1) (z.1.1 (Fin.last N))
    (disorderSplit hk z.1.2).2 x ∂backgroundPosterior p a N k gamma (oldConfiguration z.1.1) (disorderSplit hk z.1.2).1)-
  Real.log (correctionFactor p a N k gamma (oldConfiguration z.1.1) (disorderSplit hk z.1.2).1 z.2)

/-- The actual unnormalized N-to-N+1 free-energy increment is the expectation
of the two true posterior log factors. Integrability is part of the conclusion;
no increment, limit, or posterior-concentration claim is assumed. -/
theorem cavity_increment_formula (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) :
    Integrable (cavityIncrementIntegrand p a hk gamma) (cavityExperimentLaw p N k) ∧
    mixtureFreeEnergy (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)-
      mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma) =
        ∫ z, cavityIncrementIntegrand p a hk gamma z ∂cavityExperimentLaw p N k := by
  let fPlus := fun z : (Fin (N+1) → S) × EuclideanSpace ℝ (KSubset (N+1) k) ↦
    Real.log (mixtureLikelihood (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
      (tensorSignal a (N+1) k gamma z.1+z.2))
  let fOld := fun z : (Fin N → S) × EuclideanSpace ℝ (KSubset N k) ↦
    Real.log (mixtureLikelihood (configurationPrior p N) (tensorSignal a N k gamma)
      (tensorSignal a N k gamma z.1+z.2))
  have hFP := measurable_tensorSignal a (N+1) k gamma
  have hFO := measurable_tensorSignal a N k gamma
  obtain ⟨KP,_,hBP⟩ := finite_signal_bound (tensorSignal a (N+1) k gamma)
  obtain ⟨KO,_,hBO⟩ := finite_signal_bound (tensorSignal a N k gamma)
  have hiPlus : Integrable fPlus ((configurationPrior p (N+1)).prod (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k)))) :=
    integrable_logLikelihood_experiment _ _ hFP (Filter.Eventually.of_forall hBP)
  have hiOld : Integrable fOld ((configurationPrior p N).prod (stdGaussian (EuclideanSpace ℝ (KSubset N k)))) :=
    integrable_logLikelihood_experiment _ _ hFO (Filter.Eventually.of_forall hBO)
  have hmOld : Measurable fOld := ((measurable_mixtureLikelihood _ _ hFO).log).comp
    ((hFO.comp measurable_fst).add measurable_snd)
  have hiPlusPull : Integrable (fun z ↦ fPlus z.1) (cavityExperimentLaw p N k) := hiPlus.comp_fst _
  have hiOldMap : Integrable fOld ((cavityExperimentLaw p N k).map (recombinedExperiment hk gamma)) := by
    rw [recombinedExperiment_map p hN hk hgamma]
    exact hiOld
  have hiOldPull : Integrable (fun z ↦ fOld (recombinedExperiment hk gamma z)) (cavityExperimentLaw p N k) :=
    (integrable_map_measure hmOld.aestronglyMeasurable (measurable_recombinedExperiment hk gamma).aemeasurable).mp hiOldMap
  have hPlusIntegral : mixtureFreeEnergy (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma) =
      ∫ z, fPlus z.1 ∂cavityExperimentLaw p N k := by
    rw [mixtureFreeEnergy_eq_integral_experiment _ _ hFP]
    change (∫ z, fPlus z ∂(configurationPrior p (N+1)).prod (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k)))) =
      ∫ z, fPlus z.1 ∂((configurationPrior p (N+1)).prod (stdGaussian (EuclideanSpace ℝ (KSubset (N+1) k)))).prod
        (stdGaussian (EuclideanSpace ℝ (KSubset N k)))
    rw [integral_fun_fst]
    simp
  have hOldIntegral : mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma) =
      ∫ z, fOld (recombinedExperiment hk gamma z) ∂cavityExperimentLaw p N k := by
    rw [mixtureFreeEnergy_eq_integral_experiment _ _ hFO]
    have H := integral_map (μ := cavityExperimentLaw p N k) (measurable_recombinedExperiment (S := S) (N := N) hk gamma).aemeasurable hmOld.aestronglyMeasurable
    rw [recombinedExperiment_map p hN hk hgamma] at H
    exact H
  have hEq : (fun z ↦ fPlus z.1-fOld (recombinedExperiment hk gamma z)) = cavityIncrementIntegrand p a hk gamma := by
    funext z
    exact cavity_log_increment p hN hk hgamma a z.1.1 z.1.2 z.2
  refine ⟨?_,?_⟩
  · rw [← hEq]
    exact hiPlusPull.sub hiOldPull
  · rw [hPlusIntegral,hOldIntegral,← integral_sub hiPlusPull hiOldPull]
    exact congrArg (fun f ↦ ∫ z, f z ∂cavityExperimentLaw p N k) hEq

end
end TensorPCA.FinitePriorCavityLawProofs
