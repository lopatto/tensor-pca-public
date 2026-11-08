-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianReplicaTransportProofs
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-! # The full two-channel posterior reconstructs the joint law -/
@[expose] public section

namespace TensorPCA.GaussianCombinedPosteriorProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs GaussianReplicaTransportProofs
open scoped RealInnerProductSpace ENNReal

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

noncomputable def conditionalOutputKernel (mu : Measure Omega) [SFinite mu]
    (A : Omega → E) (B : Omega → D) : Kernel D E :=
  (Kernel.const D (stdGaussian E)).withDensity
    (fun v y ↦ ENNReal.ofReal (mixtureLikelihood (posteriorKernel mu B v) A y))

theorem conditionalOutputKernel_apply (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (v : D) :
    conditionalOutputKernel mu A B v = mixtureLaw (posteriorKernel mu B v) A := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  rw [conditionalOutputKernel, Kernel.withDensity_apply _
    (measurable_conditionalLikelihood mu A B hA hB).ennreal_ofReal, Kernel.const_apply,
    mixtureLaw_eq_withDensity (posteriorKernel mu B v) A hA]

theorem conditionalOutputKernel_isMarkov (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    IsMarkovKernel (conditionalOutputKernel mu A B) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  refine ⟨fun v ↦ ?_⟩
  rw [conditionalOutputKernel_apply mu A B hA hB]
  exact mixtureLaw_probability (posteriorKernel mu B v) A hA

theorem conditionalOutputKernel_eq_map (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    conditionalOutputKernel mu A B = (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)).map
      (fun z : Omega × E ↦ A z.1+z.2) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hObs : Measurable (fun z : Omega × E ↦ A z.1+z.2) := (hA.comp measurable_fst).add measurable_snd
  apply Kernel.ext
  intro v
  rw [conditionalOutputKernel_apply mu A B hA hB,
    Kernel.map_apply _ hObs, Kernel.prod_apply, Kernel.const_apply]
  rfl

theorem pairObservationLaw_eq_compProd (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    pairObservationLaw mu A B = (mixtureLaw mu B) ⊗ₘ conditionalOutputKernel mu A B := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have hM : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,(z.1.1,z.2))) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hObs : Measurable (fun z : Omega × E ↦ A z.1+z.2) := (hA.comp measurable_fst).add measurable_snd
  symm
  rw [conditionalOutputKernel_eq_map mu A B hA hB, Measure.compProd_map hObs,
    sideExperiment_eq_actualLaw mu B hB,
    Measure.map_map (measurable_id.prodMap hObs) hM]
  rfl

theorem conditionalOutput_compProd_combined (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    conditionalOutputKernel mu A B ⊗ₖ combinedPosteriorKernel mu A B =
      (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)).map
        (fun z : Omega × E ↦ (A z.1+z.2,z.1)) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsMarkovKernel (conditionalOutputKernel mu A B) := conditionalOutputKernel_isMarkov mu A B hA hB
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have hObs : Measurable (fun z : Omega × E ↦ (A z.1+z.2,z.1)) :=
    ((hA.comp measurable_fst).add measurable_snd).prodMk measurable_fst
  apply Kernel.ext
  intro v
  rw [Kernel.compProd_apply_eq_compProd_sectR, conditionalOutputKernel_apply mu A B hA hB,
    Kernel.map_apply _ hObs, Kernel.prod_apply, Kernel.const_apply]
  have hk : Kernel.sectR (combinedPosteriorKernel mu A B) v = posteriorKernel (posteriorKernel mu B v) A := by
    apply Kernel.ext
    intro y
    rw [Kernel.sectR_apply, combinedPosteriorKernel_apply mu A B hA hB,
      posteriorKernel_apply (posteriorKernel mu B v) A hA]
  rw [hk, mixture_compProd_posteriorKernel (posteriorKernel mu B v) A hA]

theorem pairLaw_compProd_combinedPosterior (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    (pairObservationLaw mu A B) ⊗ₘ combinedPosteriorKernel mu A B =
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)).map
        (fun z ↦ ((B z.1.1+z.1.2,A z.1.1+z.2),z.1.1)) := by
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsMarkovKernel (conditionalOutputKernel mu A B) := conditionalOutputKernel_isMarkov mu A B hA hB
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have hM : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,(z.1.1,z.2))) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hObs : Measurable (fun z : Omega × E ↦ (A z.1+z.2,z.1)) :=
    ((hA.comp measurable_fst).add measurable_snd).prodMk measurable_fst
  rw [pairObservationLaw_eq_compProd mu A B hA hB, ← Measure.compProd_assoc,
    conditionalOutput_compProd_combined mu A B hA hB, Measure.compProd_map hObs,
    sideExperiment_eq_actualLaw mu B hB,
    Measure.map_map (measurable_id.prodMap hObs) hM,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable ((measurable_id.prodMap hObs).comp hM)]
  rfl

theorem pairObservationLaw_probability (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    IsProbabilityMeasure (pairObservationLaw mu A B) := by
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have : IsMarkovKernel (conditionalOutputKernel mu A B) := conditionalOutputKernel_isMarkov mu A B hA hB
  rw [pairObservationLaw_eq_compProd mu A B hA hB]
  infer_instance

theorem pairObservationLaw_eq_withDensity (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    pairObservationLaw mu A B = ((stdGaussian D).prod (stdGaussian E)).withDensity
      (fun p ↦ ENNReal.ofReal (combinedLikelihood mu A B p.2 p.1)) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsMarkovKernel (conditionalOutputKernel mu A B) := conditionalOutputKernel_isMarkov mu A B hA hB
  have : IsMarkovKernel ((Kernel.const D (stdGaussian E)).withDensity
      (fun v y ↦ ENNReal.ofReal (mixtureLikelihood (posteriorKernel mu B v) A y))) :=
    conditionalOutputKernel_isMarkov mu A B hA hB
  rw [pairObservationLaw_eq_compProd mu A B hA hB, mixtureLaw_eq_withDensity mu B hB,
    conditionalOutputKernel, Measure.withDensity_compProd_withDensity
      (measurable_mixtureLikelihood mu B hB).ennreal_ofReal
      (measurable_conditionalLikelihood mu A B hA hB).ennreal_ofReal,
    Measure.compProd_const]
  congr 1
  funext p
  rw [← ENNReal.ofReal_mul (mixtureLikelihood_pos mu B hB p.1).le,
    ← combinedLikelihood_factor mu A B hB]

/-- The literal normalized full likelihood computes the actual conditional
mean given both Gaussian observations, without point-event conditioning. -/
theorem combinedMean_ae_eq_condExp [StandardBorelSpace Omega]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (C : Omega → V) (hC : StronglyMeasurable C) (hInt : Integrable C mu) :
    (fun z : (Omega × D) × E ↦ combinedMean mu A B C (B z.1.1+z.1.2,A z.1.1+z.2)) =ᵐ[
      (mu.prod (stdGaussian D)).prod (stdGaussian E)]
      ((mu.prod (stdGaussian D)).prod (stdGaussian E))[fun z ↦ C z.1.1 |
        MeasurableSpace.comap (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,A z.1.1+z.2))
          (inferInstance : MeasurableSpace (D × E))] := by
  have : Nonempty Omega := nonempty_of_isProbabilityMeasure mu
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have hObs : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,A z.1.1+z.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk ((hA.comp measurable_fst.fst).add measurable_snd)
  have hX : Measurable (fun z : (Omega × D) × E ↦ z.1.1) := measurable_fst.fst
  have hK := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hObs hX
    (pairLaw_compProd_combinedPosterior mu A B hA hB).symm
  have hCE := condExp_ae_eq_integral_condDistrib hObs hX.aemeasurable hC
    ((hInt.comp_fst (stdGaussian D)).comp_fst (stdGaussian E))
  have hk := ae_of_ae_map hObs.aemeasurable hK
  filter_upwards [hCE,hk] with z hcz hkz
  rw [hcz,hkz]
  rfl


end TensorPCA.GaussianCombinedPosteriorProofs
