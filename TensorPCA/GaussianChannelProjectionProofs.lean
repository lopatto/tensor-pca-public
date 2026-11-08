-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianChannelInformationProofs

/-!
# Retaining part of a Gaussian channel

For a linear observation map which sends canonical Gaussian noise to canonical
Gaussian noise, data processing compares both output entropy and mutual information. Their difference bounds the free-energy cost of discarded signal
coordinates by their signal energy. The noise transport premise is a concrete
finite linear-Gaussian fact, to be proved for each applied coordinate map.
-/
@[expose] public section

namespace TensorPCA.GaussianChannelProjectionProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianMixtureStabilityProofs GaussianChannelInformationProofs
open scoped ENNReal RealInnerProductSpace

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem map_gaussian_product (mu : Measure Omega) (P : E →L[ℝ] D)
    (hP : (stdGaussian E).map P = stdGaussian D) :
    (mu.prod (stdGaussian E)).map (Prod.map id P) = mu.prod (stdGaussian D) := by
  rw [← Measure.map_prod_map mu (stdGaussian E) measurable_id P.continuous.measurable,
    Measure.map_id, hP]

theorem map_mixtureLaw (mu : Measure Omega) (F : Omega → E) (hF : Measurable F)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    (mixtureLaw mu F).map P = mixtureLaw mu (P ∘ F) := by
  have hObsE : Measurable (fun z : Omega × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  have hObsD : Measurable (fun z : Omega × D ↦ P (F z.1)+z.2) :=
    (P.continuous.measurable.comp (hF.comp measurable_fst)).add measurable_snd
  change ((mu.prod (stdGaussian E)).map (fun z ↦ F z.1+z.2)).map P =
    (mu.prod (stdGaussian D)).map (fun z ↦ P (F z.1)+z.2)
  rw [← map_gaussian_product mu P hP, Measure.map_map P.continuous.measurable hObsE,
    Measure.map_map hObsD (measurable_id.prodMap P.continuous.measurable)]
  congr 1
  funext z
  exact P.map_add _ _

theorem map_jointLaw (mu : Measure Omega) (F : Omega → E) (hF : Measurable F)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    (jointLaw mu F).map (Prod.map id P) = jointLaw mu (P ∘ F) := by
  have hObsE : Measurable (fun z : Omega × E ↦ (z.1, F z.1+z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  have hObsD : Measurable (fun z : Omega × D ↦ (z.1, P (F z.1)+z.2)) :=
    measurable_fst.prodMk ((P.continuous.measurable.comp (hF.comp measurable_fst)).add measurable_snd)
  change ((mu.prod (stdGaussian E)).map (fun z ↦ (z.1, F z.1+z.2))).map (Prod.map id P) =
    (mu.prod (stdGaussian D)).map (fun z ↦ (z.1, P (F z.1)+z.2))
  rw [← map_gaussian_product mu P hP,
    Measure.map_map (measurable_id.prodMap P.continuous.measurable) hObsE,
    Measure.map_map hObsD (measurable_id.prodMap P.continuous.measurable)]
  congr 1
  funext z
  exact congrArg (Prod.mk z.1) (P.map_add _ _)

theorem map_product_output (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    (mu.prod (mixtureLaw mu F)).map (Prod.map id P) = mu.prod (mixtureLaw mu (P ∘ F)) := by
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  rw [← Measure.map_prod_map mu (mixtureLaw mu F) measurable_id P.continuous.measurable,
    Measure.map_id, map_mixtureLaw mu F hF P hP]

theorem mixtureFreeEnergy_projection_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    mixtureFreeEnergy mu (P ∘ F) ≤ mixtureFreeEnergy mu F := by
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  have hfin := klDiv_mixtureLaw_ne_top mu F (fun _ ↦ (0 : E)) hF measurable_const
    (by simpa using hF2)
  rw [mixtureLaw_zero] at hfin
  have h := klDiv_map_le (mixtureLaw mu F) (stdGaussian E) P.continuous.measurable
  rw [map_mixtureLaw mu F hF P hP, hP] at h
  exact ENNReal.toReal_mono hfin h

theorem channelInformation_projection_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    channelInformation mu (P ∘ F) ≤ channelInformation mu F := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  have h := klDiv_map_le (jointLaw mu F) (mu.prod (mixtureLaw mu F))
    (measurable_id.prodMap P.continuous.measurable)
  rw [map_jointLaw mu F hF P hP, map_product_output mu F hF P hP] at h
  exact ENNReal.toReal_mono (channelInformation_finite mu F hF hF2) h

/-- Keeping a Gaussian subchannel changes the free energy by a
nonnegative amount bounded by half the discarded signal energy. -/
theorem discarded_channel_freeEnergy_bounds (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu)
    (P : E →L[ℝ] D) (hP : (stdGaussian E).map P = stdGaussian D) :
    0 ≤ mixtureFreeEnergy mu F-mixtureFreeEnergy mu (P ∘ F) ∧
    mixtureFreeEnergy mu F-mixtureFreeEnergy mu (P ∘ F) ≤
      (1 / 2 : ℝ) * ∫ x, (‖F x‖ ^ 2-‖P (F x)‖ ^ 2) ∂mu := by
  constructor
  · exact sub_nonneg.mpr (mixtureFreeEnergy_projection_le mu F hF hF2 P hP)
  · have hPF : Measurable (P ∘ F) := P.continuous.measurable.comp hF
    have hPF2 : MemLp (P ∘ F) 2 mu := P.comp_memLp' hF2
    have hI := channelInformation_projection_le mu F hF hF2 P hP
    rw [mixtureFreeEnergy_eq_energy_sub_information mu F hF hF2,
      mixtureFreeEnergy_eq_energy_sub_information mu (P ∘ F) hPF hPF2,
      integral_sub (f := fun x ↦ ‖F x‖ ^ 2) (g := fun x ↦ ‖P (F x)‖ ^ 2)
        (hF2.integrable_norm_pow (by decide : 2 ≠ 0))
        (hPF2.integrable_norm_pow (by decide : 2 ≠ 0))]
    simp only [Function.comp_apply]
    linarith


end TensorPCA.GaussianChannelProjectionProofs
