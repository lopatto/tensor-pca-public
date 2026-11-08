-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMixtureStabilityProofs

/-!
# Gaussian-channel information identities

Mutual information is the relative entropy of the latent/output joint law to the product of its two marginals. No auxiliary information quantity or
conditional-distribution premise is introduced.
-/
@[expose] public section

namespace TensorPCA.GaussianChannelInformationProofs

open MeasureTheory ProbabilityTheory InformationTheory GaussianPriorTransferProofs
  GaussianMixtureStabilityProofs
open scoped ENNReal RealInnerProductSpace

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def channelInformation (mu : Measure Omega) (F : Omega → E) : ℝ :=
  (klDiv (jointLaw mu F) (mu.prod (mixtureLaw mu F))).toReal

omit [BorelSpace E] in
theorem jointLaw_zero (mu : Measure Omega) [IsProbabilityMeasure mu] :
    jointLaw mu (fun _ ↦ (0 : E)) = mu.prod (stdGaussian E) := by
  simp [jointLaw]

theorem product_output_eq_withDensity (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    mu.prod (mixtureLaw mu F) = (mu.prod (stdGaussian E)).withDensity
      (fun z ↦ ENNReal.ofReal (mixtureLikelihood mu F z.2)) := by
  rw [mixtureLaw_eq_withDensity mu F hF, prod_withDensity_right
    (measurable_mixtureLikelihood mu F hF).ennreal_ofReal]

theorem jointLaw_llr_base (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    llr (jointLaw mu F) (mu.prod (stdGaussian E)) =ᵐ[jointLaw mu F]
      fun z ↦ Real.log (mixtureWeight (F z.1) z.2) := by
  have h := jointLaw_llr mu F (fun _ ↦ (0 : E)) hF measurable_const
  rw [jointLaw_zero] at h
  simpa only [mixtureWeight, Real.log_exp, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, sub_self, sub_zero] using h

theorem jointLaw_llr_product (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    llr (jointLaw mu F) (mu.prod (mixtureLaw mu F)) =ᵐ[jointLaw mu F] fun z ↦
      Real.log (mixtureWeight (F z.1) z.2) - Real.log (mixtureLikelihood mu F z.2) := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have hW : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hL : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureLikelihood mu F z.2)) :=
    (measurable_mixtureLikelihood mu F hF).ennreal_ofReal.comp measurable_snd
  have hright := Measure.rnDeriv_withDensity_right (jointLaw mu F) (mu.prod (stdGaussian E))
    hL.aemeasurable (.of_forall fun z ↦ (ENNReal.ofReal_pos.mpr (mixtureLikelihood_pos mu F hF z.2)).ne')
    (.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
  have hleft := Measure.rnDeriv_withDensity (mu.prod (stdGaussian E)) hW
  rw [← jointLaw_eq_withDensity mu F hF] at hleft
  rw [← product_output_eq_withDensity mu F hF] at hright
  filter_upwards [hleft.filter_mono (jointLaw_absolutelyContinuous mu F hF).ae_le,
    hright.filter_mono (jointLaw_absolutelyContinuous mu F hF).ae_le] with z hl hr
  rw [llr, hr, hl, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mixtureWeight_pos (F z.1) z.2).le,
    ENNReal.toReal_ofReal (mixtureLikelihood_pos mu F hF z.2).le,
    Real.log_mul (inv_ne_zero (mixtureLikelihood_pos mu F hF z.2).ne')
      (mixtureWeight_pos (F z.1) z.2).ne', Real.log_inv]
  ring

theorem jointLaw_absolutelyContinuous_product (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : jointLaw mu F ≪ mu.prod (mixtureLaw mu F) := by
  apply (jointLaw_absolutelyContinuous mu F hF).trans
  rw [product_output_eq_withDensity mu F hF]
  exact withDensity_absolutelyContinuous'
    ((measurable_mixtureLikelihood mu F hF).ennreal_ofReal.comp measurable_snd).aemeasurable
    (.of_forall fun z ↦ (ENNReal.ofReal_pos.mpr (mixtureLikelihood_pos mu F hF z.2)).ne')

theorem integrable_joint_logWeight (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    Integrable (fun z : Omega × E ↦ Real.log (mixtureWeight (F z.1) z.2)) (jointLaw mu F) := by
  have h := integrable_jointLaw_llr mu F (fun _ ↦ (0 : E)) hF measurable_const (by simpa using hF2)
  rw [jointLaw_zero] at h
  exact h.congr (jointLaw_llr_base mu F hF)

theorem integrable_joint_logLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    Integrable (fun z : Omega × E ↦ Real.log (mixtureLikelihood mu F z.2)) (jointLaw mu F) := by
  have h := integrable_mixtureLogLikelihood mu F hF hF2
  rw [← jointLaw_map_snd mu F hF] at h
  exact (integrable_map_measure (measurable_mixtureLikelihood mu F hF).log.aestronglyMeasurable
    measurable_snd.aemeasurable).mp h

theorem channelInformation_finite (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    klDiv (jointLaw mu F) (mu.prod (mixtureLaw mu F)) ≠ ∞ := by
  apply klDiv_ne_top (jointLaw_absolutelyContinuous_product mu F hF)
  exact ((integrable_joint_logWeight mu F hF hF2).sub'
    (integrable_joint_logLikelihood mu F hF hF2)).congr (jointLaw_llr_product mu F hF).symm

/-- Exact finite Gaussian channel identity: output free energy equals half
signal energy minus actual latent/output mutual information. -/
theorem mixtureFreeEnergy_eq_energy_sub_information (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    mixtureFreeEnergy mu F = (1 / 2 : ℝ) * (∫ x, ‖F x‖ ^ 2 ∂mu)-channelInformation mu F := by
  have : IsProbabilityMeasure (jointLaw mu F) := jointLaw_probability mu F hF
  have : IsProbabilityMeasure (mixtureLaw mu F) := mixtureLaw_probability mu F hF
  have hW : (∫ z, Real.log (mixtureWeight (F z.1) z.2) ∂jointLaw mu F) =
      (1 / 2 : ℝ) * ∫ x, ‖F x‖ ^ 2 ∂mu := by
    have h := integral_jointLaw_llr mu F (fun _ ↦ (0 : E)) hF measurable_const (by simpa using hF2)
    rw [jointLaw_zero, integral_congr_ae (jointLaw_llr_base mu F hF)] at h
    simpa only [sub_zero] using h
  have hL : (∫ z : Omega × E, Real.log (mixtureLikelihood mu F z.2) ∂jointLaw mu F) =
      mixtureFreeEnergy mu F := by
    rw [mixtureFreeEnergy_eq_integral mu F hF, ← jointLaw_map_snd mu F hF,
      integral_map measurable_snd.aemeasurable (measurable_mixtureLikelihood mu F hF).log.aestronglyMeasurable]
  rw [channelInformation, toReal_klDiv_of_measure_eq (jointLaw_absolutelyContinuous_product mu F hF) (by simp),
    integral_congr_ae (jointLaw_llr_product mu F hF),
    integral_sub (integrable_joint_logWeight mu F hF hF2) (integrable_joint_logLikelihood mu F hF hF2), hW, hL]
  ring

theorem mixtureFreeEnergy_le_half_energy (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (hF2 : MemLp F 2 mu) :
    mixtureFreeEnergy mu F ≤ (1 / 2 : ℝ) * ∫ x, ‖F x‖ ^ 2 ∂mu := by
  rw [mixtureFreeEnergy_eq_energy_sub_information mu F hF hF2]
  exact sub_le_self _ ENNReal.toReal_nonneg


end TensorPCA.GaussianChannelInformationProofs
