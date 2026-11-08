-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianBoundedIMMSEProofs
public import Mathlib.Probability.Kernel.Composition.Prod

/-! # A Gaussian side observation as the conditional prior

The two channels have independent Gaussian noises and both likelihoods retain
their full squared-signal penalties. Conditioning on one channel gives the conditional prior for the remaining channel.
-/
@[expose] public section

namespace TensorPCA.GaussianSideChannelProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianPosteriorCovarianceProofs GaussianBoundedIMMSEProofs
open scoped RealInnerProductSpace ENNReal

variable {Omega E D : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

theorem posteriorMean_eq_weightedIntegral (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (a : Omega → ℝ) (y : E) :
    posteriorMean mu F a y = (mixtureLikelihood mu F y)⁻¹ *
      ∫ x, mixtureWeight (F x) y * a x ∂mu := by
  have hm : Measurable (fun x ↦ ENNReal.ofReal (posteriorWeight mu F y x)) :=
    Measurable.of_uncurry_left (x := y) (measurable_posteriorWeight mu F hF)
  rw [posteriorMean, posteriorKernel_apply mu F hF,
    integral_withDensity_eq_integral_toReal_smul hm (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (posteriorWeight_pos mu F hF y _).le, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by simp only [posteriorWeight]; ring

noncomputable def combinedLikelihood (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    (y : E) (v : D) : ℝ :=
  ∫ x, mixtureWeight (A x) y * mixtureWeight (B x) v ∂mu

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem combinedLikelihood_factor (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hB : Measurable B) (y : E) (v : D) :
    combinedLikelihood mu A B y v = mixtureLikelihood mu B v *
      mixtureLikelihood (posteriorKernel mu B v) A y := by
  change _ = mixtureLikelihood mu B v * posteriorMean mu B (fun x ↦ mixtureWeight (A x) y) v
  rw [posteriorMean_eq_weightedIntegral mu B hB, ← mul_assoc,
    mul_inv_cancel₀ (mixtureLikelihood_pos mu B hB v).ne', one_mul]
  unfold combinedLikelihood
  apply integral_congr_ae
  exact .of_forall fun x ↦ mul_comm _ _

theorem posteriorKernel_absolutelyContinuous (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) (v : D) : posteriorKernel mu B v ≪ mu := by
  rw [posteriorKernel_apply mu B hB]
  exact withDensity_absolutelyContinuous mu _

theorem combinedLikelihood_pos (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (y : E) (v : D) :
    0 < combinedLikelihood mu A B y v := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  rw [combinedLikelihood_factor mu A B hB]
  exact mul_pos (mixtureLikelihood_pos mu B hB v)
    (mixtureLikelihood_pos (posteriorKernel mu B v) A hA y)

theorem log_combinedLikelihood_factor (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (y : E) (v : D) :
    Real.log (combinedLikelihood mu A B y v) = Real.log (mixtureLikelihood mu B v) +
      Real.log (mixtureLikelihood (posteriorKernel mu B v) A y) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  rw [combinedLikelihood_factor mu A B hB,
    Real.log_mul (mixtureLikelihood_pos mu B hB v).ne'
      (mixtureLikelihood_pos (posteriorKernel mu B v) A hA y).ne']

theorem measurable_combinedLikelihood (mu : Measure Omega) [SFinite mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    Measurable (Function.uncurry (combinedLikelihood mu A B)) := by
  have h1 : Measurable (fun z : (E × D) × Omega ↦ mixtureWeight (A z.2) z.1.1) :=
    continuous_mixtureWeight.measurable.comp ((hA.comp measurable_snd).prodMk measurable_fst.fst)
  have h2 : Measurable (fun z : (E × D) × Omega ↦ mixtureWeight (B z.2) z.1.2) :=
    continuous_mixtureWeight.measurable.comp ((hB.comp measurable_snd).prodMk measurable_fst.snd)
  exact ((h1.mul h2).stronglyMeasurable.integral_prod_right' (ν := mu)).measurable

theorem measurable_conditionalLikelihood (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun z : D × E ↦ mixtureLikelihood (posteriorKernel mu B z.1) A z.2) := by
  have hm : Measurable (fun z : D × E ↦
      combinedLikelihood mu A B z.2 z.1 / mixtureLikelihood mu B z.1) :=
    ((measurable_combinedLikelihood mu A B hA hB).comp measurable_swap).div
      ((measurable_mixtureLikelihood mu B hB).comp measurable_fst)
  convert hm using 1
  funext z
  rw [combinedLikelihood_factor mu A B hB,
    mul_div_cancel_left₀ _ (mixtureLikelihood_pos mu B hB z.1).ne']

omit [BorelSpace E] in
theorem posterior_prod_eq_compProd_const (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) :
    posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E) =
      posteriorKernel mu B ⊗ₖ Kernel.const (D × Omega) (stdGaussian E) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  ext v s hs
  rw [Kernel.prod_apply, Kernel.const_apply, Measure.prod_apply hs, Kernel.compProd_apply hs]
  rfl

omit [BorelSpace E] in
/-- This is the actual law of the side observation, latent signal and the
independent remaining noise, rather than a synthetic conditional experiment. -/
theorem sideExperiment_eq_actualLaw (mu : Measure Omega) [IsProbabilityMeasure mu]
    (B : Omega → D) (hB : Measurable B) :
    (mixtureLaw mu B) ⊗ₘ (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)) =
      ((mu.prod (stdGaussian D)).prod (stdGaussian E)).map
        (fun z ↦ (B z.1.1+z.1.2, (z.1.1,z.2))) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have hY : Measurable (fun z : Omega × D ↦ (B z.1+z.2, z.1)) :=
    ((hB.comp measurable_fst).add measurable_snd).prodMk measurable_fst
  have hp := Measure.map_prod_map (mu.prod (stdGaussian D)) (stdGaussian E) hY measurable_id
  simp only [Measure.map_id] at hp
  rw [posterior_prod_eq_compProd_const mu B hB, ← Measure.compProd_assoc', Measure.compProd_const,
    mixture_compProd_posteriorKernel mu B hB, hp,
    Measure.map_map MeasurableEquiv.prodAssoc.measurable (hY.prodMap measurable_id)]
  rfl

noncomputable def combinedPosteriorWeight (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    (z : D × E) (x : Omega) : ℝ :=
  (combinedLikelihood mu A B z.2 z.1)⁻¹ * (mixtureWeight (B x) z.1 * mixtureWeight (A x) z.2)

noncomputable def combinedPosteriorKernel (mu : Measure Omega) [SFinite mu]
    (A : Omega → E) (B : Omega → D) : Kernel (D × E) Omega :=
  (Kernel.const (D × E) mu).withDensity (fun z x ↦ ENNReal.ofReal (combinedPosteriorWeight mu A B z x))

theorem measurable_combinedPosteriorWeight (mu : Measure Omega) [SFinite mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    Measurable (Function.uncurry (fun z x ↦ ENNReal.ofReal (combinedPosteriorWeight mu A B z x))) := by
  have hZ : Measurable (fun p : (D × E) × Omega ↦ (combinedLikelihood mu A B p.1.2 p.1.1)⁻¹) :=
    (((measurable_combinedLikelihood mu A B hA hB).comp measurable_swap).inv).comp measurable_fst
  have hB' : Measurable (fun p : (D × E) × Omega ↦ mixtureWeight (B p.2) p.1.1) :=
    continuous_mixtureWeight.measurable.comp ((hB.comp measurable_snd).prodMk measurable_fst.fst)
  have hA' : Measurable (fun p : (D × E) × Omega ↦ mixtureWeight (A p.2) p.1.2) :=
    continuous_mixtureWeight.measurable.comp ((hA.comp measurable_snd).prodMk measurable_fst.snd)
  exact (hZ.mul (hB'.mul hA')).ennreal_ofReal

/-- The literal normalized product likelihood agrees with sequential Bayesian
conditioning on the actual two independent Gaussian observations. -/
theorem combinedPosteriorKernel_apply (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (v : D) (y : E) :
    combinedPosteriorKernel mu A B (v,y) = (posteriorKernel mu B v).withDensity
      (fun x ↦ ENNReal.ofReal (posteriorWeight (posteriorKernel mu B v) A y x)) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have h1 : Measurable (fun x ↦ ENNReal.ofReal (posteriorWeight mu B v x)) :=
    Measurable.of_uncurry_left (x := v) (measurable_posteriorWeight mu B hB)
  have h2 : Measurable (fun x ↦ ENNReal.ofReal (posteriorWeight (posteriorKernel mu B v) A y x)) :=
    Measurable.of_uncurry_left (x := y) (measurable_posteriorWeight (posteriorKernel mu B v) A hA)
  rw [combinedPosteriorKernel, Kernel.withDensity_apply _ (measurable_combinedPosteriorWeight mu A B hA hB),
    Kernel.const_apply]
  nth_rw 1 [posteriorKernel_apply mu B hB]
  rw [← withDensity_mul mu h1 h2]
  congr 1
  funext x
  change ENNReal.ofReal (combinedPosteriorWeight mu A B (v,y) x) =
    ENNReal.ofReal (posteriorWeight mu B v x) *
      ENNReal.ofReal (posteriorWeight (posteriorKernel mu B v) A y x)
  rw [← ENNReal.ofReal_mul (posteriorWeight_pos mu B hB v x).le]
  congr 1
  simp only [combinedPosteriorWeight, posteriorWeight, combinedLikelihood_factor mu A B hB,
    mul_inv_rev]
  ring

theorem combinedPosteriorKernel_isMarkov (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    IsMarkovKernel (combinedPosteriorKernel mu A B) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  refine ⟨fun z ↦ ?_⟩
  rcases z with ⟨v,y⟩
  have : IsMarkovKernel (posteriorKernel (posteriorKernel mu B v) A) :=
    posteriorKernel_isMarkov (posteriorKernel mu B v) A hA
  have h : IsProbabilityMeasure (posteriorKernel (posteriorKernel mu B v) A y) := inferInstance
  rw [posteriorKernel_apply (posteriorKernel mu B v) A hA] at h
  rw [combinedPosteriorKernel_apply mu A B hA hB]
  exact h


end TensorPCA.GaussianSideChannelProofs
