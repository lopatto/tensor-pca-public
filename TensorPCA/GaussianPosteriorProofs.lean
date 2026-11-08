-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMixtureStabilityProofs
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Posterior kernel for a general Gaussian signal prior

The prior need not have a constant signal norm. Every observation has a strictly
positive mixture likelihood, and the normalized full likelihood defines a Markov kernel reconstructing the latent/output joint law.
-/
@[expose] public section

namespace TensorPCA.GaussianPosteriorProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs
open scoped ENNReal RealInnerProductSpace ProbabilityTheory

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def posteriorWeight (mu : Measure Omega) (F : Omega → E) (y : E) (x : Omega) : ℝ :=
  (mixtureLikelihood mu F y)⁻¹ * mixtureWeight (F x) y

noncomputable def posteriorKernel (mu : Measure Omega) [SFinite mu] (F : Omega → E) : Kernel E Omega :=
  (Kernel.const E mu).withDensity (fun y x ↦ ENNReal.ofReal (posteriorWeight mu F y x))

theorem measurable_posteriorWeight (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    Measurable (Function.uncurry (fun y x ↦ ENNReal.ofReal (posteriorWeight mu F y x))) := by
  have hL : Measurable (fun z : E × Omega ↦ (mixtureLikelihood mu F z.1)⁻¹) :=
    (measurable_mixtureLikelihood mu F hF).inv.comp measurable_fst
  have hW : Measurable (fun z : E × Omega ↦ mixtureWeight (F z.2) z.1) :=
    continuous_mixtureWeight.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)
  exact (hL.mul hW).ennreal_ofReal

theorem posteriorWeight_pos (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) (x : Omega) :
    0 < posteriorWeight mu F y x :=
  mul_pos (inv_pos.mpr (mixtureLikelihood_pos mu F hF y)) (mixtureWeight_pos (F x) y)

theorem integrable_posteriorWeight (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) : Integrable (posteriorWeight mu F y) mu :=
  (integrable_mixtureWeight mu F hF y).const_mul _

theorem integral_posteriorWeight (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) : (∫ x, posteriorWeight mu F y x ∂mu) = 1 := by
  unfold posteriorWeight
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (mixtureLikelihood_pos mu F hF y).ne'

theorem posteriorKernel_apply (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) (y : E) :
    posteriorKernel mu F y = mu.withDensity (fun x ↦ ENNReal.ofReal (posteriorWeight mu F y x)) := by
  rw [posteriorKernel, Kernel.withDensity_apply _ (measurable_posteriorWeight mu F hF), Kernel.const_apply]

theorem posteriorKernel_isMarkov (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) : IsMarkovKernel (posteriorKernel mu F) := by
  refine ⟨fun y ↦ ⟨?_⟩⟩
  rw [posteriorKernel_apply mu F hF, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_posteriorWeight mu F hF y)
      (.of_forall fun x ↦ (posteriorWeight_pos mu F hF y x).le), integral_posteriorWeight mu F hF y]
  simp

theorem observedLatent_eq_withDensity (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    (mu.prod (stdGaussian E)).map (fun z ↦ (F z.1+z.2, z.1)) =
      ((stdGaussian E).prod mu).withDensity (fun z ↦ ENNReal.ofReal (mixtureWeight (F z.2) z.1)) := by
  have hObs : Measurable (fun z : Omega × E ↦ (z.1, F z.1+z.2)) :=
    measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
  have hW : Measurable (fun z : Omega × E ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) :=
    (continuous_mixtureWeight.measurable.comp ((hF.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have h := GaussianChannelProofs.map_withDensity_equiv
    (MeasurableEquiv.prodComm : Omega × E ≃ᵐ E × Omega) (mu.prod (stdGaussian E))
    (fun z ↦ ENNReal.ofReal (mixtureWeight (F z.1) z.2)) hW
  rw [← jointLaw_eq_withDensity mu F hF, jointLaw,
    Measure.map_map MeasurableEquiv.prodComm.measurable hObs] at h
  change (mu.prod (stdGaussian E)).map (fun z ↦ (F z.1+z.2, z.1)) =
    ((mu.prod (stdGaussian E)).map Prod.swap).withDensity
      (fun z ↦ ENNReal.ofReal (mixtureWeight (F z.2) z.1)) at h
  simpa only [Measure.prod_swap] using h

theorem mixture_compProd_posteriorKernel (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → E) (hF : Measurable F) :
    (mixtureLaw mu F) ⊗ₘ posteriorKernel mu F =
      (mu.prod (stdGaussian E)).map (fun z ↦ (F z.1+z.2, z.1)) := by
  have : IsMarkovKernel ((Kernel.const E mu).withDensity
      (fun y x ↦ ENNReal.ofReal (posteriorWeight mu F y x))) := posteriorKernel_isMarkov mu F hF
  rw [mixtureLaw_eq_withDensity mu F hF, posteriorKernel,
    Measure.withDensity_compProd_withDensity (measurable_mixtureLikelihood mu F hF).ennreal_ofReal
      (measurable_posteriorWeight mu F hF), Measure.compProd_const, observedLatent_eq_withDensity mu F hF]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (mixtureLikelihood_pos mu F hF z.1).le]
  congr 1
  rw [posteriorWeight, ← mul_assoc, mul_inv_cancel₀ (mixtureLikelihood_pos mu F hF z.1).ne', one_mul]

noncomputable def posteriorMean {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (mu : Measure Omega) [SFinite mu] (F : Omega → E) (a : Omega → V) (y : E) : V :=
  ∫ x, a x ∂posteriorKernel mu F y

/-- The explicit likelihood posterior computes the actual conditional mean
given the actual observation sigma-algebra, with no point-event conditioning. -/
theorem posteriorMean_ae_eq_condExp [StandardBorelSpace Omega]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) (ha : StronglyMeasurable a) (haInt : Integrable a mu) :
    (fun z : Omega × E ↦ posteriorMean mu F a (F z.1+z.2)) =ᵐ[mu.prod (stdGaussian E)]
      (mu.prod (stdGaussian E))[fun z ↦ a z.1 |
        MeasurableSpace.comap (fun z : Omega × E ↦ F z.1+z.2) (inferInstance : MeasurableSpace E)] := by
  have : Nonempty Omega := nonempty_of_isProbabilityMeasure mu
  have : IsMarkovKernel (posteriorKernel mu F) := posteriorKernel_isMarkov mu F hF
  have hObs : Measurable (fun z : Omega × E ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  have hK := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hObs measurable_fst
    (mixture_compProd_posteriorKernel mu F hF).symm
  have hce := condExp_ae_eq_integral_condDistrib hObs measurable_fst.aemeasurable ha
    (haInt.comp_fst (stdGaussian E))
  have hk := ae_of_ae_map hObs.aemeasurable hK
  filter_upwards [hce, hk] with z hcz hkz
  rw [hcz, hkz]
  rfl

/-- The genuine posterior projection/Nishimori second-moment identity for any
square-integrable observable of the actual prior. Unit signal norms are not
assumed. Nonemptiness is derived from the probability prior in the CE bridge. -/
theorem integral_latent_inner_posteriorMean [StandardBorelSpace Omega]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Omega → E) (hF : Measurable F)
    (a : Omega → V) (ha : StronglyMeasurable a) (ha2 : MemLp a 2 mu) :
    (∫ z : Omega × E, inner ℝ (a z.1) (posteriorMean mu F a (F z.1+z.2))
      ∂mu.prod (stdGaussian E)) =
      ∫ z : Omega × E, ‖posteriorMean mu F a (F z.1+z.2)‖ ^ 2 ∂mu.prod (stdGaussian E) := by
  let obs : Omega × E → E := fun z ↦ F z.1+z.2
  let base := mu.prod (stdGaussian E)
  let A : Omega × E → V := fun z ↦ a z.1
  let C : Omega × E → V := base[A | MeasurableSpace.comap obs (inferInstance : MeasurableSpace E)]
  have hObs : Measurable obs := (hF.comp measurable_fst).add measurable_snd
  have hm : MeasurableSpace.comap obs (inferInstance : MeasurableSpace E) ≤
      (inferInstance : MeasurableSpace (Omega × E)) := hObs.comap_le
  have hA2 : MemLp A 2 base := ha2.comp_fst (stdGaussian E)
  have hC2 : MemLp C 2 base := hA2.condExp (by norm_num)
  have hCross : Integrable (fun z ↦ inner ℝ (A z) (C z)) base := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hA2.toLp A) (hC2.toLp C)).congr
    filter_upwards [hA2.coeFn_toLp, hC2.coeFn_toLp] with z hAz hCz
    rw [hAz, hCz]
  have hpull := condExp_bilin_of_stronglyMeasurable_right (innerSL ℝ)
    (show StronglyMeasurable[MeasurableSpace.comap obs (inferInstance : MeasurableSpace E)] C
      from stronglyMeasurable_condExp) hCross
    (hA2.integrable (by norm_num))
  have hCE : (∫ z, inner ℝ (A z) (C z) ∂base) = ∫ z, ‖C z‖ ^ 2 ∂base := by
    calc
      _ = ∫ z, base[fun z ↦ inner ℝ (A z) (C z) |
          MeasurableSpace.comap obs (inferInstance : MeasurableSpace E)] z ∂base :=
        (integral_condExp (μ := base) (f := fun z ↦ inner ℝ (A z) (C z)) hm).symm
      _ = ∫ z, inner ℝ (C z) (C z) ∂base := integral_congr_ae hpull
      _ = _ := by simp only [real_inner_self_eq_norm_sq]
  have hMean := posteriorMean_ae_eq_condExp mu F hF a ha (ha2.integrable (by norm_num))
  calc
    _ = ∫ z, inner ℝ (A z) (C z) ∂base := by
      apply integral_congr_ae
      filter_upwards [hMean] with z hz
      rw [hz]
    _ = ∫ z, ‖C z‖ ^ 2 ∂base := hCE
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hMean] with z hz
      rw [hz]


end TensorPCA.GaussianPosteriorProofs
