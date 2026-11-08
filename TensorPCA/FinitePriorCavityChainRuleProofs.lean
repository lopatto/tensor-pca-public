-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityComparisonProofs
public import TensorPCA.SphericalGaussianTransferProofs

/-! Channel chain rules for a common background and a fresh
independent prior coordinate. These are finite identities, without a cavity
increment bound, concentration assumption, or asymptotic premise. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityChainRuleProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs GaussianTwoChannelFreeEnergyProofs
open FinitePriorCavityComparisonProofs GaussianCompactFeatureComparison
open scoped RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega S E : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem mixtureLaw_prod_fst (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (B : Omega → E) (hB : Measurable B) :
    mixtureLaw (q.prod p) (fun z ↦ B z.1) = mixtureLaw q B := by
  have H := SphericalGaussianTransferProofs.mixtureLaw_map_prior (q.prod p) Prod.fst measurable_fst B hB
  simpa only [Measure.map_fst_prod,measure_univ,one_smul,Function.comp_def] using H.symm

theorem mixtureFreeEnergy_prod_fst (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (B : Omega → E) (hB : Measurable B) :
    mixtureFreeEnergy (q.prod p) (fun z ↦ B z.1) = mixtureFreeEnergy q B := by
  unfold mixtureFreeEnergy
  rw [mixtureLaw_prod_fst q p B hB]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mixtureLikelihood_prod_fst (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (B : Omega → E) (y : E) :
    mixtureLikelihood (q.prod p) (fun z ↦ B z.1) y = mixtureLikelihood q B y := by
  unfold mixtureLikelihood
  dsimp only
  simpa only [probReal_univ,one_smul] using
    (integral_fun_fst (μ := q) (ν := p) (fun x : Omega ↦ mixtureWeight (B x) y))

theorem posteriorKernel_prod_fst (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (B : Omega → E) (hB : Measurable B) (y : E) :
    posteriorKernel (q.prod p) (fun z ↦ B z.1) y = (posteriorKernel q B y).prod p := by
  have hW : Measurable (fun x : Omega ↦ ENNReal.ofReal (posteriorWeight q B y x)) := by
    simpa only [Function.comp_def,Function.uncurry_apply_pair,id_eq] using
      (measurable_posteriorWeight q B hB).comp (measurable_const.prodMk measurable_id)
  have hBF : Measurable (fun z : Omega × S ↦ B z.1) := hB.comp measurable_fst
  rw [posteriorKernel_apply (q.prod p) (fun z ↦ B z.1) hBF y,posteriorKernel_apply q B hB,
    prod_withDensity_left hW]
  congr 1
  funext z
  simp only [posteriorWeight,mixtureLikelihood_prod_fst]

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]

theorem mixtureFreeEnergy_joinedSignal (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) :
    mixtureFreeEnergy mu (joinedSignal A B) = twoChannelFreeEnergy mu A B := by
  let F := joinedSignal A B
  have hF : Measurable F := measurable_joinedSignal A B hA hB
  have hObs : Measurable (fun z : Omega × EuclideanSpace ℝ (iota ⊕ kappa) ↦ F z.1+z.2) :=
    (hF.comp measurable_fst).add measurable_snd
  have hL : Measurable (fun z : Omega × EuclideanSpace ℝ (iota ⊕ kappa) ↦
      Real.log (mixtureLikelihood mu F (F z.1+z.2))) :=
    ((measurable_mixtureLikelihood mu F hF).log).comp hObs
  have hMap : Measurable (fun z : (Omega × EuclideanSpace ℝ kappa) × EuclideanSpace ℝ iota ↦
      (z.1.1,joinedOutput (z.1.2,z.2))) :=
    measurable_fst.fst.prodMk
      (continuous_joinedOutput.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  rw [mixtureFreeEnergy_eq_integral_experiment mu F hF,← joinedExperiment_gaussian_map mu,
    integral_map hMap.aemeasurable hL.aestronglyMeasurable]
  unfold twoChannelFreeEnergy
  apply integral_congr_ae
  exact .of_forall fun z ↦ by
    dsimp only [F]
    have he : joinedSignal A B z.1.1+joinedOutput (z.1.2,z.2) =
        joinedOutput (B z.1.1+z.1.2,A z.1.1+z.2) := by
      change sumJoin (A z.1.1,B z.1.1)+sumJoin (z.2,z.1.2) = _
      rw [← map_add]
      rfl
    rw [he,mixtureLikelihood_join]

omit [DecidableEq iota] in
theorem twoChannelFreeEnergy_prod_background
    (q : Measure Omega) [IsProbabilityMeasure q] (p : Measure S) [IsProbabilityMeasure p]
    (A : Omega × S → EuclideanSpace ℝ iota) (B : Omega → E)
    (hA : Measurable A) (hB : Measurable B) {CA CB : ℝ} (hCA : 0 ≤ CA)
    (hbA : ∀ᵐ z ∂q.prod p, ‖A z‖ ≤ CA) (hbB : ∀ᵐ x ∂q, ‖B x‖ ≤ CB) :
    twoChannelFreeEnergy (q.prod p) A (fun z ↦ B z.1) = mixtureFreeEnergy q B+
      ∫ y, mixtureFreeEnergy ((posteriorKernel q B y).prod p) A ∂mixtureLaw q B := by
  rw [twoChannelFreeEnergy_eq_conditional (q.prod p) A (fun z ↦ B z.1)
    hA (hB.comp measurable_fst) hCA hbA (Measure.quasiMeasurePreserving_fst.ae hbB),
    mixtureFreeEnergy_prod_fst q p B hB,mixtureLaw_prod_fst q p B hB]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun y ↦ by
    dsimp only
    rw [posteriorKernel_prod_fst q p B hB y]

omit [DecidableEq iota] in
theorem integrable_conditional_mixtureFreeEnergy
    (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → E)
    (hA : Measurable A) (hB : Measurable B) {C : ℝ} (hbA : ∀ᵐ x ∂q, ‖A x‖ ≤ C) :
    Integrable (fun y ↦ mixtureFreeEnergy (posteriorKernel q B y) A) (mixtureLaw q B) := by
  have : IsProbabilityMeasure (mixtureLaw q B) := mixtureLaw_probability q B hB
  have H : Integrable (GaussianConditionalChannelDerivativeProofs.conditionalFreeEnergy q A B 1)
      (mixtureLaw q B) := by
    apply Integrable.of_bound
      (GaussianConditionalChannelDerivativeProofs.measurable_conditionalFreeEnergy q A B hA hB 1).aestronglyMeasurable
      (C^2/2)
    exact .of_forall fun y ↦ by
      have hb := GaussianConditionalChannelDerivativeProofs.conditionalFreeEnergy_bounds q A B hA hB hbA 1 y
      rw [Real.norm_of_nonneg hb.1]
      simpa only [one_pow,one_mul] using hb.2
  apply H.congr
  exact .of_forall fun y ↦ by
    unfold GaussianConditionalChannelDerivativeProofs.conditionalFreeEnergy
    congr 1
    funext x
    exact one_smul ℝ (A x)

omit [DecidableEq iota] in
theorem integrable_conditional_prod_mixtureFreeEnergy
    (q : Measure Omega) [IsProbabilityMeasure q] (p : Measure S) [IsProbabilityMeasure p]
    (A : Omega × S → EuclideanSpace ℝ iota) (B : Omega → E)
    (hA : Measurable A) (hB : Measurable B) {C : ℝ} (hbA : ∀ᵐ z ∂q.prod p, ‖A z‖ ≤ C) :
    Integrable (fun y ↦ mixtureFreeEnergy ((posteriorKernel q B y).prod p) A) (mixtureLaw q B) := by
  have H := integrable_conditional_mixtureFreeEnergy (q.prod p) A (fun z ↦ B z.1)
    hA (hB.comp measurable_fst) hbA
  rw [mixtureLaw_prod_fst q p B hB] at H
  apply H.congr
  exact .of_forall fun y ↦ by
    dsimp only
    rw [posteriorKernel_prod_fst q p B hB y]

end
end TensorPCA.FinitePriorCavityChainRuleProofs
