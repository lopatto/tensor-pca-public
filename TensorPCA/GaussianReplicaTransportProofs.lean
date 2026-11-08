-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianTwoStrengthPathProofs

/-! # A common full posterior law for the two Guerra derivative terms -/
@[expose] public section

namespace TensorPCA.GaussianReplicaTransportProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianPosteriorCovarianceProofs GaussianSideChannelProofs GaussianTwoStrengthPathProofs
open scoped RealInnerProductSpace

variable {Omega E D V : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def pairObservationLaw (mu : Measure Omega) (A : Omega → E) (B : Omega → D) : Measure (D × E) :=
  ((mu.prod (stdGaussian D)).prod (stdGaussian E)).map
    (fun z ↦ (B z.1.1+z.1.2,A z.1.1+z.2))

noncomputable def combinedMean (mu : Measure Omega) [SFinite mu] (A : Omega → E) (B : Omega → D)
    (C : Omega → V) (p : D × E) : V := ∫ x, C x ∂combinedPosteriorKernel mu A B p

omit [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ D] [BorelSpace D] in
theorem stronglyMeasurable_combinedMean (mu : Measure Omega) [SFinite mu]
    (A : Omega → E) (B : Omega → D) (C : Omega → V) (hC : StronglyMeasurable C) :
    StronglyMeasurable (combinedMean mu A B C) := hC.integral_kernel

theorem norm_combinedMean_le (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (C : Omega → V) {K : ℝ} (hCB : ∀ᵐ x ∂mu, ‖C x‖ ≤ K) (p : D × E) :
    ‖combinedMean mu A B C p‖ ≤ K := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  rcases p with ⟨v,y⟩
  rw [combinedMean, combinedPosteriorKernel_apply mu A B hA hB,
    ← posteriorKernel_apply (posteriorKernel mu B v) A hA]
  exact norm_posteriorMean_le (posteriorKernel mu B v) A hA C
    ((posteriorKernel_absolutelyContinuous mu B hB v).ae_le hCB) y

theorem integrable_combinedMean_secondMoment_side (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (C : Omega → V) (hC : StronglyMeasurable C) {K : ℝ} (hCB : ∀ᵐ x ∂mu, ‖C x‖ ≤ K) :
    Integrable (fun p : D × (Omega × E) ↦ ‖combinedMean mu A B C (p.1,A p.2.1+p.2.2)‖^2)
      ((mixtureLaw mu B) ⊗ₘ (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E))) := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have hObs : Measurable (fun p : D × (Omega × E) ↦ (p.1,A p.2.1+p.2.2)) :=
    measurable_fst.prodMk ((hA.comp measurable_snd.fst).add measurable_snd.snd)
  have hm := ((stronglyMeasurable_combinedMean mu A B C hC).comp_measurable hObs).norm.measurable.pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable (K^2)
  exact .of_forall fun p ↦ by
    change ‖‖combinedMean mu A B C (p.1,A p.2.1+p.2.2)‖^2‖ ≤ K^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_combinedMean_le mu A B hA hB C hCB _) 2

/-- The averaged conditional experiment is exactly the actual pair-output law
when the integrand is a full-posterior moment. -/
theorem combinedMean_secondMoment_transport (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (C : Omega → V) (hC : StronglyMeasurable C) {K : ℝ} (hCB : ∀ᵐ x ∂mu, ‖C x‖ ≤ K) :
    (∫ v, ∫ z : Omega × E, ‖combinedMean mu A B C (v,A z.1+z.2)‖^2
      ∂(posteriorKernel mu B v).prod (stdGaussian E) ∂mixtureLaw mu B) =
      ∫ p, ‖combinedMean mu A B C p‖^2 ∂pairObservationLaw mu A B := by
  have : IsMarkovKernel (posteriorKernel mu B) := posteriorKernel_isMarkov mu B hB
  have : IsProbabilityMeasure (mixtureLaw mu B) := mixtureLaw_probability mu B hB
  have hm := (stronglyMeasurable_combinedMean mu A B C hC).norm.measurable.pow_const 2
  have hSideObs : Measurable (fun p : D × (Omega × E) ↦ (p.1,A p.2.1+p.2.2)) :=
    measurable_fst.prodMk ((hA.comp measurable_snd.fst).add measurable_snd.snd)
  have hSideMeas : Measurable (fun p : D × (Omega × E) ↦ ‖combinedMean mu A B C (p.1,A p.2.1+p.2.2)‖^2) :=
    hm.comp hSideObs
  have hM : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,(z.1.1,z.2))) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk (measurable_fst.fst.prodMk measurable_snd)
  have hObs : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,A z.1.1+z.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk ((hA.comp measurable_fst.fst).add measurable_snd)
  have hInt := integrable_combinedMean_secondMoment_side mu A B hA hB C hC hCB
  calc
    _ = ∫ p : D × (Omega × E), ‖combinedMean mu A B C (p.1,A p.2.1+p.2.2)‖^2
        ∂(mixtureLaw mu B) ⊗ₘ (posteriorKernel mu B ×ₖ Kernel.const D (stdGaussian E)) := by
      rw [Measure.integral_compProd hInt]
      simp only [Kernel.prod_apply, Kernel.const_apply]
    _ = ∫ z : (Omega × D) × E, ‖combinedMean mu A B C (B z.1.1+z.1.2,A z.1.1+z.2)‖^2
        ∂(mu.prod (stdGaussian D)).prod (stdGaussian E) := by
      rw [sideExperiment_eq_actualLaw mu B hB, integral_map hM.aemeasurable hSideMeas.aestronglyMeasurable]
    _ = _ := (integral_map hObs.aemeasurable hm.aestronglyMeasurable).symm

theorem combinedPosteriorKernel_swap (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (p : D × E) :
    combinedPosteriorKernel mu A B p = combinedPosteriorKernel mu B A p.swap := by
  rw [combinedPosteriorKernel, Kernel.withDensity_apply _ (measurable_combinedPosteriorWeight mu A B hA hB),
    Kernel.const_apply]
  rw [combinedPosteriorKernel, Kernel.withDensity_apply _ (measurable_combinedPosteriorWeight mu B A hB hA),
    Kernel.const_apply]
  congr 1
  funext x
  simp only [combinedPosteriorWeight, Prod.fst_swap, Prod.snd_swap]
  rw [combinedLikelihood_swap mu A B p.2 p.1,
    mul_comm (mixtureWeight (B x) p.1) (mixtureWeight (A x) p.2)]

theorem pairObservationLaw_swap (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) :
    (pairObservationLaw mu A B).map Prod.swap = pairObservationLaw mu B A := by
  have hSwap : MeasurePreserving (fun z : (Omega × D) × E ↦ ((z.1.1,z.2),z.1.2))
      ((mu.prod (stdGaussian D)).prod (stdGaussian E))
      ((mu.prod (stdGaussian E)).prod (stdGaussian D)) := by
    convert ((measurePreserving_prodAssoc mu (stdGaussian E) (stdGaussian D)).symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id mu).prod (Measure.measurePreserving_swap (μ := stdGaussian D) (ν := stdGaussian E))).comp
        (measurePreserving_prodAssoc mu (stdGaussian D) (stdGaussian E))) using 1
    rfl
  have hObsAB : Measurable (fun z : (Omega × D) × E ↦ (B z.1.1+z.1.2,A z.1.1+z.2)) :=
    ((hB.comp measurable_fst.fst).add measurable_fst.snd).prodMk ((hA.comp measurable_fst.fst).add measurable_snd)
  have hObsBA : Measurable (fun z : (Omega × E) × D ↦ (A z.1.1+z.1.2,B z.1.1+z.2)) :=
    ((hA.comp measurable_fst.fst).add measurable_fst.snd).prodMk ((hB.comp measurable_fst.fst).add measurable_snd)
  change (((mu.prod (stdGaussian D)).prod (stdGaussian E)).map _).map Prod.swap =
    ((mu.prod (stdGaussian E)).prod (stdGaussian D)).map _
  rw [Measure.map_map measurable_swap hObsAB, ← hSwap.map_eq,
    Measure.map_map hObsBA hSwap.measurable]
  rfl

theorem swapped_combinedMean_secondMoment (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (C : Omega → V) (hC : StronglyMeasurable C) :
    (∫ p, ‖combinedMean mu B A C p‖^2 ∂pairObservationLaw mu B A) =
      ∫ p, ‖combinedMean mu A B C p‖^2 ∂pairObservationLaw mu A B := by
  have hm := (stronglyMeasurable_combinedMean mu B A C hC).norm.measurable.pow_const 2
  rw [← pairObservationLaw_swap mu A B hA hB, integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun p ↦ by
    change ‖∫ x, C x ∂combinedPosteriorKernel mu B A p.swap‖^2 = _
    rw [← combinedPosteriorKernel_swap mu A B hA hB p]
    rfl

theorem conditionalPosteriorSecondMoment_eq_pairMoment {iota : Type*} [Fintype iota]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    {K : ℝ} (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ K) (lam : ℝ) :
    (∫ v, GaussianConditionalChannelDerivativeProofs.conditionalPosteriorSecondMoment mu A B lam v
      ∂mixtureLaw mu B) =
      ∫ p, ‖combinedMean mu (fun x ↦ lam • A x) B A p‖^2
        ∂pairObservationLaw mu (fun x ↦ lam • A x) B :=
  combinedMean_secondMoment_transport mu (fun x ↦ lam • A x) B
    ((continuous_const_smul lam).measurable.comp hA) hB A hA.stronglyMeasurable hAB

theorem hasDerivAt_guerraPath_commonPosterior {iota kappa : Type*} [Fintype iota] [Fintype kappa]
    [StandardBorelSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → EuclideanSpace ℝ iota) (B : Omega → EuclideanSpace ℝ kappa)
    (hA : Measurable A) (hB : Measurable B) {KA KB : ℝ} (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAB : ∀ᵐ x ∂mu, ‖A x‖ ≤ KA) (hBB : ∀ᵐ x ∂mu, ‖B x‖ ≤ KB)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun u ↦ GaussianTwoChannelFreeEnergyProofs.twoChannelFreeEnergy mu
        (fun x ↦ Real.sqrt u • A x) (fun x ↦ Real.sqrt (1-u) • B x))
      ((1/2:ℝ) * ∫ p, ‖combinedMean mu (fun x ↦ Real.sqrt t • A x)
          (fun x ↦ Real.sqrt (1-t) • B x) A p‖^2
          ∂pairObservationLaw mu (fun x ↦ Real.sqrt t • A x) (fun x ↦ Real.sqrt (1-t) • B x) -
       (1/2:ℝ) * ∫ p, ‖combinedMean mu (fun x ↦ Real.sqrt t • A x)
          (fun x ↦ Real.sqrt (1-t) • B x) B p‖^2
          ∂pairObservationLaw mu (fun x ↦ Real.sqrt t • A x) (fun x ↦ Real.sqrt (1-t) • B x)) t := by
  have hAt : Measurable (fun x ↦ Real.sqrt t • A x) := (continuous_const_smul _).measurable.comp hA
  have hBt : Measurable (fun x ↦ Real.sqrt (1-t) • B x) := (continuous_const_smul _).measurable.comp hB
  have h := hasDerivAt_guerraPath mu A B hA hB hKA hKB hAB hBB ht0 ht1
  rw [conditionalPosteriorSecondMoment_eq_pairMoment mu A _ hA hBt hAB,
    conditionalPosteriorSecondMoment_eq_pairMoment mu B _ hB hAt hBB,
    swapped_combinedMean_secondMoment mu _ _ hAt hBt B hB.stronglyMeasurable] at h
  exact h


end TensorPCA.GaussianReplicaTransportProofs
