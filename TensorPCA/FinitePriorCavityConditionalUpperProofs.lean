-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityScalarErrorProofs
public import TensorPCA.FinitePriorCavityConditionalIncrementProofs
public import TensorPCA.FinitePriorScalarDomainProofs
public import TensorPCA.GaussianRevealVarianceProofs

/-! The conditional physical increment is bounded by the scalar potential averaged under the same background observation law. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityConditionalUpperProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorScalarDomainProofs FinitePriorCavityFieldProofs
open FinitePriorCavityPartitionProofs FinitePriorCavityConditionalIncrementProofs
open FinitePriorCavityScalarErrorProofs GaussianRevealVarianceProofs PosteriorPairProofs
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S Y : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableSpace Y] {N : ℕ}

theorem measurable_meanOverlap (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa] (a : S → ℝ) :
    Measurable (fun y ↦ meanOverlap (kappa y) a) := by
  unfold meanOverlap
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_of_finite (fun x : Fin N → S ↦ a (x i))).stronglyMeasurable.integral_kernel.measurable).pow_const 2

theorem integrable_scalarPotential_meanOverlap (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa]
    (nu : Measure Y) [IsFiniteMeasure nu] (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (k : ℕ) (gamma : ℝ) (hN : 0 < N) {K : ℝ} (hb : ∀ s, |a s| ≤ K) :
    Integrable (fun y ↦ scalarPotential p a k gamma (meanOverlap (kappa y) a)) nu := by
  have hm := (continuous_scalarPotential p a k gamma).measurable.comp (measurable_meanOverlap kappa a)
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (K^2))).bddAbove_image
    (continuous_scalarPotential p a k gamma).norm.continuousOn
  apply Integrable.of_bound hm.aestronglyMeasurable B
  exact .of_forall fun y ↦ hB ⟨meanOverlap (kappa y) a,
    ⟨meanOverlap_nonneg _ a,GuerraRemainderProofs.meanOverlap_le _ a hN hb⟩,rfl⟩

theorem integrable_sqrt_replicaVariance (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa]
    (nu : Measure Y) [IsFiniteMeasure nu] (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    Integrable (fun y ↦ Real.sqrt (replicaVariance (kappa y) a)) nu := by
  apply Integrable.of_bound ((measurable_replicaVariance kappa a).sqrt.aestronglyMeasurable)
    (Real.sqrt (4*K^4))
  exact .of_forall fun y ↦ by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (replicaVariance_bounds (kappa y) a hN hK hb).2

/-- A genuine conditional increment bound for any correctly split prior.
The scalar mean and the variance use exactly the same background posterior. -/
theorem exists_conditional_increment_upper_constant (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k)
    {gamma K : ℝ} (hgamma : 0 < gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N →
      ∀ (qFull : Measure (Fin (N+1) → S)) [IsProbabilityMeasure qFull]
        (qOld : Measure (Fin N → S)) [IsProbabilityMeasure qOld]
        (pLast : Measure S) [IsProbabilityMeasure pLast],
        qFull.map (configurationSplit N) = qOld.prod pLast →
      mixtureFreeEnergy qFull (tensorSignal a (N+1) k gamma)-
        mixtureFreeEnergy qOld (tensorSignal a N k gamma) ≤
      (∫ y, scalarPotential pLast a k gamma
          (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
          ∂mixtureLaw qOld (backgroundSignal a N k gamma))+
        C*(1/(N : ℝ)+∫ y, Real.sqrt (replicaVariance
          (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
          ∂mixtureLaw qOld (backgroundSignal a N k gamma)) := by
  obtain ⟨C,hC,hbound⟩ := exists_conditional_scalar_error_constant a hk hgamma.le hK hb
  refine ⟨C,hC,?_⟩
  intro N hN qFull _ qOld _ pLast _ hSplit
  have hBG : Measurable (backgroundSignal a N k gamma) := measurable_of_finite _
  have : IsMarkovKernel (posteriorKernel qOld (backgroundSignal a N k gamma)) :=
    posteriorKernel_isMarkov qOld _ hBG
  have : IsProbabilityMeasure (mixtureLaw qOld (backgroundSignal a N k gamma)) := mixtureLaw_probability qOld _ hBG
  have hP := integrable_scalarPotential_meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma))
    (mixtureLaw qOld (backgroundSignal a N k gamma)) pLast a k gamma hN hb
  have hV := integrable_sqrt_replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma))
    (mixtureLaw qOld (backgroundSignal a N k gamma)) a hN hK hb
  obtain ⟨hI,hEq⟩ := conditional_cavity_increment_formula (k := k) hN (by omega) hgamma qFull qOld pLast hSplit a
  rw [hEq]
  have H := integral_mono_ae hI (hP.add (((integrable_const (1/(N : ℝ))).add hV).const_mul C))
    (.of_forall fun y ↦ hbound N hN (posteriorKernel qOld (backgroundSignal a N k gamma) y) pLast)
  change _ ≤ ∫ y, scalarPotential pLast a k gamma
    (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)+
    C*(1/(N : ℝ)+Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a))
    ∂mixtureLaw qOld (backgroundSignal a N k gamma) at H
  have hR : Integrable (fun y ↦ C*(1/(N : ℝ)+Real.sqrt
    (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)))
    (mixtureLaw qOld (backgroundSignal a N k gamma)) := ((integrable_const (1/(N : ℝ))).add hV).const_mul C
  rw [integral_add hP hR,integral_const_mul,integral_add (integrable_const (1/(N : ℝ))) hV,
    integral_const,probReal_univ,one_smul] at H
  exact H

end
end TensorPCA.FinitePriorCavityConditionalUpperProofs
