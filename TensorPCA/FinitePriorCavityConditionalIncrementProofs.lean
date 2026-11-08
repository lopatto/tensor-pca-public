-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityChainRuleProofs
public import TensorPCA.FinitePriorCavityNormalizationProofs
public import TensorPCA.FinitePriorCavityPartitionProofs
public import TensorPCA.GaussianFinitePriorApproximationScalarProofs

/-! The exact conditional free-energy cavity increment for unordered tensor channels. The prior factorization is the finite conditional product identity, allowing a Dirac law for an already revealed last spin. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityConditionalIncrementProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianTwoChannelFreeEnergyProofs GaussianFiberChannelProofs GaussianCompactFeatureComparison
open FinitePriorChannelProofs FinitePriorCavityFieldProofs FinitePriorCavityPartitionProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityComparisonProofs FinitePriorCavityChainRuleProofs
open GaussianFinitePriorApproximationScalarProofs TensorOrbitAggregationProofs TensorOrbitCountProofs
open scoped RealInnerProductSpace ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def diagonalEmbedding {iota : Type*} [Fintype iota] (a b : ℝ) (hab : a^2+b^2 = 1) :
    EuclideanSpace ℝ iota →ₗᵢ[ℝ] EuclideanSpace ℝ (iota ⊕ iota) where
  toFun x := sumJoin (a • x,b • x)
  map_add' x y := by
    change sumJoin (a • (x+y),b • (x+y)) = sumJoin (a • x,b • x)+sumJoin (a • y,b • y)
    rw [← map_add,smul_add,smul_add]
    rfl
  map_smul' c x := by
    change sumJoin (a • (c • x),b • (c • x)) = c • sumJoin (a • x,b • x)
    rw [← map_smul]
    congr 1
    simp only [Prod.smul_mk,smul_smul,mul_comm]
  norm_map' x := by
    classical
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖sumJoin (a • x,b • x)‖^2 = ‖x‖^2
    rw [norm_sumJoin_sq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,mul_pow,mul_pow,sq_abs,sq_abs]
    have H := congrArg (fun r : ℝ ↦ r*‖x‖^2) hab
    nlinarith only [H]

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

def freshSignal (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (z : (Fin N → S) × S) :
    EuclideanSpace ℝ (KSubset N (k-1)) := a z.2 • cavitySignal a N k gamma z.1

omit [Fintype S] [MeasurableSingletonClass S] in
theorem reindexed_tensorSignal_eq_join {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (x : Fin (N+1) → S) :
    disorderReindex hk (tensorSignal a (N+1) k gamma x) =
      joinedSignal (fun z : (Fin N → S) × S ↦ backgroundSignal a N k gamma z.1)
        (freshSignal a N k gamma) (configurationSplit N x) := by
  ext (T | T)
  · have H := congrArg (fun v : EuclideanSpace ℝ (KSubset N k) ↦ v T) (tensorSignal_old hk a gamma x)
    change (disorderReindex hk (tensorSignal a (N+1) k gamma x)) (.inl T) =
      backgroundSignal a N k gamma (oldConfiguration x) T at H
    change (disorderReindex hk (tensorSignal a (N+1) k gamma x)) (.inl T) =
      backgroundSignal a N k gamma (configurationSplit N x).1 T
    rw [configurationSplit_apply]
    exact H
  · have H := congrArg (fun v : EuclideanSpace ℝ (KSubset N (k-1)) ↦ v T) (tensorSignal_last hk a gamma x)
    change (disorderReindex hk (tensorSignal a (N+1) k gamma x)) (.inr T) =
      (a (x (Fin.last N)) • cavitySignal a N k gamma (oldConfiguration x)) T at H
    change (disorderReindex hk (tensorSignal a (N+1) k gamma x)) (.inr T) =
      (a (configurationSplit N x).2 • cavitySignal a N k gamma (configurationSplit N x).1) T
    rw [configurationSplit_apply]
    exact H

omit [Fintype S] [MeasurableSingletonClass S] in
theorem old_joinedSignal_eq_diagonal {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) (x : Fin N → S) :
    joinedSignal (correctionSignal a N k gamma) (backgroundSignal a N k gamma) x =
      diagonalEmbedding (correctionCoefficient N k gamma/aggregateCoefficient N k gamma)
        (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
        (by linarith [normalized_correction_weights hN hk hgamma]) (tensorSignal a N k gamma x) := by
  have hc := (aggregateCoefficient_pos hN hk hgamma).ne'
  change sumJoin (correctionSignal a N k gamma x,backgroundSignal a N k gamma x) =
    sumJoin ((correctionCoefficient N k gamma/aggregateCoefficient N k gamma) • tensorSignal a N k gamma x,
      (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma) • tensorSignal a N k gamma x)
  congr 1
  apply Prod.ext
  · simp_rw [correctionSignal,tensorSignal_eq_monomial,smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hc).symm
  · simp_rw [backgroundSignal_eq_monomial,tensorSignal_eq_monomial,smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hc).symm

theorem old_freeEnergy_eq_twoChannel {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (q : Measure (Fin N → S)) [IsProbabilityMeasure q] (a : S → ℝ) :
    mixtureFreeEnergy q (tensorSignal a N k gamma) =
      twoChannelFreeEnergy q (correctionSignal a N k gamma) (backgroundSignal a N k gamma) := by
  let I : EuclideanSpace ℝ (KSubset N k) →ₗᵢ[ℝ] EuclideanSpace ℝ (KSubset N k ⊕ KSubset N k) :=
    diagonalEmbedding (correctionCoefficient N k gamma/aggregateCoefficient N k gamma)
    (aggregateCoefficient (N+1) k gamma/aggregateCoefficient N k gamma)
    (by linarith [normalized_correction_weights hN hk hgamma])
  have hsig : I ∘ tensorSignal a N k gamma =
      joinedSignal (correctionSignal a N k gamma) (backgroundSignal a N k gamma) := by
    funext x
    exact (old_joinedSignal_eq_diagonal hN hk hgamma a x).symm
  have H := mixtureFreeEnergy_isometricImage q (tensorSignal a N k gamma) (measurable_of_finite _)
    MemLp.of_discrete I
  rw [hsig,mixtureFreeEnergy_joinedSignal q _ _ (measurable_of_finite _) (measurable_of_finite _)] at H
  exact H.symm

theorem full_freeEnergy_eq_twoChannel {N k : ℕ} (hk : 0 < k)
    (qFull : Measure (Fin (N+1) → S)) [IsProbabilityMeasure qFull]
    (qOld : Measure (Fin N → S)) [IsProbabilityMeasure qOld]
    (pLast : Measure S) [IsProbabilityMeasure pLast]
    (hSplit : qFull.map (configurationSplit N) = qOld.prod pLast) (a : S → ℝ) (gamma : ℝ) :
    mixtureFreeEnergy qFull (tensorSignal a (N+1) k gamma) =
      twoChannelFreeEnergy (qOld.prod pLast) (freshSignal a N k gamma)
        (fun z ↦ backgroundSignal a N k gamma z.1) := by
  let F := joinedSignal (fun z : (Fin N → S) × S ↦ backgroundSignal a N k gamma z.1)
    (freshSignal a N k gamma)
  have hsig : (disorderReindex hk).toLinearIsometry ∘ tensorSignal a (N+1) k gamma = F ∘ configurationSplit N := by
    funext x
    exact reindexed_tensorSignal_eq_join hk a gamma x
  have H := mixtureFreeEnergy_isometricImage qFull (tensorSignal a (N+1) k gamma)
    (measurable_of_finite _) MemLp.of_discrete (disorderReindex hk).toLinearIsometry
  rw [hsig] at H
  have hMap := mixtureFreeEnergy_map_prior qFull (configurationSplit N) (configurationSplit N).measurable
    F (measurable_of_finite _)
  rw [hSplit] at hMap
  rw [← hMap] at H
  change mixtureFreeEnergy (qOld.prod pLast)
    (joinedSignal (fun z ↦ backgroundSignal a N k gamma z.1) (freshSignal a N k gamma)) = _ at H
  rw [mixtureFreeEnergy_joinedSignal (qOld.prod pLast) _ _ (measurable_of_finite _) (measurable_of_finite _),
    GaussianTwoStrengthPathProofs.twoChannelFreeEnergy_swap (qOld.prod pLast) _ _
      (measurable_of_finite _) (measurable_of_finite _)] at H
  exact H.symm

/-- Exact conditional increment, for any genuine split prior. The correction
and fresh terms have the same actual background posterior and observation law;
both conditional free energies are integrable. -/
theorem conditional_cavity_increment_formula {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (qFull : Measure (Fin (N+1) → S)) [IsProbabilityMeasure qFull]
    (qOld : Measure (Fin N → S)) [IsProbabilityMeasure qOld]
    (pLast : Measure S) [IsProbabilityMeasure pLast]
    (hSplit : qFull.map (configurationSplit N) = qOld.prod pLast) (a : S → ℝ) :
    Integrable (fun y ↦
      mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
        (freshSignal a N k gamma)-
      mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma))
      (mixtureLaw qOld (backgroundSignal a N k gamma)) ∧
    mixtureFreeEnergy qFull (tensorSignal a (N+1) k gamma)-mixtureFreeEnergy qOld (tensorSignal a N k gamma) =
      ∫ y, mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
        (freshSignal a N k gamma)-
        mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma)
          ∂mixtureLaw qOld (backgroundSignal a N k gamma) := by
  obtain ⟨CA,hCA,hA⟩ := finite_signal_bound (freshSignal a N k gamma)
  obtain ⟨CB,_,hB⟩ := finite_signal_bound (backgroundSignal a N k gamma)
  obtain ⟨CC,hCC,hC⟩ := finite_signal_bound (correctionSignal a N k gamma)
  have hIA := integrable_conditional_prod_mixtureFreeEnergy qOld pLast (freshSignal a N k gamma)
    (backgroundSignal a N k gamma) (measurable_of_finite _) (measurable_of_finite _) (.of_forall hA)
  have hIC := integrable_conditional_mixtureFreeEnergy qOld (correctionSignal a N k gamma)
    (backgroundSignal a N k gamma) (measurable_of_finite _) (measurable_of_finite _) (.of_forall hC)
  refine ⟨hIA.sub hIC,?_⟩
  rw [full_freeEnergy_eq_twoChannel hk qFull qOld pLast hSplit a gamma,
    old_freeEnergy_eq_twoChannel hN hk hgamma qOld a,
    twoChannelFreeEnergy_prod_background qOld pLast _ _ (measurable_of_finite _) (measurable_of_finite _)
      hCA (.of_forall hA) (.of_forall hB),
    twoChannelFreeEnergy_eq_conditional qOld _ _ (measurable_of_finite _) (measurable_of_finite _)
      hCC (.of_forall hC) (.of_forall hB),
    integral_sub hIA hIC]
  ring

end
end TensorPCA.FinitePriorCavityConditionalIncrementProofs
