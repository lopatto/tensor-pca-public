-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidate
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdInvariance

/-! Exact bounded membership moments under the one selected candidate graph, including
the zero-time physical window observable.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidateMoments
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGThresholdWeights SphericalGGWeightObservable SphericalGGIndicatorTilt
open SphericalGGLastSpinCandidate SphericalGGSelectedCandidate SphericalGGBoundedScoreWeights
open SphericalGGMaskedScoreStability SphericalGGThresholdInvariance
open FiniteGGConditionalLowMass FiniteGGBoundaryBands FiniteGGWindowScalar
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

theorem old_observable_integral_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhiM : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2)) :
    (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v (n+1))=
      ∫ q,Phi (appendLast n q).1.1 (appendLast n q).2 ∂((jointLaw nu v n)⊗ₘlastKernel nu v n) := by
  have HM : Measurable (fun p : ((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1.1 p.2) :=
    hPhiM.comp (measurable_fst.fst.prodMk measurable_snd)
  exact ((appendLast_hasLaw (K := K) nu hv n).integral_comp HM.aestronglyMeasurable).symm

 theorem membership_moment_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    (hCover : (⋃ i,thresholdMasks (K := K) nu v a b eta J P i)=univ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhiM : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2))
    (hPhi : ∀ x old,Phi x old∈Icc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hfM : Measurable f) {C : ℝ} (hf : ∀ z∈Icc (0 : ℝ) 1,|f z|≤C) :
    (∑ i,∫ p,(maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2)*
      f (membershipMass nu v (n+1) (threshold a b J i) p) ∂jointLaw nu v (n+1))=
      ∫ q,Phi (appendLast n q).1.1 (appendLast n q).2*
        f (candidateMass (lastKernel nu v n) (selectedPairSet nu v n a b eta J P) q)
          ∂((jointLaw nu v n)⊗ₘlastKernel nu v n) := by
  let Fi := fun i p ↦ (maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2)*
    f (membershipMass nu v (n+1) (threshold a b J i) p)
  have hpAbs (x) (old) : |Phi x old|≤1 := by
    rw [abs_of_nonneg (hPhi x old).1]; exact (hPhi x old).2
  have hMaskM (i : Fin J) : MeasurableSet (thresholdMasks (K := K) nu v a b eta J P i) := by
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    exact FiniteGGFirstGoodPartition.firstGood_measurable _
      (FiniteGGParameterScorePartition.goodParameter_measurable
        (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
        (SphericalFirstJetPowerBudget.unitOverlap_measurable N) a b J P eta hGlobal) i
  have hFI (i : Fin J) : Integrable (Fi i) (jointLaw nu v (n+1)) := by
    letI := jointLaw_probability nu hv (n+1) (K := K)
    have hM := ((maskedPhi_measurable (hMaskM i) hPhiM).comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hfM.comp (membershipMass_measurable nu hv (n+1) (threshold a b J i)))
    apply Integrable.of_bound hM.aestronglyMeasurable C
    exact Eventually.of_forall (fun p ↦ by
      change ‖Fi i p‖≤C
      rw [Real.norm_eq_abs,abs_mul]
      exact ((mul_le_mul_of_nonneg_right (maskedPhi_abs_le _ zero_le_one hpAbs p.1.1 p.2) (abs_nonneg _)).trans_eq (one_mul _)).trans
        (hf _ (membershipMass_mem nu hv (n+1) (threshold a b J i) p)))
  have hFs : Integrable (fun p ↦ ∑ i,Fi i p) (jointLaw nu v (n+1)) :=
    integrable_finset_sum Finset.univ (fun i _ ↦ hFI i)
  have hLaw := appendLast_hasLaw (K := K) nu hv n
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hFI i)]
  trans ∫ q,(∑ i,Fi i (appendLast n q)) ∂((jointLaw nu v n)⊗ₘlastKernel nu v n)
  · exact (hLaw.integral_comp hFs.aestronglyMeasurable).symm
  · apply integral_congr_ae
    refine Eventually.of_forall (fun q ↦ ?_)
    have hc : (appendLast n q).1.1∈⋃ i,thresholdMasks nu v a b eta J P i := by rw [hCover]; exact mem_univ _
    obtain ⟨i,hi⟩ := mem_iUnion.mp hc
    have hp : q.1∈prefixMasks nu v n a b eta J P i := hi
    have hCan := candidateMass_selected_on_cell nu hv n a b eta J P i q.1 hp q.2
    change candidateMass (lastKernel nu v n) (selectedPairSet nu v n a b eta J P) q=
      membershipMass nu v (n+1) (threshold a b J i) (appendLast n q) at hCan
    have hNot (j : Fin J) (hji : j≠i) : (appendLast n q).1.1∉thresholdMasks nu v a b eta J P j := by
      intro hj
      exact (Set.disjoint_left.mp (FiniteGGFirstGoodPartition.firstGood_disjoint _ hji)) hj hi
    dsimp only
    rw [Finset.sum_eq_single i]
    · simp only [Fi,maskedPhi,if_pos hi,hCan]
    · intro j _ hji
      simp only [Fi,maskedPhi,if_neg (hNot j hji),zero_mul]
    · intro hh
      exact False.elim (hh (Finset.mem_univ i))

 theorem zero_window_eq {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    (hCover : (⋃ i,thresholdMasks (K := K) nu v a b eta J P i)=univ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhiM : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2))
    (hPhi : ∀ x old,Phi x old∈Icc (0 : ℝ) 1) (kappa : ℝ) :
    thresholdWindowSum nu v (n+1) a b eta J P kappa Phi 0=
      ∫ q,Phi (appendLast n q).1.1 (appendLast n q).2*
        window kappa (candidateMass (lastKernel nu v n) (selectedPairSet nu v n a b eta J P) q)
          ∂((jointLaw nu v n)⊗ₘlastKernel nu v n) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have h0 (i : Fin J) (p) :
      scoreIntegrand nu v (n+1) (thresholdScore (n+1) (threshold a b J i))
        (maskedPhi (thresholdMasks nu v a b eta J P i) Phi)
        (fun _ ↦ thresholdMembership (n+1) (threshold a b J i)) (window kappa) 0 p=
      (maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2)*
        window kappa (membershipMass nu v (n+1) (threshold a b J i) p) := by
    unfold scoreIntegrand GGFiniteJointScoreStability.integrand
    rw [GGFiniteReplicaWeightMoments.tiltedWeightMean_zero]
    simp only [GGFiniteReweightingDerivative.reweightingNormalizer,GGFiniteEmpiricalNormalizer.normalizer,
      zero_mul,Real.exp_zero,integral_const,probReal_univ,one_smul,one_pow,mul_one,div_one]
    rfl
  unfold thresholdWindowSum scoreObservable
  simp_rw [h0]
  exact membership_moment_eq nu hv n a b eta J P hGlobal hCover Phi hPhiM hPhi
    (window kappa) (window_continuous kappa).measurable
    (fun z _ ↦ by rw [abs_of_nonneg (window_mem_Icc kappa z).1]; exact (window_mem_Icc kappa z).2)

end
end TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidateMoments
