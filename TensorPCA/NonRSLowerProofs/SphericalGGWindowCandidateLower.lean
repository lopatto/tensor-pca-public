-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidateMoments
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentUniform
public import TensorPCA.NonRSLowerProofs.FiniteGGWeightedConditionalWindow

/-! Zero-time window lower bound from the uniform threshold GG first moment and the same
single candidate bad-pair mass.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateLower
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGWeightObservable
open SphericalGGIndicatorTilt SphericalGGLastSpinCandidate SphericalGGSelectedCandidate
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability SphericalGGThresholdInvariance
open SphericalGGSelectedCandidateMoments SphericalGGThresholdFirstMomentUniform
open FiniteGGBoundaryBands FiniteGGWindowScalar FiniteGGConditionalLowMass FiniteGGWeightedConditionalWindow
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

 theorem exists_uniform_threshold_window_lower_threshold (K n J : ℕ) (hJ : 0<J)
    {a b eta : ℝ} (hab : a<b) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J → Polynomial ℝ) (hPK : ∀ i,(P i).natDegree≤K)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {kappa eps : ℝ} (hKappa : 0<kappa) (heps : 0<eps) :
    ∃ V : ℝ,1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ),V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old,Phi x old∈Icc (0 : ℝ) 1) →
        (∀ i x,x∈thresholdMasks nu v a b eta J P i → ∀ old,Phi x old≠0 →
          ∀ l : Fin (n+1),unitOverlap (old (Fin.last (n+1))) (old l.castSucc)<threshold a b J i) →
        ∀ Omega : Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N),
          MeasurableSet Omega →
          (∀ q,q∉Omega → Phi (appendLast n q).1.1 (appendLast n q).2=0) →
          (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v (n+1))/3-kappa-
            Real.sqrt (∫ p,badPairMass (lastKernel nu v n) Omega (selectedPairSet nu v n a b eta J P) p ∂jointLaw nu v n)-
              4*(eps+2*eta)/3≤thresholdWindowSum nu v (n+1) a b eta J P kappa Phi 0 := by
  obtain ⟨V,hV,hMean⟩ := exists_uniform_threshold_first_moment_threshold K (n+1) J hJ hab hBudget P hPK hApprox hGlobal heps
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhiM hPhi hSupport Omega hOmega hOff
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := lastKernel_markov (K := K) nu hv0 n
  letI := jointLaw_probability nu hv0 n (K := K)
  let mu := (jointLaw (K := K) nu v n)⊗ₘlastKernel nu v n
  let B := selectedPairSet (K := K) nu v n a b eta J P
  let f := fun q ↦ Phi (appendLast n q).1.1 (appendLast n q).2
  have hPart := thresholdMasks_properties (K := K) nu hv0 (n+1) hab J hJ hBudget P hApprox hGlobal
  have hMeanEq := membership_moment_eq nu hv0 n a b eta J P hGlobal hPart.2.2.1 Phi hPhiM hPhi
    (fun z ↦ z) measurable_id (C := 1) (fun z hz ↦ by rw [abs_of_nonneg hz.1]; exact hz.2)
  change (∑ i,∫ p,(maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2)*
      membershipMass nu v (n+1) (threshold a b J i) p ∂jointLaw nu v (n+1))=
    ∫ q,f q*candidateMass (lastKernel nu v n) B q ∂mu at hMeanEq
  have hPhiEq := old_observable_integral_eq nu hv0 n Phi hPhiM
  change (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v (n+1))=∫ q,f q ∂mu at hPhiEq
  have hMoment : (∫ q,f q*candidateMass (lastKernel nu v n) B q ∂mu)≤
      (∫ q,f q ∂mu)/((n+2 : ℕ) : ℝ)+(eps+2*eta) := by
    rw [← hMeanEq,← hPhiEq]
    have H := hMean nu v hv Phi hPhiM hPhi hSupport
    have hCast : ((n+2 : ℕ) : ℝ)=((n+1 : ℕ) : ℝ)+1 := by push_cast; ring
    simpa only [hCast,add_assoc] using H
  have hfM : Measurable f := hPhiM.comp
    ((appendLast_measurable N K n).fst.fst.prodMk (appendLast_measurable N K n).snd)
  have hB : MeasurableSet B := selectedPairSet_measurable nu hv0 n a b eta J P hGlobal
  have H := weighted_conditional_window_integral_lower (jointLaw nu v n) (lastKernel nu v n)
    Omega hOmega B hB f hfM (fun q ↦ hPhi _ _) hOff hKappa (n+2) (by omega) hMoment
  have hZero := zero_window_eq nu hv0 n a b eta J P hGlobal hPart.2.2.1 Phi hPhiM hPhi kappa
  change thresholdWindowSum nu v (n+1) a b eta J P kappa Phi 0=
    ∫ q,f q*window kappa (candidateMass (lastKernel nu v n) B q) ∂mu at hZero
  rw [← hPhiEq,← hZero] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateLower
