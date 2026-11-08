-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGSelectedCandidate
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdInvariance

/-! A single candidate low-mass bound for the complete finite threshold window sum. The
finite partition incurs no cardinality loss.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateUpper
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGWeightObservable
open SphericalGGIndicatorTilt SphericalGGLastSpinCandidate SphericalGGSelectedCandidate
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability SphericalGGRootWindowBounds
open SphericalGGThresholdInvariance FiniteGGBoundaryBands FiniteGGWindowScalar FiniteGGConditionalLowMass
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

 theorem thresholdWindowSum_le_candidate_mass {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ) {a b eta : ℝ} (hab : a<b) (J : ℕ) (hJ : 0<J)
    (hBudget : 1/(J : ℝ)≤eta/2) (P : Fin J → Polynomial ℝ)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {kappa t gap : ℝ} (hKappa : 0<kappa) (ht : 0≤t) (hGap : 0≤gap)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhiM : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2))
    (hPhi : ∀ x old,Phi x old∈Icc (0 : ℝ) 1)
    (Omega : Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N))
    (hOmega : MeasurableSet Omega)
    (hOff : ∀ q,q∉Omega → Phi (appendLast n q).1.1 (appendLast n q).2=0)
    (hBelow : ∀ q∈Omega,∀ l : Fin (n+1),unitOverlap q.2 (q.1.2 l)<a)
    (hGamma : ∀ i : Fin J,∀ q∈Omega,q.1∈prefixMasks nu v n a b eta J P i →
      pairMean nu v ((Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))) q.1.1.1≤1-gap) :
    thresholdWindowSum nu v (n+1) a b eta J P kappa Phi t≤
      7*Real.exp (-t*gap)+Real.exp t*Real.sqrt
        (∫ p,badPairMass (lastKernel nu v n) Omega (selectedPairSet nu v n a b eta J P) p ∂jointLaw nu v n) := by
  letI := lastKernel_markov (K := K) nu hv n
  letI := jointLaw_probability nu hv n (K := K)
  let mu := (jointLaw (K := K) nu v n)⊗ₘlastKernel nu v n
  let B := selectedPairSet (K := K) nu v n a b eta J P
  let Low := Omega∩{q | candidateMass (lastKernel nu v n) B q≤7*Real.exp (-t)}
  let Fi := fun i p ↦ scoreIntegrand nu v (n+1) (thresholdScore (n+1) (threshold a b J i))
    (maskedPhi (thresholdMasks nu v a b eta J P i) Phi)
    (fun _ ↦ thresholdMembership (n+1) (threshold a b J i)) (window kappa) t p
  let F := fun p ↦ ∑ i,Fi i p
  have hPart := thresholdMasks_properties (K := K) nu hv (n+1) hab J hJ hBudget P hApprox hGlobal
  have hW (z : ℝ) : |window kappa z|≤1 := by
    rw [abs_of_nonneg (window_mem_Icc kappa z).1]; exact (window_mem_Icc kappa z).2
  have hpAbs (x) (old) : |Phi x old|≤1 := by
    rw [abs_of_nonneg (hPhi x old).1]; exact (hPhi x old).2
  have hBM (i : Fin J) : Measurable (fun p : (Fin K → ℝ)×((Fin (n+2) → UnitSpin N)×UnitSpin N) ↦
      thresholdMembership (n+1) (threshold a b J i) p.2) :=
    (thresholdMembership_measurable N (n+1) (threshold a b J i)).comp measurable_snd
  have hFI (i : Fin J) : Integrable (Fi i) (jointLaw nu v (n+1)) :=
    scoreIntegrand_integrable nu hv (n+1) (thresholdScore_measurable (n+1) (threshold a b J i))
      (lastBounds (n+1)) (thresholdScore_bound (n+1) (threshold a b J i))
      (maskedPhi_measurable (hPart.1 i) hPhiM) (maskedPhi_abs_le _ zero_le_one hpAbs)
      (hBM i) (window_continuous kappa).measurable hW t
  have hFs : Integrable F (jointLaw nu v (n+1)) := integrable_finset_sum Finset.univ (fun i _ ↦ hFI i)
  have hLaw := appendLast_hasLaw (K := K) nu hv n
  have hPull : thresholdWindowSum nu v (n+1) a b eta J P kappa Phi t=
      ∫ q,F (appendLast n q) ∂mu := by
    unfold thresholdWindowSum scoreObservable
    change (∑ i,∫ p,Fi i p ∂jointLaw nu v (n+1))=_
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ hFI i)]
    exact (hLaw.integral_comp hFs.aestronglyMeasurable).symm
  have hB : MeasurableSet B := selectedPairSet_measurable nu hv n a b eta J P hGlobal
  have hLow : MeasurableSet Low := hOmega.inter
    (measurableSet_le (candidateMass_measurable (lastKernel nu v n) B hB) measurable_const)
  have hPoint (q) : F (appendLast n q)≤Real.exp (t*(1-gap))*Low.indicator (fun _ ↦ (1 : ℝ)) q := by
    by_cases hq : q∈Omega
    · have hCover : (appendLast n q).1.1∈⋃ i,thresholdMasks nu v a b eta J P i := by
        rw [hPart.2.2.1]; exact mem_univ _
      obtain ⟨i,hi⟩ := mem_iUnion.mp hCover
      have hp : q.1∈prefixMasks nu v n a b eta J P i := hi
      have hCan := candidateMass_selected_on_cell nu hv n a b eta J P i q.1 hp q.2
      change candidateMass (lastKernel nu v n) B q=
        membershipMass nu v (n+1) (threshold a b J i) (appendLast n q) at hCan
      have hBelow' : ∀ l : Fin (n+1),unitOverlap ((appendLast n q).2 (Fin.last (n+1)))
          ((appendLast n q).2 l.castSucc)<threshold a b J i := by
        intro l
        simpa only [appendLast,Fin.snoc_last,Fin.snoc_castSucc] using (hBelow q hq l).trans (threshold_mem hab J i).1
      have H := scoreIntegrand_le_small_membership nu hv (n+1) (threshold a b J i) hKappa ht Phi
        (appendLast n q) (hPhi _ _).1 (hPhi _ _).2 hBelow' (hGamma i q hq hp)
      change (∑ j,Fi j (appendLast n q))≤_
      rw [sum_masked_scoreIntegrands_eq_on_cell nu v n a b eta J P i kappa t Phi (appendLast n q) hi]
      convert H using 1
      by_cases hs : candidateMass (lastKernel nu v n) B q≤7*Real.exp (-t)
      · have hLq : q∈Low := ⟨hq,hs⟩
        have hOq : appendLast n q∈{p | membershipMass nu v (n+1) (threshold a b J i) p≤7*Real.exp (-t)} := by
          change membershipMass nu v (n+1) (threshold a b J i) (appendLast n q)≤7*Real.exp (-t)
          rw [← hCan]
          exact hs
        rw [indicator_of_mem hLq,indicator_of_mem hOq]
      · have hLq : q∉Low := fun hh ↦ hs hh.2
        have hOq : appendLast n q∉{p | membershipMass nu v (n+1) (threshold a b J i) p≤7*Real.exp (-t)} := by
          intro hh
          exact hs (hCan.symm ▸ hh)
        rw [indicator_of_notMem hLq,indicator_of_notMem hOq]
    · have hZeros (i : Fin J) : Fi i (appendLast n q)=0 := by
        apply scoreIntegrand_zero_of_zero
        have HH := hOff q hq
        simp only [maskedPhi,HH,ite_self]
      have hZero : F (appendLast n q)=0 := by simp only [F,hZeros,Finset.sum_const_zero]
      rw [hZero]
      exact mul_nonneg (Real.exp_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hMono := integral_mono (hLaw.integrable_comp hFs)
    (((integrable_const (1 : ℝ)).indicator hLow).const_mul (Real.exp (t*(1-gap)))) hPoint
  rw [integral_const_mul,integral_indicator_const (1 : ℝ) hLow,smul_eq_mul,mul_one] at hMono
  have hMass := conditional_low_mass_le (jointLaw nu v n) (lastKernel nu v n)
    Omega hOmega B hB Omega hOmega (Subset.refl Omega) (by positivity : 0≤7*Real.exp (-t))
  rw [hPull]
  calc
    _ ≤ Real.exp (t*(1-gap))*mu.real Low := hMono
    _ ≤ Real.exp (t*(1-gap))*(7*Real.exp (-t)+Real.sqrt
        (∫ p,badPairMass (lastKernel nu v n) Omega B p ∂jointLaw nu v n)) :=
      mul_le_mul_of_nonneg_left hMass (Real.exp_nonneg _)
    _ ≤ _ := root_decay ht hGap (le_refl (1-gap))

end
end TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateUpper
