-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateUpper
public import TensorPCA.NonRSLowerProofs.SphericalGGWindowCandidateLower
public import TensorPCA.NonRSLowerProofs.SphericalGGOldEventMassRestriction
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowContradictionConstants
public import TensorPCA.NonRSLowerProofs.FiniteGGCandidateMassMonotonicity

/-! Uniform finite duplication under the full perturbation Gibbs law. The exported event
uses the original weight support and one fixed overlap threshold; no selected graph,
GG identity, or own-mean hypothesis remains.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteDuplication
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGWeightObservable
open SphericalGGIndicatorTilt SphericalGGLastSpinCandidate SphericalGGSelectedCandidate
open SphericalGGBoundedScoreWeights SphericalGGThresholdInvariance
open SphericalGGWindowCandidateUpper SphericalGGWindowCandidateLower SphericalGGOldEventMassRestriction
open FiniteGGBoundaryBands FiniteGGWindowScalar FiniteGGConditionalLowMass
open FiniteGGPrechosenPolynomialFamily FiniteGGWindowContradictionConstants FiniteGGCandidateMassMonotonicity
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

def eventSupport {N K : ℕ} (n : ℕ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ) :
    Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N) :=
  {q | Phi (appendLast n q).1.1 (appendLast n q).2≠0}

theorem eventSupport_measurable {N K : ℕ} (n : ℕ)
    (Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ)
    (hPhi : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi p.1 p.2)) :
    MeasurableSet (eventSupport n Phi) := by
  have H := hPhi.comp ((appendLast_measurable N K n).fst.fst.prodMk (appendLast_measurable N K n).snd)
  exact (H (measurableSet_singleton (0 : ℝ))).compl

private theorem badPair_integrable {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    {v : ℝ} (hv : 0≤v) (n : ℕ)
    (Omega : Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×UnitSpin N))
    (hOmega : MeasurableSet Omega)
    (B : Set ((((Fin K → ℝ)×PerturbationDisorder N K)×(Fin (n+1) → UnitSpin N))×(UnitSpin N×UnitSpin N)))
    (hB : MeasurableSet B) :
    Integrable (badPairMass (lastKernel nu v n) Omega B) (jointLaw nu v n) := by
  letI := lastKernel_markov (K := K) nu hv n
  letI := jointLaw_probability nu hv n (K := K)
  apply Integrable.of_bound (badPairMass_measurable (lastKernel nu v n) Omega hOmega B hB).aestronglyMeasurable 1
  exact Eventually.of_forall (fun q ↦ by
    rw [Real.norm_of_nonneg (badPairMass_mem_Icc (lastKernel nu v n) Omega B q).1]
    exact (badPairMass_mem_Icc (lastKernel nu v n) Omega B q).2)

theorem threshold_graph_subset_selected {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) {a b eta : ℝ} (hab : a<b) (J : ℕ) (P : Fin J → Polynomial ℝ)
    (hCover : (⋃ i,thresholdMasks (K := K) nu v a b eta J P i)=univ) :
    thresholdPairSet (N := N) (K := K) n b⊆selectedPairSet nu v n a b eta J P := by
  apply common_graph_subset_maskedUnion (prefixMasks nu v n a b eta J P)
    (fun i ↦ thresholdPairSet n (threshold a b J i)) (thresholdPairSet n b)
  · ext q
    simp only [mem_iUnion,mem_univ,iff_true]
    have hh : q.1.1∈⋃ i,thresholdMasks nu v a b eta J P i := by rw [hCover]; exact mem_univ _
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact ⟨i,hi⟩
  · intro i q hq
    change b≤unitOverlap q.2.2 q.2.1 at hq
    exact (threshold_mem hab J i).2.le.trans hq

 theorem exists_uniform_physical_duplication_threshold (n : ℕ)
    {a b p : ℝ} (ha : -1<a) (hab : a<b) (hb : b<1) (hp : p∈Ioc (0 : ℝ) 1) :
    ∃ Q : ℕ,∃ c : ℝ,0<c ∧ ∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧
      ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ),V≤v →
        ∀ Phi : (Fin K → ℝ) → (Fin (n+2) → UnitSpin N) → ℝ,
          Measurable (fun q : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦ Phi q.1 q.2) →
          (∀ x old,Phi x old∈Icc (0 : ℝ) 1) →
          (∀ x old,Phi x old≠0 → ∀ l : Fin (n+1),unitOverlap (old (Fin.last (n+1))) (old l.castSucc)<a) →
          p≤(∫ q,Phi q.1.1 q.2 ∂jointLaw nu v (n+1)) →
          c≤∫ q,badPairMass (lastKernel nu v n) (eventSupport n Phi) (thresholdPairSet n b) q ∂jointLaw nu v n := by
  have hpHalf : p/2∈Ioc (0 : ℝ) 1 := ⟨half_pos hp.1,by linarith only [hp.2]⟩
  obtain ⟨kappa,eps,t,c,hKappa,_hKU,heps,ht,hc,hSeparate⟩ := exists_window_separation_constants hpHalf (half_pos hp.1)
  let A := 2*(1 : ℝ)*|t| *Real.exp ((2*(((n+1 : ℕ) : ℝ)+1)+2)*|t| *2)*
    ((((n+1 : ℕ) : ℝ)+1)+(2/kappa+8))
  have hA : 0≤A := by dsimp only [A]; positivity
  let eta := min 1 (min (eps/4) (eps/(2*(A+1))))
  have hEta : 0<eta := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hEta1 : eta≤1 := min_le_left _ _
  have hEtaE : eta≤eps/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hEtaA : A*eta≤eps/2 := by
    have hh : eta≤eps/(2*(A+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have H := (le_div_iff₀ (by positivity : 0<2*(A+1))).mp hh
    nlinarith only [H,hEta.le]
  have hMomentE : eps/2+2*eta≤eps := by linarith only [hEtaE]
  obtain ⟨J,hJ,_hr,hBudget,P,Q,_hIntervals,_hDisj,hDegree,hApprox,hGlobal,_hExists⟩ :=
    exists_prechosen_polynomial_family ha hab hb hEta hEta1
  refine ⟨Q,c,hc,?_⟩
  intro K hQK
  have hPK (i : Fin J) : (P i).natDegree≤K := (hDegree i).trans hQK
  obtain ⟨VI,hVI,hInvariant⟩ := exists_uniform_threshold_window_threshold K (n+1) J hJ hab hBudget P hPK hApprox hGlobal
    (C := 1) zero_le_one t hKappa (half_pos heps)
  obtain ⟨VL,hVL,hLower⟩ := exists_uniform_threshold_window_lower_threshold K n J hJ hab hBudget P hPK hApprox hGlobal hKappa (half_pos heps)
  let V := VI+VL
  have hV : 1≤V := by dsimp only [V]; linarith only [hVI,hVL]
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhiM hPhi hSupport hMass
  have hVIs : VI≤v := by dsimp only [V] at hv; linarith only [hv,hVL]
  have hVLs : VL≤v := by dsimp only [V] at hv; linarith only [hv,hVI]
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  let R := restrictedPhi nu v n p Phi
  let Omega := eventSupport n R
  let B := selectedPairSet (K := K) nu v n a b eta J P
  let D := ∫ q,badPairMass (lastKernel nu v n) Omega B q ∂jointLaw nu v n
  let W0 := thresholdWindowSum nu v (n+1) a b eta J P kappa R 0
  let W1 := thresholdWindowSum nu v (n+1) a b eta J P kappa R t
  have hRM := restrictedPhi_measurable nu hv0 n p Phi hPhiM hPhi
  have hR (x) (old) : R x old∈Icc (0 : ℝ) 1 := restrictedPhi_mem_Icc nu v n p Phi hPhi x old
  have hRN (x) (old) (hh : R x old≠0) : Phi x old≠0 := (restrictedPhi_ne_zero nu v n p Phi x old hh).1
  have hOmega : MeasurableSet Omega := eventSupport_measurable n R hRM
  have hOff (q) (hh : q∉Omega) : R (appendLast n q).1.1 (appendLast n q).2=0 := not_ne_iff.mp hh
  have hBelow (q) (hq : q∈Omega) (l : Fin (n+1)) : unitOverlap q.2 (q.1.2 l)<a := by
    have H := hSupport _ _ (hRN _ _ hq) l
    simpa only [appendLast,Fin.snoc_last,Fin.snoc_castSucc] using H
  have hGamma (i : Fin J) (q) (hq : q∈Omega) (_hi : q.1∈prefixMasks nu v n a b eta J P i) :
      pairMean nu v ((Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))) q.1.1.1≤1-p/2 := by
    apply restrictedPhi_own_pairMean_gap nu hv0 n p Phi hPhiM hPhi _ _ hq
    intro old ho
    have H := (hSupport q.1.1.1 old ho (0 : Fin (n+1))).trans (threshold_mem hab J i).1
    simpa only [Fin.castSucc_zero] using H
  have hSupportR (i : Fin J) (x) (_hx : x∈thresholdMasks nu v a b eta J P i) (old) (hh : R x old≠0)
      (l : Fin (n+1)) : unitOverlap (old (Fin.last (n+1))) (old l.castSucc)<threshold a b J i :=
    (hSupport x old (hRN x old hh) l).trans (threshold_mem hab J i).1
  have hUpper : W1≤7*Real.exp (-t*(p/2))+Real.exp t*Real.sqrt D :=
    thresholdWindowSum_le_candidate_mass nu hv0 n hab J hJ hBudget P hApprox hGlobal hKappa ht (half_pos hp.1).le
      R hRM hR Omega hOmega hOff hBelow hGamma
  have hLow := hLower nu v hVLs R hRM hR hSupportR Omega hOmega hOff
  have hRetained : p/2≤∫ q,R q.1.1 q.2 ∂jointLaw nu v (n+1) :=
    restrictedPhi_joint_mass_ge_half nu hv0 n p hp.1.le Phi hPhiM hPhi hMass
  have hLow' : (p/2)/3-kappa-Real.sqrt D-4*eps/3≤W0 := by
    change (∫ q,R q.1.1 q.2 ∂jointLaw nu v (n+1))/3-kappa-Real.sqrt D-4*(eps/2+2*eta)/3≤W0 at hLow
    linarith only [hLow,hRetained,hMomentE]
  have hRAbs (x) (old) : |R x old|≤1 := by rw [abs_of_nonneg (hR x old).1]; exact (hR x old).2
  have hInv := hInvariant nu v hVIs R hRM hRAbs
  have hInv' : |W0-W1|≤eps := by
    change |W1-W0|≤eps/2+A*eta at hInv
    rw [abs_sub_comm]
    exact hInv.trans (by linarith only [hEtaA])
  have hD : 0≤D := integral_nonneg (fun _ ↦ measureReal_nonneg)
  have hPositive : c≤D := hSeparate D W0 W1 hD hLow' hUpper hInv'
  have hOrig : MeasurableSet (eventSupport n Phi) := eventSupport_measurable n Phi hPhiM
  have hSub : Omega⊆eventSupport n Phi := fun q hq ↦ hRN _ _ hq
  have hPart := thresholdMasks_properties (K := K) nu hv0 (n+1) hab J hJ hBudget P hApprox hGlobal
  have hGraph : thresholdPairSet (N := N) (K := K) n b⊆B := threshold_graph_subset_selected nu v n hab J P hPart.2.2.1
  letI := lastKernel_markov (K := K) nu hv0 n
  have hB : MeasurableSet B := selectedPairSet_measurable nu hv0 n a b eta J P hGlobal
  have hPoint (q) : badPairMass (lastKernel nu v n) Omega B q≤
      badPairMass (lastKernel nu v n) (eventSupport n Phi) (thresholdPairSet n b) q :=
    (badPairMass_mono_Omega (lastKernel nu v n) hSub B q).trans
      (badPairMass_antitone_graph (lastKernel nu v n) (eventSupport n Phi) hGraph q)
  exact hPositive.trans (integral_mono (badPair_integrable nu hv0 n Omega hOmega B hB)
    (badPair_integrable nu hv0 n (eventSupport n Phi) hOrig (thresholdPairSet n b) (thresholdPairSet_measurable N K n b)) hPoint)

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteDuplication
