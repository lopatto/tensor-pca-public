-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentAverage

/-! Uniform finite-family threshold first moments. The amplitude-only
first-good restrictions are retained before applying the own-pair L1 bound,
so polynomial approximation contributes twice eta, independently of J. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentUniform
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGThresholdWeights SphericalGGIndicatorTilt
open SphericalGGWeightObservable SphericalGGMaskedScoreStability
open SphericalPolynomialFirstJetClippedBudget SphericalPolynomialFirstJetCubeMean
open SphericalGGThresholdFirstMoment SphericalGGThresholdFirstMomentAverage FiniteGGBoundaryBands
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sum_restrictions_eq_active {X : Type*} (J : ℕ) (S : Fin J → Set X)
    (hDisj : ∀ i j,i≠j→Disjoint (S i) (S j)) {x : X} {i : Fin J} (hi : x∈S i)
    (f : Fin J → X → ℝ) : (∑ j,(S j).indicator (f j) x)=f i x := by
  classical
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj ↦ (Set.disjoint_left.mp (hDisj j i hji)) hj hi) _
  · simp

theorem exists_uniform_threshold_first_moment_threshold (K n J : ℕ) (hJ : 0<J)
    {a b eta : ℝ} (hab : a<b) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J → Polynomial ℝ) (hPK : ∀ i,(P i).natDegree≤K)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ,1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ),V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old,0≤Phi x old ∧ Phi x old≤1) →
        (∀ i x,x∈thresholdMasks nu v a b eta J P i → ∀ old,Phi x old≠0 →
          ∀ l : Fin n,unitOverlap (old (Fin.last n)) (old l.castSucc)<threshold a b J i) →
        (∑ i,∫ p,maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2*
          membershipMass nu v n (threshold a b J i) p ∂jointLaw nu v n)≤
          (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v n)/((n : ℝ)+1)+eps+2*eta := by
  classical
  let C : ℝ := ∑ i,∑ q ∈ Finset.range (K+1),|(P i).coeff q|
  have hC : 0≤C := Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun q _ ↦ abs_nonneg _))
  obtain ⟨V,hV,hMean⟩ := exists_uniform_polynomial_error_mean_threshold K (div_pos heps (by positivity : 0<C+1))
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhi hp hSupport
  have hvp : 0<v := lt_of_lt_of_le zero_lt_one (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hvp.le
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let S := thresholdMasks (K := K) nu v a b eta J P
  let F : Fin J → (Fin K → ℝ) → ℝ := fun i x ↦
    ∫ s,maskedPhi (S i) Phi x (initial s)*(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))
      ∂law d ((parameterizedGibbsKernel nu v).sectR x) (n+2)
  let O : (Fin K → ℝ) → ℝ := fun x ↦ ∫ old,Phi x old ∂law d ((parameterizedGibbsKernel nu v).sectR x) (n+1)
  let E : Fin J → (Fin K → ℝ) → ℝ := fun i x ↦
    ∑ q ∈ Finset.range (K+1),|(P i).coeff q| *boundedPowerError nu v x n q
  have hPart := thresholdMasks_properties (K := K) nu hvp.le n hab J hJ hBudget P hApprox hGlobal
  have hpAbs (x) (old) : |Phi x old|≤1 := by rw [abs_of_nonneg (hp x old).1]; exact (hp x old).2
  have hM (i : Fin J) := maskedPhi_measurable (hPart.1 i) hPhi
  have hMb (i : Fin J) (x) (old) : |maskedPhi (S i) Phi x old|≤1 := maskedPhi_abs_le (S i) zero_le_one hpAbs x old
  have hIM (i : Fin J) : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦
      maskedPhi (S i) Phi p.1 (initial p.2)*(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (p.2 (Fin.last n).castSucc) (p.2 (Fin.last (n+1))))) := by
    have hR : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦
        unitOverlap (p.2 (Fin.last n).castSucc) (p.2 (Fin.last (n+1)))) := by
      have hPair : Measurable (fun p : (Fin K → ℝ)×(Fin (n+2) → UnitSpin N) ↦
          (p.2 (Fin.last n).castSucc,p.2 (Fin.last (n+1)))) :=
        ((measurable_pi_apply _).comp measurable_snd).prodMk ((measurable_pi_apply _).comp measurable_snd)
      simpa only [Function.comp_def] using (SphericalFirstJetPowerBudget.unitOverlap_measurable N).comp hPair
    exact ((hM i).comp (measurable_fst.prodMk ((initial_measurable _).comp measurable_snd))).mul
      ((measurable_const.indicator measurableSet_Ici).comp hR)
  have hZB (i : Fin J) (x : Fin K → ℝ) (s : Fin (n+2) → UnitSpin N) :
      |maskedPhi (S i) Phi x (initial s)*(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))|≤1 := by
    rw [abs_mul]
    have hI : |(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
      (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))|≤1 := by
      by_cases h : unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1)))∈Ici (threshold a b J i) <;> simp [h]
    exact (mul_le_mul (hMb i x _) hI (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hFB (i : Fin J) (x : Fin K → ℝ) : |F i x|≤1 := by
    have H := norm_integral_le_of_norm_le_const (μ := law d ((parameterizedGibbsKernel nu v).sectR x) (n+2))
      (f := fun s ↦ maskedPhi (S i) Phi x (initial s)*(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1))))) (C := 1)
      (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hZB i x s))
    simpa only [F,Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hFI (i : Fin J) : Integrable (F i) (positiveCubeLaw K) :=
    Integrable.of_bound (parameterized_law_integral_measurable d (parameterizedGibbsKernel nu v) (n+2)
      _ (hIM i) (hZB i)).aestronglyMeasurable 1
      (Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using hFB i x))
  have hOI : Integrable O (positiveCubeLaw K) := by
    apply Integrable.of_bound (parameterized_law_integral_measurable d (parameterizedGibbsKernel nu v) (n+1) Phi hPhi hpAbs).aestronglyMeasurable 1
    exact Eventually.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ := law d ((parameterizedGibbsKernel nu v).sectR x) (n+1)) (f := Phi x) (C := 1)
        (Eventually.of_forall (fun old ↦ by simpa only [Real.norm_eq_abs] using hpAbs x old))))
  have hEI (i : Fin J) : Integrable (E i) (positiveCubeLaw K) :=
    integrable_finsetSum (Finset.range (K+1)) (fun q _ ↦ (boundedPowerError_integrable nu hvp.le n q).const_mul |(P i).coeff q|)
  have hEN (i : Fin J) (x : Fin K → ℝ) : 0≤E i x :=
    Finset.sum_nonneg (fun q _ ↦ mul_nonneg (abs_nonneg _) (boundedPowerError_nonneg nu v x n q))
  have hPoint (x : Fin K → ℝ) (hx : ∀ p,|x p|≤2) (hxp : ∀ p,0<x p) :
      (∑ i,F i x)≤O x/((n : ℝ)+1)+(∑ i,E i x)+2*eta := by
    obtain ⟨i,hi⟩ : ∃ i : Fin J,x∈S i := by
      have hh : x∈⋃ i,S i := by rw [hPart.2.2.1]; trivial
      exact Set.mem_iUnion.mp hh
    have hFresh : (∑ j,F j x)=∫ s,Phi x (initial s)*(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))
        (unitOverlap (s (Fin.last n).castSucc) (s (Fin.last (n+1)))) ∂law d ((parameterizedGibbsKernel nu v).sectR x) (n+2) := by
      rw [Finset.sum_eq_single i]
      · simp only [F,maskedPhi,if_pos hi]
      · intro j _ hji
        have hj : x∉S j := fun hj ↦ (Set.disjoint_left.mp (hPart.2.1 j i hji)) hj hi
        simp only [F,maskedPhi,if_neg hj,zero_mul,integral_zero]
      · simp
    have hL := hPart.2.2.2 x
    rw [sum_restrictions_eq_active J S hPart.2.1 hi] at hL
    rw [last_score_error_eq] at hL
    have H := fixed_amplitude_threshold_first_moment nu hvp x hx hxp n (threshold a b J i)
      (Phi x) (hPhi.comp (measurable_const.prodMk measurable_id)) (hpAbs x) (hSupport i x hi) (P i) (hPK i) (hGlobal i)
    have hOld : 0≤O x := integral_nonneg (fun old ↦ (hp x old).1)
    have hGamma : pairMean nu v ((Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))) x≤1 :=
      (le_abs_self _).trans (pairMean_abs_le nu hvp.le (fun r ↦ by by_cases h : r∈Ici (threshold a b J i) <;> simp [h]) x)
    have hOwn : O x*pairMean nu v ((Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ))) x/((n : ℝ)+1)≤O x/((n : ℝ)+1) := by
      exact div_le_div_of_nonneg_right (by nlinarith only [hOld,hGamma]) (by positivity)
    have hE : E i x≤∑ j,E j x := Finset.single_le_sum (fun j _ ↦ hEN j x) (Finset.mem_univ i)
    rw [hFresh]
    have ht := (abs_le.mp H).2
    change _≤E i x+2*pairMean nu v (fun r ↦ |(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ)) r-extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x at ht
    have hL' : pairMean nu v (fun r ↦ |(Ici (threshold a b J i)).indicator (fun _ ↦ (1 : ℝ)) r-extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x≤eta := by
      simpa only [FiniteGGParameterScorePartition.ownScoreL1,pairMean,abs_sub_comm] using hL
    linarith only [ht,hOwn,hE,hL']
  have hEmean (i : Fin J) : (∫ x,E i x ∂positiveCubeLaw K)≤
      eps/(C+1)*(∑ q ∈ Finset.range (K+1),|(P i).coeff q|) := by
    have H := hMean (N := N) (K := K) le_rfl nu v hv n (lastPolynomial n (P i))
      (fun j ↦ lastPolynomial_degree n (P i) (hPK i) j)
    simpa only [Fin.sum_univ_castSucc,lastPolynomial,Fin.snoc_castSucc,Fin.snoc_last,
      Polynomial.coeff_zero,abs_zero,zero_mul,Finset.sum_const_zero,zero_add] using H
  have hEtotal : (∫ x,(∑ i,E i x) ∂positiveCubeLaw K)≤eps := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hEI i)]
    calc
      _ ≤ ∑ i,eps/(C+1)*(∑ q ∈ Finset.range (K+1),|(P i).coeff q|) := Finset.sum_le_sum (fun i _ ↦ hEmean i)
      _ = eps/(C+1)*C := (Finset.mul_sum _ _ _).symm
      _ ≤ eps := by
        have hNon : 0≤eps/(C+1) := div_nonneg heps.le (by positivity)
        have hEq : eps/(C+1)*(C+1)=eps := div_mul_cancel₀ eps (by positivity : C+1≠0)
        nlinarith only [hNon,hEq]
  have hPointAE : ∀ᵐ x ∂positiveCubeLaw K,(∑ i,F i x)≤O x/((n : ℝ)+1)+(∑ i,E i x)+2*eta := by
    apply (positiveCubeLaw_support K).mono
    intro x hx
    have hxp (p : Fin K) : 0<x p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) (hx p).1
    have hxb (p : Fin K) : |x p|≤2 := by rw [abs_of_pos (hxp p)]; linarith only [(hx p).2]
    exact hPoint x hxb hxp
  have hSumFI := integrable_finsetSum Finset.univ (fun i _ ↦ hFI i)
  have hSumEI := integrable_finsetSum Finset.univ (fun i _ ↦ hEI i)
  have hR0 : Integrable (fun x ↦ O x/((n : ℝ)+1)+(∑ i,E i x)) (positiveCubeLaw K) := by
    convert (hOI.div_const ((n : ℝ)+1)).add hSumEI using 1
  have H := integral_mono_ae hSumFI (hR0.add (integrable_const (2*eta))) hPointAE
  simp only [Pi.add_apply] at H
  rw [integral_add hR0 (integrable_const (2*eta)),
    integral_add (hOI.div_const ((n : ℝ)+1)) hSumEI,integral_div,integral_const,
    probReal_univ,smul_eq_mul,one_mul] at H
  have hLHS : (∑ i,∫ p,maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2*
      membershipMass nu v n (threshold a b J i) p ∂jointLaw nu v n)=
      ∫ x,(∑ i,F i x) ∂positiveCubeLaw K := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hFI i)]
    apply Finset.sum_congr rfl
    intro i _
    exact joint_membership_integral_eq_cube nu hvp.le n (threshold a b J i)
      (maskedPhi (S i) Phi) (hM i) (hMb i)
  rw [hLHS,joint_old_integral_eq_cube nu hvp.le n Phi hPhi hpAbs]
  change (∫ x,(∑ i,F i x) ∂positiveCubeLaw K)≤(∫ x,O x ∂positiveCubeLaw K)/((n : ℝ)+1)+eps+2*eta
  linarith only [H,hEtotal]

theorem exists_uniform_threshold_first_moment_small_error (K n J : ℕ) (hJ : 0<J)
    {a b eta : ℝ} (hab : a<b) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J → Polynomial ℝ) (hPK : ∀ i,(P i).natDegree≤K)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {eps : ℝ} (heps : 0<eps) (hEta : eta≤eps/4) :
    ∃ V : ℝ,1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ),V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old,0≤Phi x old ∧ Phi x old≤1) →
        (∀ i x,x∈thresholdMasks nu v a b eta J P i → ∀ old,Phi x old≠0 →
          ∀ l : Fin n,unitOverlap (old (Fin.last n)) (old l.castSucc)<threshold a b J i) →
        (∑ i,∫ p,maskedPhi (thresholdMasks nu v a b eta J P i) Phi p.1.1 p.2*
          membershipMass nu v n (threshold a b J i) p ∂jointLaw nu v n)≤
          (∫ p,Phi p.1.1 p.2 ∂jointLaw nu v n)/((n : ℝ)+1)+eps := by
  obtain ⟨V,hV,hMain⟩ := exists_uniform_threshold_first_moment_threshold K n J hJ hab hBudget P hPK hApprox hGlobal (half_pos heps)
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhi hp hSupport
  exact (hMain nu v hv Phi hPhi hp hSupport).trans (by linarith only [hEta])


end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdFirstMomentUniform
