-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGThresholdWeights

/-! Indicator-score window invariance from a fixed finite polynomial family and its
first-good amplitude restrictions.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGThresholdInvariance
open MeasureTheory ProbabilityTheory Filter Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGBoundedScoreWeights SphericalGGMaskedScoreStability SphericalGGFiniteScoreInvariance
open SphericalGGThresholdWeights FiniteGGBoundaryBands FiniteGGWindowScalar
open NonRSUpperProofs.GaussianGGIndicatorTransfer
open scoped BigOperators
noncomputable section

def thresholdWindowSum {N K : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
    (v : ℝ) (n : ℕ) (a b eta : ℝ) (J : ℕ) (P : Fin J → Polynomial ℝ) (kappa : ℝ)
    (Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, scoreObservable nu v n (thresholdScore n (threshold a b J i))
    (maskedPhi (thresholdMasks nu v a b eta J P i) Phi)
    (fun _ ↦ thresholdMembership n (threshold a b J i)) (window kappa) t

 theorem exists_uniform_threshold_window_threshold (K n J : ℕ) (hJ : 0<J)
    {a b eta : ℝ} (hab : a<b) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin J → Polynomial ℝ) (hPK : ∀ i,(P i).natDegree≤K)
    (hApprox : ∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2)
    (hGlobal : ∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2)
    {C : ℝ} (hC : 0≤C) (t : ℝ) {kappa : ℝ} (hKappa : 0<kappa) {eps : ℝ} (heps : 0<eps) :
    ∃ V : ℝ,1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
      (v : ℝ),V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
        Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
        (∀ x old,|Phi x old|≤C) →
        |thresholdWindowSum nu v n a b eta J P kappa Phi t-thresholdWindowSum nu v n a b eta J P kappa Phi 0|≤
          eps+(2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *2)*(((n : ℝ)+1)+(2/kappa+8)))*eta := by
  have hL : 0≤2/kappa+8 := by positivity
  have hW (z : ℝ) : |window kappa z|≤1 := by
    rw [abs_of_nonneg (window_mem_Icc kappa z).1]
    exact (window_mem_Icc kappa z).2
  obtain ⟨V,hV,hMain⟩ := exists_uniform_finite_score_weight_threshold K n J hJ
    (fun i ↦ lastPolynomial n (P i)) (fun i ↦ lastPolynomial_degree n (P i) (hPK i))
    (fun i ↦ thresholdScore n (threshold a b J i)) (fun i ↦ thresholdScore_measurable n (threshold a b J i))
    (lastBounds n) (fun i ↦ thresholdScore_bound n (threshold a b J i))
    (fun i ↦ lastPolynomial_bound n (P i) (hGlobal i)) hC t (windowTest kappa) (window kappa)
    (window_continuous kappa).measurable hW (fun _ ↦ rfl) hL (window_abs_sub_le hKappa) heps
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhi hp
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  have hPart := thresholdMasks_properties (K := K) nu hv0 n hab J hJ hBudget P hApprox hGlobal
  have hbM (i : Fin J) : Measurable (fun p : (Fin K → ℝ)×((Fin (n+1) → UnitSpin N)×UnitSpin N) ↦
      thresholdMembership n (threshold a b J i) p.2) := (thresholdMembership_measurable N n (threshold a b J i)).comp measurable_snd
  have HH := hMain nu v hv Phi hPhi hp (thresholdMasks nu v a b eta J P) hPart.1
    (fun i _ ↦ thresholdMembership n (threshold a b J i)) hbM
    (fun i _ q ↦ (thresholdMembership_mem n (threshold a b J i) q).1)
    (fun i _ q ↦ (thresholdMembership_mem n (threshold a b J i) q).2) eta hPart.2.2.2
  simpa only [thresholdWindowSum,sum_lastBounds] using HH

theorem exists_prechosen_threshold_window_family (n : ℕ)
    {a b : ℝ} (ha : -1<a) (hab : a<b) (hb : b<1)
    {C : ℝ} (hC : 0≤C) (t : ℝ) {kappa : ℝ} (hKappa : 0<kappa) {eps : ℝ} (heps : 0<eps) :
    ∃ eta : ℝ,0<eta ∧ eta≤1 ∧ ∃ J : ℕ,0<J ∧ ∃ P : Fin J → Polynomial ℝ,∃ Q : ℕ,
      1/(J : ℝ)≤eta/2 ∧
      (∀ i,(P i).natDegree≤Q) ∧
      (∀ i,‖(P i).toContinuousMapOn (Icc (-1 : ℝ) 1)-FiniteGGPrechosenPolynomialFamily.rampTest a b J i‖≤eta/2) ∧
      (∀ i r,|extendTest ((P i).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) ∧
      (∀ i,threshold a b J i∈Ioo a b ∧ band a b J i⊆Ioo a b ∧ band a b J i⊆Ioo (-1 : ℝ) 1) ∧
      ∀ K : ℕ,Q≤K → ∃ V : ℝ,1≤V ∧ ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu]
        (v : ℝ),V≤v → ∀ Phi : (Fin K → ℝ) → (Fin (n+1) → UnitSpin N) → ℝ,
          Measurable (fun p : (Fin K → ℝ)×(Fin (n+1) → UnitSpin N) ↦ Phi p.1 p.2) →
          (∀ x old,|Phi x old|≤C) →
          |thresholdWindowSum nu v n a b eta J P kappa Phi t-thresholdWindowSum nu v n a b eta J P kappa Phi 0|≤eps := by
  let A := 2*C*|t| *Real.exp ((2*((n : ℝ)+1)+2)*|t| *2)*(((n : ℝ)+1)+(2/kappa+8))
  have hA : 0≤A := by dsimp only [A]; positivity
  let eta := min 1 (eps/(2*(A+1)))
  have hEta : 0<eta := lt_min zero_lt_one (div_pos heps (by positivity))
  have hEta1 : eta≤1 := min_le_left _ _
  have hSmall : A*eta≤eps/2 := by
    have H := (le_div_iff₀ (by positivity : 0<2*(A+1))).mp (min_le_right (1 : ℝ) (eps/(2*(A+1))))
    change eta*(2*(A+1))≤eps at H
    nlinarith only [H,hEta.le]
  obtain ⟨J,hJ,_hr,hBudget,P,Q,hIntervals,_hDisj,hDegree,hApprox,hGlobal,_hExists⟩ :=
    FiniteGGPrechosenPolynomialFamily.exists_prechosen_polynomial_family ha hab hb hEta hEta1
  refine ⟨eta,hEta,hEta1,J,hJ,P,Q,hBudget,hDegree,hApprox,hGlobal,hIntervals,?_⟩
  intro K hQK
  obtain ⟨V,hV,hMain⟩ := exists_uniform_threshold_window_threshold K n J hJ hab hBudget P
    (fun i ↦ (hDegree i).trans hQK) hApprox hGlobal hC t hKappa (half_pos heps)
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv Phi hPhi hp
  have H := hMain nu v hv Phi hPhi hp
  exact H.trans (by change eps/2+A*eta≤eps; linarith only [hSmall])

end
end TensorPCA.NonRSLowerProofs.SphericalGGThresholdInvariance
