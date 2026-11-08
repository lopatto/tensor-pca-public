-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeLawFamilyApproximation
public import TensorPCA.NonRSLowerProofs.SphericalGGFiniteArrayPositivity

/-! One coherent physical family for finite tree laws, bad-threshold errors and the
closed negative-overlap event. Finite maxima combine the required threshold bounds
for that same family.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeLawPhysicalFamily
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights
open SphericalGGTreeLawFamilyApproximation SphericalGGFiniteArrayPositivity
open FiniteGGBoundaryBands FiniteGGPrechosenPolynomialFamily FiniteGGParameterScorePartition
open FiniteGGMonotoneBoundaryCuts FiniteGGProductCutMasks
open FiniteNestedPartition FiniteNestedLawComparison FiniteNestedDiscountedPartitionLaw
open FiniteNestedStrictSurrogate
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_uniform_physical_tree_law_family (R depth : ℕ) (hR : 0<R)
    (a b : Fin depth→ℝ) (ha : ∀l,-1<a l) (hab : ∀l,a l<b l) (hb : ∀l,b l≤1)
    (hSep : ∀l j : Fin depth,l<j→b l≤a j) {epsLaw epsBad epsNeg etaCap negTol : ℝ} (hepsLaw : 0<epsLaw) (hepsBad : 0<epsBad)
    (hepsNeg : 0<epsNeg) (hEtaCap : 0<etaCap) (hNegTol : 0<negTol) :
    ∃ tau : ℝ,∃ htau : 0<tau,∃ htau1 : tau≤1,
    ∃ eta : ℝ,0<eta ∧ eta≤1 ∧ eta≤etaCap ∧ ∃ J : ℕ,0<J ∧ 1/(J : ℝ)≤eta/2 ∧
      ∃ P : Fin depth→Fin J→Polynomial ℝ,∃ Q : ℕ,
        (∀l j,(P l j).natDegree≤Q) ∧
        (∀l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta/2) ∧
        (∀l j r,|extendTest ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) ∧
        ∀K : ℕ,Q≤K → ∃ V : ℝ,∃ hV : 1≤V,
          ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : V≤v),
            let hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
            letI := parameterizedGibbsKernel_markov (K := K) nu hv0
            let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
            let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
            let good := fun l ↦ goodParameter d (parameterizedGibbsKernel nu v)
              unitOverlap (a l) (b l) J (P l) eta
            let cuts := fun (index : Fin depth→Fin J) l ↦ threshold (a l) (b l) J (index l)
            let heights := fun (index : Fin depth→Fin J) (x : Fin K→ℝ) l ↦ lowerHeight nu v (cuts index l) x
            let h0 := fun index x ↦ (own_lower_heights_properties nu hv0 (cuts index)
              (threshold_vector_strictMono a b hab hSep index).monotone x).1
            let hm := fun index x ↦ (own_lower_heights_properties nu hv0 (cuts index)
              (threshold_vector_strictMono a b hab hSep index).monotone x).2.1
            let h1 := fun index x ↦ (own_lower_heights_properties nu hv0 (cuts index)
              (threshold_vector_strictMono a b hab hSep index).monotone x).2.2
            let surrogate := fun (m : ℕ) index x ↦ partitionPMF depth m
              (strictHeightApprox depth (heights index x) tau) 0 (le_refl 0)
              (strictHeightApprox_pos depth (heights index x) tau (h0 index x) htau htau1)
              (strictHeightApprox_strictMono depth (heights index x) tau (hm index x) htau htau1)
              (fun l ↦ (strictHeightApprox_lt_one depth (heights index x) tau (h1 index x) htau htau1 l).le)
            ∀m : ℕ,0<m → m≤R →
            (∑index : Fin depth→Fin J,∫x,l1Distance
              (treePMF (cuts index) (threshold_vector_strictMono a b hab hSep index).monotone (law d (G x) m))
              (surrogate m index x) ∂(positiveCubeLaw K).restrict (cutCell good index))≤epsLaw ∧
            (jointLaw (K := K) nu v (m-1)).real {q | ∃index : Fin depth→Fin J,
              q.1.1∈cutCell good index ∧ ¬thresholdGood (cuts index) q.2}≤epsBad ∧
            (jointLaw (K := K) nu v (m-1)).real {q | ∃i j : Fin (m-1+1),
              unitOverlap (q.2 i) (q.2 j)≤-negTol}≤epsNeg := by
  classical
  obtain ⟨tau,htau,htau1,eta,hEta,hEta1,hEtaCapLe,J,hJ,hBudget,P,Qfamily,hDegree,hApprox,hGlobal,hFamily⟩ :=
    exists_uniform_tree_law_family_approximation R depth hR a b ha hab hb hSep hepsLaw hepsBad hEtaCap
  let cut : ℝ := min 1 negTol
  have hCut : 0<cut := lt_min (by norm_num) hNegTol
  have hCut1 : cut≤1 := min_le_left _ _
  have hCutTol : cut≤negTol := min_le_right _ _
  choose Qneg Vneg hVneg hNeg using (fun r : Fin R ↦
    exists_uniform_finite_array_positivity_threshold r.val hCut hCut1 hepsNeg)
  let Q : ℕ := Qfamily+∑r : Fin R,Qneg r
  have hQfamily : Qfamily≤Q := by dsimp only [Q]; omega
  have hQneg (r : Fin R) : Qneg r≤Q := by
    have H := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (Qneg j)) (Finset.mem_univ r)
    dsimp only [Q]
    omega
  refine ⟨tau,htau,htau1,eta,hEta,hEta1,hEtaCapLe,J,hJ,hBudget,P,Q,
    (fun l j ↦ (hDegree l j).trans hQfamily),hApprox,hGlobal,?_⟩
  intro K hK
  obtain ⟨VF,hVF,hMain⟩ := hFamily K (hQfamily.trans hK)
  let V : ℝ := VF+1+∑r : Fin R,Vneg r
  have hSum : 0≤∑r : Fin R,Vneg r := Finset.sum_nonneg (fun r _ ↦ (by norm_num : (0 : ℝ)≤1).trans (hVneg r))
  have hV : 1≤V := by dsimp only [V]; linarith only [hVF,hSum]
  have hVFdom : VF≤V := by dsimp only [V]; linarith only [hSum]
  have hVnegdom (r : Fin R) : Vneg r≤V := by
    have H := Finset.single_le_sum (fun j _ ↦ (by norm_num : (0 : ℝ)≤1).trans (hVneg j)) (Finset.mem_univ r)
    dsimp only [V]
    linarith only [H,hVF]
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hv0
  dsimp only
  intro m hm hmR
  have H := hMain nu v (hVFdom.trans hv) m hm hmR
  refine ⟨H.1,H.2,?_⟩
  let r : Fin R := ⟨m-1,by omega⟩
  have Hneg := hNeg r K ((hQneg r).trans hK) nu v ((hVnegdom r).trans hv)
  change (jointLaw (K := K) nu v (m-1)).real {q | ∃i j : Fin (m-1+1),
    unitOverlap (q.2 i) (q.2 j)≤-cut}≤epsNeg at Hneg
  letI := jointLaw_probability (K := K) nu hv0 (m-1)
  apply le_trans _ Hneg
  exact measureReal_mono (by
    rintro q ⟨i,j,hij⟩
    exact ⟨i,j,hij.trans (neg_le_neg hCutTol)⟩)
    (measure_ne_top (jointLaw (K := K) nu v (m-1)) _)

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeLawPhysicalFamily
