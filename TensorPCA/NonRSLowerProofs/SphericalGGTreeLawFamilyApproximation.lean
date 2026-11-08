-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceControlled
public import TensorPCA.NonRSLowerProofs.FiniteNestedLawAverage

/-! Coherent tree-law approximation and selected bad-event control throughout a fixed
replica horizon, using one strict-height family. All requested counts share tau,
cuts and masks; no independent replacement family or rare-cell normalization is
used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeLawFamilyApproximation
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights SphericalGGTreeRecurrence
open SphericalGGTreeRecurrenceControlled
open FiniteGGBoundaryBands FiniteGGPrechosenPolynomialFamily FiniteGGParameterScorePartition
open FiniteGGMonotoneBoundaryCuts FiniteGGProductCutMasks
open FiniteNestedPartition FiniteNestedLawComparison FiniteNestedDiscountedPartitionLaw
open FiniteNestedStrictSurrogate FiniteNestedLawAverage
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Approximation of the entire finite tree probability law, with GG and coarsening
errors estimated. The strict parameter and finite family are chosen before the
physical model.
-/
theorem exists_uniform_tree_law_family_approximation (R depth : ℕ) (hR : 0<R)
    (a b : Fin depth→ℝ) (ha : ∀l,-1<a l) (hab : ∀l,a l<b l) (hb : ∀l,b l≤1)
    (hSep : ∀l j : Fin depth,l<j→b l≤a j) {epsLaw epsBad etaCap : ℝ} (hepsLaw : 0<epsLaw) (hepsBad : 0<epsBad) (hEtaCap : 0<etaCap) :
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
              q.1.1∈cutCell good index ∧ ¬thresholdGood (cuts index) q.2}≤epsBad := by
  classical
  let S : ℝ := ∑j ∈ Finset.Ico 1 R,((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)/(j : ℝ))
  have hS : 0≤S := Finset.sum_nonneg (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (by positivity) (Nat.cast_nonneg _)))
  let tau : ℝ := min 1 (epsLaw/(2*(S+1)))
  have htau : 0<tau := lt_min (by norm_num) (div_pos hepsLaw (by positivity))
  have htau1 : tau≤1 := min_le_left _ _
  have hTau : tau*(2*(S+1))≤epsLaw := (le_div_iff₀ (by positivity : 0<2*(S+1))).mp (min_le_right _ _)
  have hTauCost : tau*S≤epsLaw/2 := by nlinarith only [hTau,htau.le]
  let common : ℝ := min (epsLaw/2) epsBad
  have hCommon : 0<common := lt_min (by positivity) hepsBad
  obtain ⟨eta,hEta,hEta1,hEtaCapLe,J,hJ,hBudget,P,Q,hDegree,hApprox,hGlobal,hMain⟩ :=
    exists_uniform_controlled_tree_recurrences R depth a b ha hab hb hSep hCommon hEtaCap
  refine ⟨tau,htau,htau1,eta,hEta,hEta1,hEtaCapLe,J,hJ,hBudget,P,Q,hDegree,hApprox,hGlobal,?_⟩
  intro K hK
  obtain ⟨V,hV,hSmall⟩ := hMain K hK
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hv0
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (a l) (b l) J (P l) eta
  let E : (Fin depth→Fin J)→Set (Fin K→ℝ) := cutCell good
  let cuts : (Fin depth→Fin J)→Fin depth→ℝ := fun index l ↦ threshold (a l) (b l) J (index l)
  have hCuts (index) : Monotone (cuts index) := (threshold_vector_strictMono a b hab hSep index).monotone
  let heights : (Fin depth→Fin J)→(Fin K→ℝ)→Fin depth→ℝ := fun index x l ↦ lowerHeight nu v (cuts index l) x
  have hHeight0 (index) (x) : ∀l,0≤heights index x l := (own_lower_heights_properties nu hv0 (cuts index) (hCuts index) x).1
  have hHeightMono (index) (x) : Monotone (heights index x) := (own_lower_heights_properties nu hv0 (cuts index) (hCuts index) x).2.1
  have hHeight1 (index) (x) : ∀l,heights index x l≤1 := (own_lower_heights_properties nu hv0 (cuts index) (hCuts index) x).2.2
  let actual : (Fin depth→Fin J)→(m : ℕ)→(Fin K→ℝ)→PMF (NestedPartition depth m) :=
    fun index m x ↦ treePMF (cuts index) (hCuts index) (law d (G.sectR x) m)
  let reference : (m : ℕ)→(Fin depth→Fin J)→(Fin K→ℝ)→PMF (NestedPartition depth m) := fun m index x ↦
    partitionPMF depth m (strictHeightApprox depth (heights index x) tau) 0 (le_refl 0)
      (strictHeightApprox_pos depth (heights index x) tau (hHeight0 index x) htau htau1)
      (strictHeightApprox_strictMono depth (heights index x) tau (hHeightMono index x) htau htau1)
      (fun l ↦ (strictHeightApprox_lt_one depth (heights index x) tau (hHeight1 index x) htau htau1 l).le)
  obtain ⟨hMasks,hDisj,hCover,_,_,_⟩ := product_parameter_partition d G (unitOverlap_measurable N)
    unitOverlap_mem_Icc a b (fun _ ↦ eta) hab hJ (fun _ ↦ hBudget) P hApprox hGlobal
  have hAtoms (index) (m) (t : NestedPartition depth m) : Measurable (fun x ↦ (actual index m x t).toReal) :=
    actual_treePMF_atom_measurable nu hv0 (cuts index) (hCuts index) t
  have hRowIntegral (index) (j : ℕ) :
      (∫x,recurrenceResidual depth j (heights index x) (actual index j x) (actual index (j+1) x)
        ∂(positiveCubeLaw K).restrict (E index))=
      (∫x,(E index).indicator (fun x ↦ recurrenceResidual depth j (heights index x)
        (actual index j x) (actual index (j+1) x)) x ∂positiveCubeLaw K) :=
    (integral_indicator (hMasks index)).symm
  have hRowTau : (∑j ∈ Finset.Ico 1 R,((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)*tau/(j : ℝ)))=tau*S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  intro m hm hmR
  have hSubset : Finset.Ico 1 m⊆Finset.Ico 1 R := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,(Finset.mem_Ico.mp hj).2.trans_le hmR⟩
  have hPartial : (∑j ∈ Finset.Ico 1 m,((j*depth+1 : ℕ) : ℝ)*(((j : ℝ)+1)*tau/(j : ℝ)))≤tau*S := by
    rw [← hRowTau]
    apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
    intro j _ _
    positivity
  have hAvg (index) : (∫x,l1Distance (actual index m x) (reference m index x)
      ∂(positiveCubeLaw K).restrict (E index))≤
      (∑j ∈ Finset.Ico 1 m,∫x,(E index).indicator (fun x ↦ recurrenceResidual depth j (heights index x)
        (actual index j x) (actual index (j+1) x)) x ∂positiveCubeLaw K)+
      ((positiveCubeLaw K).restrict (E index)).real univ*(tau*S) := by
    have H := averaged_surrogate_l1_le depth m (heights index)
      (own_lower_heights_measurable nu hv0 (cuts index)) (hHeight0 index) (hHeightMono index) (hHeight1 index)
      tau htau htau1 (actual index) (hAtoms index) ((positiveCubeLaw K).restrict (E index)) hm
    simp_rw [hRowIntegral] at H
    exact H.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hPartial measureReal_nonneg))
  have hMass : (∑index : Fin depth→Fin J,((positiveCubeLaw K).restrict (E index)).real univ)=1 := by
    simp only [measureReal_restrict_apply MeasurableSet.univ,univ_inter]
    have H := measureReal_iUnion_fintype (μ := positiveCubeLaw K) (fun i j hij ↦ hDisj i j hij) hMasks
    rw [hCover,probReal_univ] at H
    exact H.symm
  have hTotal := Finset.sum_le_sum (s := Finset.univ) (fun index _ ↦ hAvg index)
  rw [Finset.sum_add_distrib,Finset.sum_comm,← Finset.sum_mul,hMass,one_mul] at hTotal
  have hEach (j : ℕ) (hj : j∈Finset.Ico 1 m) :
      (∑index : Fin depth→Fin J,∫x,(E index).indicator (fun x ↦ recurrenceResidual depth j (heights index x)
        (actual index j x) (actual index (j+1) x)) x ∂positiveCubeLaw K)≤(epsLaw/2)/((R : ℝ)+1) := by
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hjN := ((Finset.mem_Ico.mp hj).2).trans_le hmR
    let r : Fin R := ⟨j-1,by omega⟩
    have hr1 : r.val+1=j := by dsimp only [r]; omega
    have hr2 : r.val+2=j+1 := by dsimp only [r]; omega
    have H := (hSmall nu v hv r).1
    change (∑index : Fin depth→Fin J,∫x,(E index).indicator (fun x ↦ recurrenceResidual depth (r.val+1) (heights index x)
      (actual index (r.val+1) x) (actual index (r.val+2) x)) x ∂positiveCubeLaw K)≤common/((R : ℝ)+1) at H
    let step : ℕ→ℝ := fun q ↦ ∑index : Fin depth→Fin J,∫x,(E index).indicator
      (fun x ↦ recurrenceResidual depth q (heights index x) (actual index q x) (actual index (q+1) x)) x ∂positiveCubeLaw K
    have H' : step (r.val+1)≤common/((R : ℝ)+1) := H
    rw [hr1] at H'
    exact H'.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have hRows : (∑j ∈ Finset.Ico 1 m,∑index : Fin depth→Fin J,
      ∫x,(E index).indicator (fun x ↦ recurrenceResidual depth j (heights index x)
        (actual index j x) (actual index (j+1) x)) x ∂positiveCubeLaw K)≤epsLaw/2 := by
    have H := Finset.sum_le_sum (s := Finset.Ico 1 m) (fun j hj ↦ hEach j hj)
    simp only [Finset.sum_const,nsmul_eq_mul] at H
    have hCard : ((Finset.Ico 1 m).card : ℝ)≤(R : ℝ)+1 := by
      have H : (Finset.Ico 1 m).card≤R+1 := by rw [Nat.card_Ico]; omega
      exact_mod_cast H
    have hPos : 0≤(epsLaw/2)/((R : ℝ)+1) := by positivity
    have HB := mul_le_mul_of_nonneg_right hCard hPos
    have hEq : ((R : ℝ)+1)*((epsLaw/2)/((R : ℝ)+1))=epsLaw/2 :=
      mul_div_cancel₀ (epsLaw/2) (by positivity : (R : ℝ)+1≠0)
    exact H.trans (HB.trans_eq hEq)
  refine ⟨?_,?_⟩
  · change (∑index : Fin depth→Fin J,∫x,l1Distance (actual index m x) (reference m index x)
      ∂(positiveCubeLaw K).restrict (E index))≤epsLaw
    linarith only [hTotal,hRows,hTauCost]
  · let r : Fin R := ⟨m-1,by omega⟩
    have H := (hSmall nu v hv r).2.1
    change (jointLaw (K := K) nu v (m-1)).real {q | ∃index : Fin depth→Fin J,
      q.1.1∈E index ∧ ¬thresholdGood (cuts index) q.2}≤common/((R : ℝ)+1) at H
    have hDiv : common/((R : ℝ)+1)≤common := by
      apply (div_le_iff₀ (by positivity : 0<(R : ℝ)+1)).2
      have HB := mul_le_mul_of_nonneg_left (show (1 : ℝ)≤(R : ℝ)+1 by have HB := Nat.cast_nonneg (α := ℝ) R; linarith only [HB]) hCommon.le
      simpa only [mul_one] using HB
    exact H.trans (hDiv.trans (min_le_right _ _))

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeLawFamilyApproximation
