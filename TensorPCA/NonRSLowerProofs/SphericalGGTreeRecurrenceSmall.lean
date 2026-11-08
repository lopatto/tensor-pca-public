-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceAverage
public import TensorPCA.NonRSLowerProofs.FiniteGGPrechosenCutVectors
public import TensorPCA.NonRSLowerProofs.SphericalGGProductCutCoarsening

/-! One prechosen cut family gives small full-PMF recurrence errors throughout a fixed
replica horizon. Errors are measured under each amplitude's pair law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceSmall
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.GaussianGGIndicatorTransfer
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalFirstJetPowerBudget SphericalGGWeightObservable SphericalGGJetFamily
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeRecurrence SphericalGGTreeRecurrenceAverage
open FiniteGGBoundaryBands FiniteGGPrechosenPolynomialFamily FiniteGGParameterScorePartition
open FiniteGGMonotoneBoundaryCuts FiniteGGProductCutMasks FiniteGGPrechosenCutVectors
open SphericalGGProductCutCoarsening
open FiniteNestedPartition FiniteNestedLawComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Product first-good cells retain their score-approximation budget under cube
integration, with each score measured under its amplitude's pair law and no factor
for the number of alternatives.
-/
theorem product_score_integral_budget {N K depth J : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (a b : Fin depth→ℝ) (hab : ∀l,a l<b l) (eta : ℝ)
    (hJ : 0<J) (hBudget : 1/(J : ℝ)≤eta/2)
    (P : Fin depth→Fin J→Polynomial ℝ)
    (hApprox : ∀l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta/2)
    (hGlobal : ∀l j r,|extendTest ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    let good := fun l ↦ goodParameter (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      (parameterizedGibbsKernel nu v) unitOverlap (a l) (b l) J (P l) eta
    (∑index : Fin depth→Fin J,∑l : Fin depth,∫x,(cutCell good index).indicator
      (fun x ↦ pairMean nu v (fun r ↦ |(Ici (threshold (a l) (b l) J (index l))).indicator (fun _ ↦ (1 : ℝ)) r-
        extendTest ((P l (index l)).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K)≤(depth : ℝ)*eta := by
  dsimp only
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (a l) (b l) J (P l) eta
  let T : (Fin depth→Fin J)→Fin depth→ℝ→ℝ := fun index l r ↦
    |(Ici (threshold (a l) (b l) J (index l))).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest ((P l (index l)).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|
  obtain ⟨hMasks,_,_,_,hOwn,_⟩ := product_parameter_partition d G (unitOverlap_measurable N)
    unitOverlap_mem_Icc a b (fun _ ↦ eta) hab hJ (fun _ ↦ hBudget) P hApprox hGlobal
  have hTm (index) (l) : Measurable (T index l) :=
    (continuous_abs.measurable : Measurable (abs : ℝ→ℝ)).comp
      ((measurable_const.indicator measurableSet_Ici).sub (extendTest_continuous _).measurable)
  have hTb (index) (l) (r : ℝ) : |T index l r|≤3 := by
    have hI : |(Ici (threshold (a l) (b l) J (index l))).indicator (fun _ ↦ (1 : ℝ)) r|≤1 := by
      by_cases h : r∈Ici (threshold (a l) (b l) J (index l)) <;> simp [h]
    dsimp only [T]
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith only [hI,hGlobal l (index l) r])
  have hInt (index) (l) : Integrable ((cutCell good index).indicator
      (fun x ↦ pairMean nu v (T index l) x)) (positiveCubeLaw K) := by
    apply (Integrable.of_bound (pairMean_measurable nu hv (hTm index l) (hTb index l)).aestronglyMeasurable 3
      (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using pairMean_abs_le nu hv (hTb index l) x))).indicator
    exact hMasks index
  have hPoint (x : Fin K→ℝ) : (∑index : Fin depth→Fin J,∑l : Fin depth,(cutCell good index).indicator
      (fun x ↦ pairMean nu v (T index l) x) x)≤(depth : ℝ)*eta := by
    have H := hOwn x
    have hEq : (∑index : Fin depth→Fin J,∑l : Fin depth,(cutCell good index).indicator
        (fun x ↦ pairMean nu v (T index l) x) x)=
        ∑index : Fin depth→Fin J,(cutCell good index).indicator (fun x ↦ ∑l : Fin depth,
          ownScoreL1 d G unitOverlap (threshold (a l) (b l) J (index l)) (P l (index l)) x) x := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases hx : x∈cutCell good index
      · simp only [indicator_of_mem hx]
        apply Finset.sum_congr rfl
        intro l _
        simp only [T,pairMean,ownScoreL1,abs_sub_comm,d,G]
      · simp only [indicator_of_notMem hx,Finset.sum_const_zero]
    rw [hEq]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
  have hFI := integrable_finsetSum Finset.univ (fun index _ ↦ integrable_finsetSum Finset.univ (fun l _ ↦ hInt index l))
  have H := integral_mono hFI (integrable_const ((depth : ℝ)*eta)) hPoint
  rw [integral_finsetSum Finset.univ (fun index _ ↦ integrable_finsetSum Finset.univ (fun l _ ↦ hInt index l))] at H
  simp_rw [integral_finsetSum Finset.univ (fun l _ ↦ hInt _ l)] at H
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using H


/-- One prechosen family works throughout the replica horizon. Numerical approximation
and ultrametricity budgets are chosen before the model; full finite PMFs use the
same cuts at every count.
-/
theorem exists_uniform_small_tree_recurrences (R depth : ℕ) (a b : Fin depth→ℝ)
    (ha : ∀l,-1<a l) (hab : ∀l,a l<b l) (hb : ∀l,b l≤1)
    (hSep : ∀l j : Fin depth,l<j→b l≤a j) {eps : ℝ} (heps : 0<eps) :
    ∃ eta : ℝ,0<eta ∧ eta≤1 ∧ ∃ J : ℕ,0<J ∧ 1/(J : ℝ)≤eta/2 ∧
      ∃ P : Fin depth→Fin J→Polynomial ℝ,∃ Q : ℕ,
        (∀l j,(P l j).natDegree≤Q) ∧
        (∀l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta/2) ∧
        (∀l j r,|extendTest ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) ∧
        ∀K : ℕ,Q≤K → ∃ V : ℝ,∃ hV : 1≤V,
          ∀ {N : ℕ} (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : V≤v),
            letI := parameterizedGibbsKernel_markov (K := K) nu ((by norm_num : (0 : ℝ)≤1).trans (hV.trans hv))
            let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
            let G := fun x : Fin K→ℝ ↦ (parameterizedGibbsKernel nu v).sectR x
            let good := fun l ↦ goodParameter d (parameterizedGibbsKernel nu v)
              unitOverlap (a l) (b l) J (P l) eta
            let cuts := fun (index : Fin depth→Fin J) l ↦ threshold (a l) (b l) J (index l)
            ∀r : Fin R,(∑index : Fin depth→Fin J,∫x,(cutCell good index).indicator
              (fun x ↦ recurrenceResidual depth (r.val+1) (fun l ↦ lowerHeight nu v (cuts index l) x)
                (treePMF (cuts index) (threshold_vector_strictMono a b hab hSep index).monotone (law d (G x) (r.val+1)))
                (treePMF (cuts index) (threshold_vector_strictMono a b hab hSep index).monotone (law d (G x) (r.val+2)))) x
                ∂positiveCubeLaw K)≤eps/((R : ℝ)+1) := by
  classical
  let count : Fin R→ℝ := fun r ↦
    Fintype.card (Σt : NestedPartition depth (r.val+1),Insertion depth (r.val+1) t)
  have hCount0 (r : Fin R) : 0≤count r := Nat.cast_nonneg _
  let M : ℝ := 1+∑r : Fin R,count r
  have hM1 : 1≤M := by
    have H : 0≤∑r : Fin R,count r := Finset.sum_nonneg (fun r _ ↦ hCount0 r)
    dsimp only [M]
    linarith only [H]
  have hMr (r : Fin R) : count r≤M := by
    have H := Finset.single_le_sum (fun j _ ↦ hCount0 j) (Finset.mem_univ r)
    dsimp only [M]
    linarith only [H]
  let L : ℝ := (R : ℝ)+3
  have hL : 0<L := by dsimp only [L]; positivity
  let C : ℝ := 2*M*L+1
  have hC1 : 1≤C := by
    have H := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) ((by norm_num : (0 : ℝ)≤1).trans hM1)) hL.le
    dsimp only [C]
    linarith only [H]
  have hC : 0<C := lt_of_lt_of_le zero_lt_one hC1
  let target : ℝ := eps/((R : ℝ)+1)
  have ht : 0<target := div_pos heps (by positivity)
  let eta : ℝ := min 1 (target/(16*C*(L^2+1)*((depth : ℝ)+1)))
  have hDen : 0<16*C*(L^2+1)*((depth : ℝ)+1) := by positivity
  have hEta : 0<eta := lt_min (by norm_num) (div_pos ht hDen)
  have hEta1 : eta≤1 := min_le_left _ _
  have hEtaCost : eta*(16*C*(L^2+1)*((depth : ℝ)+1))≤target :=
    (le_div_iff₀ hDen).mp (min_le_right _ _)
  let delta : ℝ := target/(16*C)
  have hDelta : 0<delta := div_pos ht (by positivity)
  have hDeltaEq : delta*(16*C)=target := div_mul_cancel₀ target (by positivity : 16*C≠0)
  obtain ⟨J,hJ,hBudget,P,D,hDegree,hApprox,hGlobal⟩ :=
    exists_prechosen_cut_polynomials depth a b hEta hEta1
  choose gapOld hGapOld QOld hOld using (fun r : Fin R ↦
    exists_uniform_product_cut_threshold r.val depth J a b (fun _ ↦ eta) hab hb hJ (fun _ ↦ hBudget) P hApprox hGlobal hDelta)
  choose gapNext hGapNext QNext hNext using (fun r : Fin R ↦
    exists_uniform_product_cut_threshold (r.val+1) depth J a b (fun _ ↦ eta) hab hb hJ (fun _ ↦ hBudget) P hApprox hGlobal hDelta)
  choose VGG hVGG hGG using (fun r : Fin R ↦ exists_uniform_finite_cell_recurrence_threshold
    depth r.val (fun (index : Fin depth→Fin J) l ↦ P l (index l)) (show 0<target/2 by positivity))
  let Q : ℕ := D+∑r : Fin R,(QOld r+QNext r)
  have hDQ : D≤Q := by dsimp only [Q]; omega
  have hOldQ (r : Fin R) : QOld r≤Q := by
    have H := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (QOld j+QNext j)) (Finset.mem_univ r)
    dsimp only [Q]
    omega
  have hNextQ (r : Fin R) : QNext r≤Q := by
    have H := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (QOld j+QNext j)) (Finset.mem_univ r)
    dsimp only [Q]
    omega
  refine ⟨eta,hEta,hEta1,J,hJ,hBudget,P,Q,(fun l j ↦ (hDegree l j).trans hDQ),hApprox,hGlobal,?_⟩
  intro K hK
  choose VOld hVOld hOldMain using (fun r : Fin R ↦ hOld r K ((hOldQ r).trans hK))
  choose VNext hVNext hNextMain using (fun r : Fin R ↦ hNext r K ((hNextQ r).trans hK))
  let V : ℝ := 1+∑r : Fin R,(VGG r+VOld r+VNext r)
  have hTerms (r : Fin R) : 0≤VGG r+VOld r+VNext r := by linarith only [hVGG r,hVOld r,hVNext r]
  have hV : 1≤V := by
    have H : 0≤∑r : Fin R,(VGG r+VOld r+VNext r) := Finset.sum_nonneg (fun r _ ↦ hTerms r)
    dsimp only [V]
    linarith only [H]
  have hDom (r : Fin R) : VGG r≤V ∧ VOld r≤V ∧ VNext r≤V := by
    have H := Finset.single_le_sum (fun j _ ↦ hTerms j) (Finset.mem_univ r)
    dsimp only [V]
    exact ⟨by linarith only [H,hVOld r,hVNext r],by linarith only [H,hVGG r,hVNext r],by linarith only [H,hVGG r,hVOld r]⟩
  refine ⟨V,hV,?_⟩
  intro N nu hnu v hv
  have hv0 : 0≤v := (by norm_num : (0 : ℝ)≤1).trans (hV.trans hv)
  letI := parameterizedGibbsKernel_markov (K := K) nu hv0
  dsimp only
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := parameterizedGibbsKernel (K := K) nu v
  let good := fun l ↦ goodParameter d G unitOverlap (a l) (b l) J (P l) eta
  let cuts : (Fin depth→Fin J)→Fin depth→ℝ := fun index l ↦ threshold (a l) (b l) J (index l)
  let E : (Fin depth→Fin J)→Set (Fin K→ℝ) := cutCell good
  have hCuts (index) : Monotone (cuts index) := (threshold_vector_strictMono a b hab hSep index).monotone
  have hCuts1 (index) (l) : cuts index l≤1 := (threshold_vector_lt_one a b hab hb index l).le
  obtain ⟨hMasks,hDisj,_,_,_,_⟩ := product_parameter_partition d G (unitOverlap_measurable N)
    unitOverlap_mem_Icc a b (fun _ ↦ eta) hab hJ (fun _ ↦ hBudget) P hApprox hGlobal
  let Own : ℝ := ∑index : Fin depth→Fin J,∑l : Fin depth,∫x,(E index).indicator
    (fun x ↦ pairMean nu v (fun r ↦ |(Ici (cuts index l)).indicator (fun _ ↦ (1 : ℝ)) r-
      extendTest ((P l (index l)).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|) x) x ∂positiveCubeLaw K
  have hOwn : Own≤(depth : ℝ)*eta := product_score_integral_budget nu hv0 a b hab eta hJ hBudget P hApprox hGlobal
  let Bad : ℕ→ℝ := fun m ↦ (jointLaw (K := K) nu v m).real
    {q | ∃index : Fin depth→Fin J,q.1.1∈E index ∧ ¬thresholdGood (cuts index) q.2}
  have hBadEq (m : ℕ) : (∑index : Fin depth→Fin J,∫x,(E index).indicator (fun x ↦
      (law d (G.sectR x) (m+1)).real {s | ¬thresholdGood (cuts index) s}) x ∂positiveCubeLaw K)=Bad m :=
    selected_bad_mass_eq_joint nu hv0 cuts hCuts E hMasks hDisj
  have hDE : 0≤(depth : ℝ)*eta := mul_nonneg (Nat.cast_nonneg _) hEta.le
  let W : ℝ := delta+L^2*((depth : ℝ)*eta)
  have hW : 0≤W := add_nonneg hDelta.le (mul_nonneg (sq_nonneg _) hDE)
  have hBadBound (z : ℝ) (hz : 0≤z) (hzL : z≤L) {mass : ℝ}
      (hMass : mass<delta+z^2*((depth : ℝ)*(eta/2))) : mass≤W := by
    have hSq : z^2≤L^2 := by simpa only [pow_two] using mul_le_mul hzL hzL hz hL.le
    have hHalf : (depth : ℝ)*(eta/2)≤(depth : ℝ)*eta :=
      mul_le_mul_of_nonneg_left (by linarith only [hEta.le]) (Nat.cast_nonneg _)
    have H := mul_le_mul hSq hHalf (by positivity : 0≤(depth : ℝ)*(eta/2)) (sq_nonneg L)
    exact hMass.le.trans (add_le_add le_rfl H)
  intro r
  have hrR : (r.val : ℝ)≤(R : ℝ) := by exact_mod_cast r.isLt.le
  have hr2 : (r.val : ℝ)+2≤L := by dsimp only [L]; linarith only [hrR]
  have hr3 : (r.val : ℝ)+3≤L := by dsimp only [L]; linarith only [hrR]
  have HOld := hOldMain r nu v ((hDom r).2.1.trans hv)
  have HNext := hNextMain r nu v ((hDom r).2.2.trans hv)
  dsimp only at HOld HNext
  change Bad r.val<delta+((r.val+1 : ℕ) : ℝ)^2*(∑_l : Fin depth,eta/2) at HOld
  change Bad (r.val+1)<delta+((r.val+2 : ℕ) : ℝ)^2*(∑_l : Fin depth,eta/2) at HNext
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at HOld HNext
  have hBOld : Bad r.val≤W := hBadBound ((r.val : ℝ)+1) (by positivity) (by linarith only [hr2]) HOld
  have hBNext : Bad (r.val+1)≤W := hBadBound ((r.val : ℝ)+2) (by positivity) hr2 (by simpa only [add_assoc,one_add_one_eq_two] using HNext)
  have H := hGG r (fun index l ↦ (hDegree l (index l)).trans (hDQ.trans hK)) nu v ((hDom r).1.trans hv)
    cuts hCuts hCuts1 E hMasks (fun index l z ↦ hGlobal l (index l) z)
  dsimp only at H
  rw [hBadEq (r.val+1),hBadEq r.val] at H
  change _≤target/2+2*count r*((r.val : ℝ)+2)*Own+(count r*((r.val : ℝ)+3)+1)*Bad (r.val+1)+Bad r.val at H
  have hScoreCoeff : 2*count r*((r.val : ℝ)+2)≤C := by
    have H0 := mul_le_mul (hMr r) hr2 (by positivity : 0≤(r.val : ℝ)+2) ((by norm_num : (0 : ℝ)≤1).trans hM1)
    dsimp only [C]
    nlinarith only [H0]
  have hNextCoeff : count r*((r.val : ℝ)+3)+1≤C := by
    have H0 := mul_le_mul (hMr r) hr3 (by positivity : 0≤(r.val : ℝ)+3) ((by norm_num : (0 : ℝ)≤1).trans hM1)
    have H1 := mul_nonneg ((by norm_num : (0 : ℝ)≤1).trans hM1) hL.le
    dsimp only [C]
    nlinarith only [H0,H1]
  have hScoreCost : 2*count r*((r.val : ℝ)+2)*Own≤C*((depth : ℝ)*eta) :=
    (mul_le_mul_of_nonneg_left hOwn (by positivity : 0≤2*count r*((r.val : ℝ)+2))).trans
      (mul_le_mul_of_nonneg_right hScoreCoeff hDE)
  have hNextCost : (count r*((r.val : ℝ)+3)+1)*Bad (r.val+1)≤C*W :=
    (mul_le_mul_of_nonneg_left hBNext (by positivity : 0≤count r*((r.val : ℝ)+3)+1)).trans
      (mul_le_mul_of_nonneg_right hNextCoeff hW)
  have hOldCost : Bad r.val≤C*W := hBOld.trans (by nlinarith only [hC1,hW])
  have hEtaTerm : C*(1+2*L^2)*((depth : ℝ)*eta)≤target/8 := by
    have hExtra : 0≤C*eta*((depth : ℝ)+2*L^2+2) := by positivity
    have hScale : 2*C*(L^2+1)*((depth : ℝ)+1)*eta≤target/8 := by nlinarith only [hEtaCost]
    nlinarith only [hExtra,hScale]
  have hDeltaTerm : 2*C*delta=target/8 := by nlinarith only [hDeltaEq]
  change _≤target
  dsimp only [W] at hNextCost hOldCost
  nlinarith only [H,hScoreCost,hNextCost,hOldCost,hEtaTerm,hDeltaTerm,ht.le]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrenceSmall
