-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGParameterScorePartition
public import TensorPCA.NonRSLowerProofs.FiniteGGMonotoneBoundaryCuts

/-! Finite product cells of the prechosen first-good restrictions. Each cell depends
only on amplitude; Gaussian disorder is averaged under the pair law for that
amplitude. A unique active cell avoids a loss proportional to the number of cut
vectors.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGProductCutMasks
open MeasureTheory ProbabilityTheory Set
open FiniteGGFirstGoodPartition FiniteGGParameterScorePartition FiniteGGBoundaryBands
open FiniteGGPrechosenPolynomialFamily
open scoped BigOperators
noncomputable section
variable {X Omega V : Type*} [MeasurableSpace X] [MeasurableSpace Omega] [MeasurableSpace V]

def cutCell {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (index : Fin depth → Fin J) : Set X := ⋂ l,firstGood (good l) (index l)

theorem cutCell_measurable {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (hGood : ∀ l j,MeasurableSet (good l j)) (index : Fin depth → Fin J) :
    MeasurableSet (cutCell good index) :=
  MeasurableSet.iInter (fun l ↦ firstGood_measurable (good l) (hGood l) (index l))

theorem cutCell_subset {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (index : Fin depth → Fin J) (l : Fin depth) : cutCell good index⊆good l (index l) := by
  intro x hx
  exact firstGood_subset (good l) (index l) (mem_iInter.mp hx l)

theorem cutCell_disjoint {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    {index other : Fin depth → Fin J} (h : index≠other) :
    Disjoint (cutCell good index) (cutCell good other) := by
  classical
  have hSome : ∃ l,index l≠other l := by
    by_contra hNot
    apply h
    funext l
    by_contra hNe
    exact hNot ⟨l,hNe⟩
  obtain ⟨l,hl⟩ := hSome
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (Set.disjoint_left.mp (firstGood_disjoint (good l) hl))
    (mem_iInter.mp hx l) (mem_iInter.mp hy l)

theorem exists_cutCell {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (hExists : ∀ l x,∃ j,x∈good l j) (x : X) : ∃ index,x∈cutCell good index := by
  classical
  choose index hIndex using (fun l ↦ exists_firstGood (good l) x (hExists l x))
  exact ⟨index,mem_iInter.mpr hIndex⟩

theorem cutCell_cover {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (hExists : ∀ l x,∃ j,x∈good l j) : (⋃ index,cutCell good index)=univ := by
  ext x
  simp only [mem_iUnion,mem_univ,iff_true]
  exact exists_cutCell good hExists x

theorem sum_cutCell_restrictions_le {depth J : ℕ} (good : Fin depth → Fin J → Set X)
    (hExists : ∀ l x,∃ j,x∈good l j)
    (error : Fin depth → Fin J → X → ℝ) (budget : Fin depth → ℝ)
    (hBound : ∀ l j x,x∈good l j→error l j x≤budget l) (x : X) :
    (∑ index : Fin depth → Fin J,(cutCell good index).indicator
      (fun x ↦ ∑ l,error l (index l) x) x)≤∑ l,budget l := by
  classical
  obtain ⟨index,hIndex⟩ := exists_cutCell good hExists x
  have hOthers (other : Fin depth → Fin J) (hNe : other≠index) : x∉cutCell good other :=
    fun ho ↦ (Set.disjoint_left.mp (cutCell_disjoint good hNe)) ho hIndex
  calc
    _ = (cutCell good index).indicator (fun x ↦ ∑ l,error l (index l) x) x :=
      Finset.sum_eq_single (f := fun other : Fin depth → Fin J ↦
        (cutCell good other).indicator (fun x ↦ ∑ l,error l (other l) x) x)
        index (fun other _ hNe ↦ indicator_of_notMem (hOthers other hNe) _)
        (fun hNot ↦ False.elim (hNot (Finset.mem_univ index)))
    _ = ∑ l,error l (index l) x := indicator_of_mem hIndex _
    _ ≤ _ := Finset.sum_le_sum (fun l _ ↦ hBound l (index l) x (cutCell_subset good index l hIndex))

theorem product_parameter_partition (d : Measure Omega) [IsProbabilityMeasure d]
    (K : Kernel (X×Omega) V) [IsMarkovKernel K] {R : V → V → ℝ}
    (hR : Measurable (fun p : V×V ↦ R p.1 p.2)) (hUnit : ∀ u v,R u v∈Icc (-1 : ℝ) 1)
    {depth J : ℕ} (a b eta : Fin depth → ℝ) (hab : ∀ l,a l<b l)
    (hJ : 0<J) (hBudget : ∀ l,1/(J : ℝ)≤eta l/2)
    (P : Fin depth → Fin J → Polynomial ℝ)
    (hApprox : ∀ l j,‖(P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)-rampTest (a l) (b l) J j‖≤eta l/2)
    (hGlobal : ∀ l j r,|NonRSUpperProofs.GaussianGGIndicatorTransfer.extendTest
      ((P l j).toContinuousMapOn (Icc (-1 : ℝ) 1)) r|≤2) :
    let good := fun l ↦ goodParameter d K R (a l) (b l) J (P l) (eta l)
    (∀ index,MeasurableSet (cutCell good index)) ∧
    (∀ index other,index≠other→Disjoint (cutCell good index) (cutCell good other)) ∧
    (⋃ index,cutCell good index)=univ ∧
    (∀ index x,x∈cutCell good index→∀ l,x∈goodParameter d K R (a l) (b l) J (P l) (eta l) (index l)) ∧
    (∀ x,(∑ index : Fin depth → Fin J,(cutCell good index).indicator
      (fun x ↦ ∑ l,ownScoreL1 d K R (threshold (a l) (b l) J (index l)) (P l (index l)) x) x)≤∑ l,eta l) ∧
    ∀ x,(∑ index : Fin depth → Fin J,(cutCell good index).indicator
      (fun x ↦ ∑ l,(((((K.sectR x)×ₖ(K.sectR x))∘ₘd).map
        (fun p : V×V ↦ R p.1 p.2)).real (band (a l) (b l) J (index l)))) x)≤∑ l,eta l/2 := by
  dsimp only
  let good := fun l ↦ goodParameter d K R (a l) (b l) J (P l) (eta l)
  have hGood : ∀ l j,MeasurableSet (good l j) :=
    fun l j ↦ goodParameter_measurable d K hR (a l) (b l) J (P l) (eta l) (hGlobal l) j
  have hExists : ∀ l x,∃ j,x∈good l j := fun l x ↦
    exists_goodParameter d K hR hUnit (hab l) J hJ (hBudget l) (P l) (hApprox l) x
  refine ⟨cutCell_measurable good hGood,(fun _ _ h ↦ cutCell_disjoint good h),
    cutCell_cover good hExists,(fun index x hx l ↦ cutCell_subset good index l hx),?_,?_⟩
  · intro x
    exact sum_cutCell_restrictions_le good hExists _ eta (fun _ _ _ hx ↦ hx.2) x
  · intro x
    exact sum_cutCell_restrictions_le good hExists _ (fun l ↦ eta l/2) (fun _ _ _ hx ↦ hx.1) x

end
end TensorPCA.NonRSLowerProofs.FiniteGGProductCutMasks
