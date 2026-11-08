-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCellAverage
public import TensorPCA.NonRSLowerProofs.SphericalGGSelectedOwnHeights
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRecurrence
public import TensorPCA.NonRSLowerProofs.SphericalGGPhysicalTreeCoupling
public import TensorPCA.NonRSLowerProofs.FiniteCavityObservedPopulationMoments

/-! Compare population and Gaussian replica moments with the unconditional marked moment
of the selected strict-height hierarchy. Its heights use the same section pair laws.
Every selected cell retains its original mass, and the common Gaussian root is
introduced once.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGObservedMarkedMoments
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteNestedStrictSurrogate
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianLawAverage FiniteNestedGaussianCellAverage
open FiniteNestedLawComparison SphericalGGTreeExtraction SphericalGGTreeHeights SphericalGGTreeRecurrence
open SphericalGGTreeCylinder FiniteCavityNumeratorMoments
open SphericalGGSelectedOwnHeights SphericalGGPhysicalTreeCoupling SphericalGGWeightObservable
open FiniteGGPositiveGrid FiniteCavityIdealField FiniteCavityShellGibbsPartition
open FiniteCavityGaussianCompatibility GaussianCompactFeatureComparison
open scoped BigOperators RealInnerProductSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem actual_tree_product_error_le_l1 {I : Type*} [Fintype I] {N K depth n M : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cell : I→Set (Fin K→ℝ)) (hCell : ∀i,MeasurableSet (cell i))
    (hDis : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (cuts : I→Fin depth→ℝ) (hCuts : ∀i,Monotone (cuts i))
    {tau : ℝ} (htau : 0<tau) (htau1 : tau≤1)
    (y : Fin (depth+1)→ℝ) {Z : Model.Vector M→ℝ} (hZ : Measurable Z)
    (hBound : ∀z,Z z∈Icc (0 : ℝ) 1) :
    letI := parameterizedGibbsKernel_markov (K := K) nu hv
    let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
    let P := fun i amp ↦ treePMF (cuts i) (hCuts i)
      (law d ((parameterizedGibbsKernel nu v).sectR amp) n)
    let x := fun i amp ↦ strictHeightApprox depth (fun l ↦ lowerHeight nu v (cuts i l) amp) tau
    |(∑i,∫amp in cell i,∑t : NestedPartition depth n,(P i amp t).toReal*treeProduct t y Z 0 ∂positiveCubeLaw K)-
      (∫amp,∫g : Model.Vector M,weightedMoment depth n
        (selectedOwnHeights nu v cell cuts tau amp) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (Real.sqrt (y 0) •g) ∂stdGaussian (Model.Vector M) ∂positiveCubeLaw K)|≤
      ∑i,∫amp in cell i,l1Distance (P i amp)
        (partitionPMF depth n (x i amp) 0 (le_refl 0)
          (strictHeightApprox_pos depth _ tau (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).1) htau htau1)
          (strictHeightApprox_strictMono depth _ tau
            ((own_lower_heights_properties nu hv (cuts i) (hCuts i) amp).2.1) htau htau1)
          (fun l ↦ (strictHeightApprox_lt_one depth _ tau
            (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).2) htau htau1 l).le)) ∂positiveCubeLaw K := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let P := fun i amp ↦ treePMF (cuts i) (hCuts i)
    (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR amp) n)
  let x : I→(Fin K→ℝ)→Fin depth→ℝ := fun i amp ↦
    strictHeightApprox depth (fun l ↦ lowerHeight nu v (cuts i l) amp) tau
  have hxs (i : I) : Measurable (x i) := (strictHeightApprox_joint_measurable depth).comp
    ((own_lower_heights_measurable nu hv (cuts i)).prodMk measurable_const)
  have hx (i : I) (amp) : ∀j,0<x i amp j := strictHeightApprox_pos depth _ tau
    (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).1) htau htau1
  have hxm (i : I) (amp) : StrictMono (x i amp) := strictHeightApprox_strictMono depth _ tau
    ((own_lower_heights_properties nu hv (cuts i) (hCuts i) amp).2.1) htau htau1
  have hx1 (i : I) (amp) : ∀j,x i amp j≤1 := fun j ↦
    (strictHeightApprox_lt_one depth _ tau (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).2) htau htau1 j).le
  have H := cell_product_error_le_l1 cell hCell hDis hCover x hxs hx hxm hx1 P
    (fun i t ↦ actual_treePMF_atom_measurable nu hv (cuts i) (hCuts i) t)
    y hZ (by norm_num : (0 : ℝ)≤1) hBound (0 : Model.Vector M) (positiveCubeLaw K)
  simpa only [one_pow,one_mul,zero_add,selectedOwnHeights] using H

theorem exists_selected_numerator_strict_moment (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : Model.Vector M→ℝ)
    (hMark : Continuous mark) (hBound : ∀z,mark z∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {I : Type u} [Fintype I] {N K depth : ℕ},0<depth →
      ∀ (cuts : I→Fin depth→ℝ) (hCuts : ∀i,Monotone (cuts i)),
      (∀i l,cuts i l∈Ioo (cutLeft depth l) (cutRight depth l))→
      ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : 0≤v),
      ∀ (cell : I→Set (Fin K→ℝ)),(∀i,MeasurableSet (cell i))→
      (∀i j,i≠j→Disjoint (cell i) (cell j))→(⋃i,cell i)=univ→
      ∀ (tau : ℝ) (htau : 0<tau) (htau1 : tau≤1),∀ (neg : ℝ),0≤neg → neg+1/(depth : ℝ)≤delta →
      letI := parameterizedGibbsKernel_markov (K := K) nu hv
      let y := fun l : Fin (depth+1) ↦ beta^2*deriv (Scalar.xiSlice k mu) (grid depth l)
      let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
      let P := fun i amp ↦ treePMF (cuts i) (hCuts i) (law d ((parameterizedGibbsKernel nu v).sectR amp) (r+1))
      let x := fun i amp ↦ strictHeightApprox depth (fun l ↦ lowerHeight nu v (cuts i l) amp) tau
      let Q := fun i amp ↦ partitionPMF depth (r+1) (x i amp) 0 (le_refl 0)
        (strictHeightApprox_pos depth _ tau (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).1) htau htau1)
        (strictHeightApprox_strictMono depth _ tau
          ((own_lower_heights_properties nu hv (cuts i) (hCuts i) amp).2.1) htau htau1)
        (fun l ↦ (strictHeightApprox_lt_one depth _ tau
          (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).2) htau htau1 l).le)
      |(∫q,(∫g : CavityDisorder N M k,∏i : Fin (r+1),mark (blockField k mu beta g (q.2 i).val)
          ∂stdGaussian (CavityDisorder N M k)) ∂jointLaw (K := K) nu v r)-
        (∫amp,∫g : Model.Vector M,weightedMoment depth (r+1)
          (selectedOwnHeights nu v cell cuts tau amp) 0
          (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
          mark (Real.sqrt (y 0) •g) ∂stdGaussian (Model.Vector M) ∂positiveCubeLaw K)|≤
        eps+(jointLaw (K := K) nu v r).real {q | ∃i,q.1.1∈cell i ∧ ¬thresholdGood (cuts i) q.2}+
          (jointLaw (K := K) nu v r).real {q | ∃i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg}+
          ∑i,∫amp in cell i,l1Distance (P i amp) (Q i amp) ∂positiveCubeLaw K := by
  obtain ⟨delta,hDelta,hPhysical⟩ := exists_selected_numerator_coupling r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro I hI N K depth hd cuts hCuts hCutsGrid nu hnu v hv cell hCell hDis hCover tau htau htau1 neg hNeg hMesh
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let y := fun l : Fin (depth+1) ↦ beta^2*deriv (Scalar.xiSlice k mu) (grid depth l)
  let P := fun i amp ↦ treePMF (cuts i) (hCuts i)
    (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR amp) (r+1))
  let A : ℝ := ∑i,∫amp in cell i,∑t : NestedPartition depth (r+1),
    (P i amp t).toReal*treeProduct t y mark 0 ∂positiveCubeLaw K
  have HP := hPhysical hd cuts hCuts hCutsGrid nu v hv cell hCell hDis hCover neg hNeg hMesh
  have hInd (i : I) :
      (∫amp,(cell i).indicator (fun amp ↦ ∑t : NestedPartition depth (r+1),
          (P i amp t).toReal*treeProduct t y mark 0) amp ∂positiveCubeLaw K)=
        ∫amp in cell i,∑t : NestedPartition depth (r+1),
          (P i amp t).toReal*treeProduct t y mark 0 ∂positiveCubeLaw K := integral_indicator (hCell i)
  have HP' : |(∫q,(∫g : CavityDisorder N M k,∏i : Fin (r+1),mark (blockField k mu beta g (q.2 i).val)
      ∂stdGaussian (CavityDisorder N M k)) ∂jointLaw (K := K) nu v r)-A|≤
      eps+(jointLaw (K := K) nu v r).real {q | ∃i,q.1.1∈cell i ∧ ¬thresholdGood (cuts i) q.2}+
        (jointLaw (K := K) nu v r).real {q | ∃i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg} := by
    have HM : (∑i,∫amp,(cell i).indicator (fun amp ↦ ∑t : NestedPartition depth (r+1),
        (P i amp t).toReal*treeProduct t y mark 0) amp ∂positiveCubeLaw K)=A := by
      dsimp only [A]
      exact Finset.sum_congr rfl (fun i _ ↦ hInd i)
    rw [← HM]
    simpa only [P,y,treeProduct,zero_add] using HP
  have HL := actual_tree_product_error_le_l1 (n := r+1) (M := M) nu hv cell hCell hDis hCover cuts hCuts
    htau htau1 y hMark.measurable hBound
  exact (abs_sub_le _ A _).trans (add_le_add HP' HL)

end
end TensorPCA.NonRSLowerProofs.SphericalGGObservedMarkedMoments
