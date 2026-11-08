-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGObservedMarkedMoments

/-! The physical theta mark uses a one-dimensional node field with sqrt(M) scaling. The
selected heights, computed from the same amplitude's pair law, remain inside its
unconditional marked moment. Theta and common-root normalizations are retained.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGCompensatorMarkedMoments
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteNestedStrictSurrogate
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianLawAverage
open FiniteNestedLawComparison SphericalGGTreeExtraction SphericalGGTreeHeights
open SphericalGGTreeCylinder
open SphericalGGSelectedOwnHeights SphericalGGPhysicalTreeCoupling SphericalGGWeightObservable
open SphericalGGObservedMarkedMoments FiniteGGPositiveGrid FiniteCavityGaussianCompatibility
open GaussianCompactFeatureComparison
open scoped BigOperators RealInnerProductSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_selected_compensator_strict_moment (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : ℝ→ℝ)
    (hMark : Continuous mark) (hBound : ∀z,mark z∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {I : Type u} [Fintype I] {N K depth : ℕ},0<N → 0<depth →
      ∀ (cuts : I→Fin depth→ℝ) (hCuts : ∀i,Monotone (cuts i)),
      (∀i l,cuts i l∈Ioo (cutLeft depth l) (cutRight depth l))→
      ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : 0≤v),
      ∀ (cell : I→Set (Fin K→ℝ)),(∀i,MeasurableSet (cell i))→
      (∀i j,i≠j→Disjoint (cell i) (cell j))→(⋃i,cell i)=univ→
      ∀ (tau : ℝ) (htau : 0<tau) (htau1 : tau≤1),∀ (neg : ℝ),0≤neg → neg+1/(depth : ℝ)≤delta →
      letI := parameterizedGibbsKernel_markov (K := K) nu hv
      let y := fun l : Fin (depth+1) ↦ beta^2*(grid depth l*deriv (Scalar.xiSlice k mu) (grid depth l)-Scalar.xiSlice k mu (grid depth l))
      let Z := fun z : Model.Vector 1 ↦ mark (Real.sqrt (M : ℝ)*z 0)
      let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
      let P := fun i amp ↦ treePMF (cuts i) (hCuts i) (law d ((parameterizedGibbsKernel nu v).sectR amp) (r+1))
      let x := fun i amp ↦ strictHeightApprox depth (fun l ↦ lowerHeight nu v (cuts i l) amp) tau
      let Q := fun i amp ↦ partitionPMF depth (r+1) (x i amp) 0 (le_refl 0)
        (strictHeightApprox_pos depth _ tau (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).1) htau htau1)
        (strictHeightApprox_strictMono depth _ tau
          ((own_lower_heights_properties nu hv (cuts i) (hCuts i) amp).2.1) htau htau1)
        (fun l ↦ (strictHeightApprox_lt_one depth _ tau
          (fun l ↦ (lowerHeight_mem_Icc nu hv (cuts i l) amp).2) htau htau1 l).le)
      |(∫q,(∫g : GroundState.Disorder N k,∏i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (q.2 i).val) g)
          ∂stdGaussian (GroundState.Disorder N k)) ∂jointLaw (K := K) nu v r)-
        (∫amp,∫g : Model.Vector 1,weightedMoment depth (r+1)
          (selectedOwnHeights nu v cell cuts tau amp) 0
          (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
          Z (Real.sqrt (y 0) •g) ∂stdGaussian (Model.Vector 1) ∂positiveCubeLaw K)|≤
        eps+(jointLaw (K := K) nu v r).real {q | ∃i,q.1.1∈cell i ∧ ¬thresholdGood (cuts i) q.2}+
          (jointLaw (K := K) nu v r).real {q | ∃i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg}+
          ∑i,∫amp in cell i,l1Distance (P i amp) (Q i amp) ∂positiveCubeLaw K := by
  obtain ⟨delta,hDelta,hPhysical⟩ := exists_selected_compensator_coupling r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro I hI N K depth hN hd cuts hCuts hCutsGrid nu hnu v hv cell hCell hDis hCover tau htau htau1 neg hNeg hMesh
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let y := fun l : Fin (depth+1) ↦ beta^2*(grid depth l*deriv (Scalar.xiSlice k mu) (grid depth l)-Scalar.xiSlice k mu (grid depth l))
  let Z := fun z : Model.Vector 1 ↦ mark (Real.sqrt (M : ℝ)*z 0)
  let P := fun i amp ↦ treePMF (cuts i) (hCuts i)
    (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      ((parameterizedGibbsKernel nu v).sectR amp) (r+1))
  let A : ℝ := ∑i,∫amp in cell i,∑t : NestedPartition depth (r+1),
    (P i amp t).toReal*treeProduct t y Z 0 ∂positiveCubeLaw K
  have HP := hPhysical hN hd cuts hCuts hCutsGrid nu v hv cell hCell hDis hCover neg hNeg hMesh
  have hInd (i : I) :
      (∫amp,(cell i).indicator (fun amp ↦ ∑t : NestedPartition depth (r+1),
          (P i amp t).toReal*treeProduct t y Z 0) amp ∂positiveCubeLaw K)=
        ∫amp in cell i,∑t : NestedPartition depth (r+1),
          (P i amp t).toReal*treeProduct t y Z 0 ∂positiveCubeLaw K := integral_indicator (hCell i)
  have HP' : |(∫q,(∫g : GroundState.Disorder N k,∏i : Fin (r+1),mark (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (q.2 i).val) g)
        ∂stdGaussian (GroundState.Disorder N k)) ∂jointLaw (K := K) nu v r)-A|≤
      eps+(jointLaw (K := K) nu v r).real {q | ∃i,q.1.1∈cell i ∧ ¬thresholdGood (cuts i) q.2}+
        (jointLaw (K := K) nu v r).real {q | ∃i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg} := by
    have HM : (∑i,∫amp,(cell i).indicator (fun amp ↦ ∑t : NestedPartition depth (r+1),
        (P i amp t).toReal*treeProduct t y Z 0) amp ∂positiveCubeLaw K)=A := by
      dsimp only [A]
      exact Finset.sum_congr rfl (fun i _ ↦ hInd i)
    rw [← HM]
    simpa only [P,y,Z,treeProduct,zero_add] using HP
  have hcoord : Measurable (fun z : Model.Vector 1 ↦ Real.sqrt (M : ℝ)*z 0) := by
    fun_prop
  have hZ : Measurable Z := hMark.measurable.comp hcoord
  have HL := actual_tree_product_error_le_l1 (n := r+1) (M := 1) nu hv cell hCell hDis hCover cuts hCuts
    htau htau1 y hZ (fun z ↦ hBound _)
  exact (abs_sub_le _ A _).trans (add_le_add HP' HL)

end
end TensorPCA.NonRSLowerProofs.SphericalGGCompensatorMarkedMoments
