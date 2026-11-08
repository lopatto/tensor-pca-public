-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianLawAverage
public import TensorPCA.NonRSLowerProofs.FiniteMeasurableCellHeights

/-! The finite-cell Gaussian comparison retains the original cell masses. Measurable
gluing combines the height families on the selected cells into one global family,
and the error is the sum of restricted L1 errors.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCellAverage
open MeasureTheory ProbabilityTheory Set
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw
open FiniteNestedGaussianMarkedMoments FiniteNestedGaussianLawAverage
open FiniteNestedLawComparison FiniteMeasurableCellHeights
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem cell_product_error_le_l1 {I A : Type*} [Fintype I] [MeasurableSpace A]
    {depth n M : ℕ} (cell : I→Set A) (hCell : ∀i,MeasurableSet (cell i))
    (hDis : ∀i j,i≠j→Disjoint (cell i) (cell j)) (hCover : (⋃i,cell i)=univ)
    (x : I→A→Fin depth→ℝ) (hxs : ∀i,Measurable (x i))
    (hx : ∀i a j,0<x i a j) (hxm : ∀i a,StrictMono (x i a)) (hx1 : ∀i a j,x i a j≤1)
    (P : I→A→PMF (NestedPartition depth n))
    (hP : ∀i t,Measurable (fun a ↦ (P i a t).toReal))
    (y : Fin (depth+1)→ℝ) {Z : EuclideanSpace ℝ (Fin M)→ℝ} (hZ : Measurable Z)
    {cap : ℝ} (hcap : 0≤cap) (hBound : ∀z,0≤Z z ∧ Z z≤cap)
    (z0 : EuclideanSpace ℝ (Fin M)) (mu : Measure A) [IsFiniteMeasure mu] :
    |(∑i,∫a in cell i,∑t : NestedPartition depth n,(P i a t).toReal*treeProduct t y Z z0 ∂mu)-
      (∫a,∫g : EuclideanSpace ℝ (Fin M),weightedMoment depth n (gluedHeights cell x a) 0
        (fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z0+Real.sqrt (y 0) •g) ∂stdGaussian (EuclideanSpace ℝ (Fin M)) ∂mu)|≤
      cap^n*(∑i,∫a in cell i,l1Distance (P i a)
        (partitionPMF depth n (x i a) 0 (le_refl 0) (hx i a) (hxm i a) (hx1 i a)) ∂mu) := by
  classical
  let T := fun j : Fin depth ↦ Real.sqrt (y j.succ-y j.castSucc) •
    ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin M))
  let W := fun (a : A) (v : Fin depth→ℝ) ↦
    ∫g : EuclideanSpace ℝ (Fin M),weightedMoment depth n v 0 T Z (z0+Real.sqrt (y 0) •g)
      ∂stdGaussian (EuclideanSpace ℝ (Fin M))
  have hiW (i : I) : Integrable (fun a ↦ W a (x i a)) mu :=
    (root_weightedMoment_joint_integrable (x i) (hxs i) (hx i) (hxm i) (hx1 i)
      y hZ hcap hBound z0 mu).integral_prod_left
  have hGlue := glued_test_integrable_and_integral_eq cell x hCell hDis hCover
    measurable_id W mu (fun i ↦ (hiW i).integrableOn)
  have hEach (i : I) :
      |(∫a in cell i,∑t : NestedPartition depth n,(P i a t).toReal*treeProduct t y Z z0 ∂mu)-
        (∫a in cell i,W a (x i a) ∂mu)|≤
        cap^n*(∫a in cell i,l1Distance (P i a)
          (partitionPMF depth n (x i a) 0 (le_refl 0) (hx i a) (hxm i a) (hx1 i a)) ∂mu) := by
    have H := law_product_error_le_strict_l1 (P i) (hP i) (x i) (hxs i) (hx i) (hxm i) (hx1 i)
      y hZ hcap hBound z0 (mu.restrict (cell i))
    have HF := integral_prod (fun p : A×EuclideanSpace ℝ (Fin M) ↦
        weightedMoment depth n (x i p.1) 0 T Z (z0+Real.sqrt (y 0) •p.2))
      (root_weightedMoment_joint_integrable (x i) (hxs i) (hx i) (hxm i) (hx1 i)
        y hZ hcap hBound z0 (mu.restrict (cell i)))
    rw [HF] at H
    exact H
  change |(∑i,∫a in cell i,∑t : NestedPartition depth n,(P i a t).toReal*treeProduct t y Z z0 ∂mu)-
    (∫a,W a (gluedHeights cell x a) ∂mu)|≤_
  simp only [id_eq,Set.preimage_id] at hGlue
  rw [hGlue.2,← Finset.sum_sub_distrib]
  calc
    _≤∑i,|(∫a in cell i,∑t : NestedPartition depth n,(P i a t).toReal*treeProduct t y Z z0 ∂mu)-
        (∫a in cell i,W a (x i a) ∂mu)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑i,cap^n*(∫a in cell i,l1Distance (P i a)
        (partitionPMF depth n (x i a) 0 (le_refl 0) (hx i a) (hxm i a) (hx1 i a)) ∂mu) :=
      Finset.sum_le_sum (fun i _ ↦ hEach i)
    _=_ := (Finset.mul_sum _ _ _).symm

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianCellAverage
