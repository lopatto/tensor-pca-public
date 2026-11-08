-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityTreeMarkApproximation
public import TensorPCA.NonRSLowerProofs.FiniteCavityTreeGaussianLaw

/-! Pointwise physical products approximate the independent-node tree moments, with the
tolerance chosen before every tree depth and matrix. The selected-array expectation
is integrated separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityTreeMomentApproximation
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionUnitGram
open FiniteUnitGramRealization FiniteCavityTreeMarkApproximation FiniteCavityTreeGaussianLaw
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteNestedGaussianVectorLaw
open scoped BigOperators RealInnerProductSpace
noncomputable section

theorem exists_physical_numerator_tree_moment_modulus (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : Model.Vector M → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {N depth : ℕ} (q : Fin (depth+1) → ℝ),
      0≤q 0 → Monotone q → q (Fin.last depth)=1 →
      ∀ (t : NestedPartition depth (r+1)) (s : Fin (r+1) → UnitSpin N),
      (∀ i j,|inner ℝ (s i).val (s j).val-overlap t q i j|≤delta)→
        |(∫ g : CavityDisorder N M k,∏ i : Fin (r+1),mark (blockField k mu beta g (s i).val)
          ∂stdGaussian (CavityDisorder N M k))-
         (∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M),
          ∏ i : Fin (r+1),mark (vectorReplicaField t
            (fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)) M g i)
          ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M)))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_uniform_tree_numerator_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N depth q hq0 hqm hq1 t s hClose
  have H := hMain q hq0 hqm hq1 t s hClose
  rw [blockField_tree_mark_product k hmu beta q hq0 hqm t (realization (overlap t q))
    (overlap_realization_inner t hq0 hqm) mark hMark] at H
  exact H

theorem exists_physical_compensator_tree_moment_modulus (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : ℝ → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {N depth : ℕ},0<N →
      ∀ (q : Fin (depth+1) → ℝ),0≤q 0 → Monotone q → q (Fin.last depth)=1 →
      ∀ (t : NestedPartition depth (r+1)) (s : Fin (r+1) → UnitSpin N),
      (∀ i j,|inner ℝ (s i).val (s j).val-overlap t q i j|≤delta)→
        |(∫ g : GroundState.Disorder N k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (s i).val) g)
          ∂stdGaussian (GroundState.Disorder N k))-
         (∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1),
          ∏ i : Fin (r+1),mark (Real.sqrt (M : ℝ)*(vectorReplicaField t
            (fun l ↦ beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))) 1 g i) 0)
          ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1)))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_uniform_tree_compensator_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N depth hN q hq0 hqm hq1 t s hClose
  have H := hMain hN q hq0 hqm hq1 t s hClose
  rw [compensator_tree_mark_product (Nat.succ_pos r) M k hmu beta q hq0 hqm t (realization (overlap t q))
    (overlap_realization_inner t hq0 hqm) mark hMark] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityTreeMomentApproximation
