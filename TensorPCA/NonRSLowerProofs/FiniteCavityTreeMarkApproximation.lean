-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalMarkModulus
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionUnitGram

/-! The physical mark modulus applies uniformly to every finite tree depth. The tree's
unit Gram matrix is realized canonically, with its terminal node exactly one. Exact
independent node-noise evaluation is a separate step.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityTreeMarkApproximation
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionUnitGram
open FiniteUnitGramRealization FiniteCavityPhysicalMarkModulus
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility
open scoped BigOperators RealInnerProductSpace
noncomputable section

theorem exists_uniform_tree_numerator_modulus (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : Model.Vector M → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {N depth : ℕ} (q : Fin (depth+1) → ℝ),
      0≤q 0 → Monotone q → q (Fin.last depth)=1 →
      ∀ (t : NestedPartition depth (r+1)) (s : Fin (r+1) → UnitSpin N),
      (∀ i j,|inner ℝ (s i).val (s j).val-overlap t q i j|≤delta)→
        |(∫ g : CavityDisorder N M k,∏ i : Fin (r+1),mark (blockField k mu beta g (s i).val)
          ∂stdGaussian (CavityDisorder N M k))-
         (∫ g : CavityDisorder (r+1) M k,∏ i : Fin (r+1),mark
          (blockField k mu beta g (realization (overlap t q) i))
          ∂stdGaussian (CavityDisorder (r+1) M k))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_uniform_physical_numerator_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N depth q hq0 hqm hq1 t s hClose
  let u : Fin (r+1) → UnitSpin (r+1) := fun i ↦
    ⟨realization (overlap t q) i,overlap_realization_norm t hq0 hqm hq1 i⟩
  have hClose' (i j : Fin (r+1)) :
      |inner ℝ (s i).val (s j).val-inner ℝ (u i).val (u j).val|≤delta := by
    change |inner ℝ (s i).val (s j).val-
      inner ℝ (realization (overlap t q) i) (realization (overlap t q) j)|≤delta
    rw [overlap_realization_inner t hq0 hqm]
    exact hClose i j
  exact hMain s u hClose'

theorem exists_uniform_tree_compensator_modulus (r M k : ℕ) {mu : ℝ}
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
         (∫ g : GroundState.Disorder (r+1) k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (realization (overlap t q) i)) g)
          ∂stdGaussian (GroundState.Disorder (r+1) k))|<eps := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_uniform_physical_compensator_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro N depth hN q hq0 hqm hq1 t s hClose
  let u : Fin (r+1) → UnitSpin (r+1) := fun i ↦
    ⟨realization (overlap t q) i,overlap_realization_norm t hq0 hqm hq1 i⟩
  have hClose' (i j : Fin (r+1)) :
      |inner ℝ (s i).val (s j).val-inner ℝ (u i).val (u j).val|≤delta := by
    change |inner ℝ (s i).val (s j).val-
      inner ℝ (realization (overlap t q) i) (realization (overlap t q) j)|≤delta
    rw [overlap_realization_inner t hq0 hqm]
    exact hClose i j
  exact hMain hN (Nat.succ_pos r) s u hClose'

end
end TensorPCA.NonRSLowerProofs.FiniteCavityTreeMarkApproximation
