-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianFeature
public import TensorPCA.NonRSLowerProofs.FiniteUnitGramRealization

/-! The literal finite tree overlap matrix is a standard unit Gram matrix, witnessed by
its already-proved Gaussian node feature.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionUnitGram
open Matrix Set
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedGaussianFeature
open FiniteUnitGramRealization
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem overlap_posSemidef {depth n : ℕ} (t : NestedPartition depth n)
    {q : Fin (depth+1)→ℝ} (hq0 : 0≤q 0) (hqm : Monotone q) :
    Matrix.PosSemidef (overlap t q) := by
  classical
  let R : Matrix (Fin n) (Coordinate t) ℝ := fun i c => feature t q i c
  have H : overlap t q=R*Rᴴ := by
    ext i j
    rw [← feature_gram t hq0 hqm i j]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Matrix.mul_apply,
      Matrix.conjTranspose,Matrix.map_apply,Matrix.transpose_apply,star_trivial,R]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [H]
  exact Matrix.posSemidef_self_mul_conjTranspose R

theorem overlap_mem_unitGramSet {depth n : ℕ} (t : NestedPartition depth n)
    {q : Fin (depth+1)→ℝ} (hq0 : 0≤q 0) (hqm : Monotone q) (hq1 : q (Fin.last depth)=1) :
    overlap t q∈unitGramSet n := by
  refine ⟨overlap_posSemidef t hq0 hqm,?_⟩
  intro i
  rw [overlap_self,hq1]

theorem overlap_realization_inner {depth n : ℕ} (t : NestedPartition depth n)
    {q : Fin (depth+1)→ℝ} (hq0 : 0≤q 0) (hqm : Monotone q) (i j : Fin n) :
    inner ℝ (realization (overlap t q) i) (realization (overlap t q) j)=overlap t q i j :=
  realization_inner _ (overlap_posSemidef t hq0 hqm) i j

theorem overlap_realization_norm {depth n : ℕ} (t : NestedPartition depth n)
    {q : Fin (depth+1)→ℝ} (hq0 : 0≤q 0) (hqm : Monotone q) (hq1 : q (Fin.last depth)=1) (i : Fin n) :
    ‖realization (overlap t q) i‖=1 :=
  realization_norm _ (overlap_posSemidef t hq0 hqm) (fun i => (overlap_self t q i).trans hq1) i

end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionUnitGram
