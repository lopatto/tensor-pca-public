-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGPositiveGrid
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder

/-! Literal Tree cylinders round overlap entries to the fixed grid. The only exceptional
data needed here is a lower overlap bound; its probability is discharged separately
by the existing positivity theorem.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGCylinderGramRounding
open Set
open NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteGGPositiveGrid
open SphericalGGTreeCylinder SphericalFirstJetPowerBudget
noncomputable section

theorem cylinder_grid_overlap_error {N depth n : ℕ} (hd : 0<depth)
    (cuts : Fin depth → ℝ) (hCuts : ∀ l,cuts l∈Ioo (cutLeft depth l) (cutRight depth l))
    (t : NestedPartition depth n) (old : Fin n → UnitSpin N) (hCylinder : treeCylinder cuts t old)
    {neg : ℝ} (hNeg : 0≤neg) (hLower : ∀ i j,-neg≤unitOverlap (old i) (old j))
    (i j : Fin n) :
    |unitOverlap (old i) (old j)-overlap t (grid depth) i j|≤neg+1/(depth : ℝ) := by
  exact rounding_of_bracketed_cuts hd cuts (cut_bracket hd cuts hCuts) (level t i j)
    hNeg (hLower i j) (unitOverlap_mem_Icc (old i) (old j)).2 (fun l ↦ hCylinder l i j)

theorem cylinder_rounding_failure_subset_negative {N depth n : ℕ} (hd : 0<depth)
    (cuts : Fin depth → ℝ) (hCuts : ∀ l,cuts l∈Ioo (cutLeft depth l) (cutRight depth l))
    (t : NestedPartition depth n) {neg : ℝ} (hNeg : 0≤neg) :
    {old : Fin n → UnitSpin N | treeCylinder cuts t old ∧
      ∃ i j,neg+1/(depth : ℝ) < |unitOverlap (old i) (old j)-overlap t (grid depth) i j|}⊆
      {old | ∃ i j,unitOverlap (old i) (old j)< -neg} := by
  rintro old ⟨hCylinder,i,j,hError⟩
  by_contra hNo
  have hLower (a b : Fin n) : -neg≤unitOverlap (old a) (old b) := by
    by_contra h
    exact hNo ⟨a,b,lt_of_not_ge h⟩
  exact (not_lt_of_ge (cylinder_grid_overlap_error hd cuts hCuts t old hCylinder hNeg hLower i j)) hError

end
end TensorPCA.NonRSLowerProofs.SphericalGGCylinderGramRounding
