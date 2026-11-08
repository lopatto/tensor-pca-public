-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! One positive negative-overlap tolerance and one finite grid work for
every prechosen numerator and compensation modulus in a finite family. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGFiniteMomentMesh
noncomputable section

theorem exists_common_grid_mesh (R : ℕ) (hR : 0<R) (deltaN deltaC : Fin R→ℝ)
    (hN : ∀r,0<deltaN r) (hC : ∀r,0<deltaC r) :
    ∃depth : ℕ,0<depth ∧ ∃negTol : ℝ,0<negTol ∧ negTol<1 ∧
      ∀r,negTol+1/(depth : ℝ)≤deltaN r ∧ negTol+1/(depth : ℝ)≤deltaC r := by
  classical
  have hNonempty : (Finset.univ : Finset (Fin R)).Nonempty :=
    ⟨⟨0,hR⟩,Finset.mem_univ _⟩
  let delta := Finset.univ.inf' hNonempty (fun r => min (deltaN r) (deltaC r))
  have hDelta : 0<delta := by
    exact (Finset.lt_inf'_iff hNonempty).2 (fun r _ => lt_min (hN r) (hC r))
  let negTol := min (1/2 : ℝ) (delta/2)
  have hTol : 0<negTol := lt_min (by norm_num) (by positivity)
  have hTol1 : negTol<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0<delta/2 by positivity)
  have hMesh : negTol+1/((n+1 : ℕ) : ℝ)≤delta := by
    have hHalf : negTol≤delta/2 := min_le_right _ _
    simp only [Nat.cast_add,Nat.cast_one] at *
    linarith
  refine ⟨n+1,Nat.zero_lt_succ _,negTol,hTol,hTol1,?_⟩
  intro r
  have hMin : delta≤min (deltaN r) (deltaC r) := Finset.inf'_le _ (Finset.mem_univ r)
  exact ⟨hMesh.trans (hMin.trans (min_le_left _ _)),hMesh.trans (hMin.trans (min_le_right _ _))⟩

end
end TensorPCA.NonRSLowerProofs.SphericalGGFiniteMomentMesh
