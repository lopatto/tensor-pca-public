-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGMonotoneBoundaryCuts

/-! Fixed nonnegative analytic representatives q_r=r/depth, ending at ONE,
and strictly interior positive cut intervals. The root representative is zero;
the physical Gaussian head still retains its separate xi'(0) variance. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGPositiveGrid
open Set
noncomputable section

def grid (depth : ℕ) (r : Fin (depth+1)) : ℝ := (r.val : ℝ)/(depth : ℝ)
def cutLeft (depth : ℕ) (l : Fin depth) : ℝ := ((l.val : ℝ)+1/3)/(depth : ℝ)
def cutRight (depth : ℕ) (l : Fin depth) : ℝ := ((l.val : ℝ)+2/3)/(depth : ℝ)

theorem grid_zero (depth : ℕ) : grid depth 0=0 := by simp only [grid,Fin.val_zero,Nat.cast_zero,zero_div]

theorem grid_last {depth : ℕ} (hd : 0<depth) : grid depth (Fin.last depth)=1 := by
  have hd0 : (depth : ℝ)≠0 := by exact_mod_cast hd.ne'
  exact div_self hd0

theorem grid_monotone {depth : ℕ} (hd : 0<depth) : Monotone (grid depth) := by
  intro r s hrs
  exact div_le_div_of_nonneg_right (by exact_mod_cast hrs) (Nat.cast_nonneg depth)

theorem grid_mem_unit {depth : ℕ} (hd : 0<depth) (r : Fin (depth+1)) : grid depth r∈Icc (0 : ℝ) 1 := by
  have hm := grid_monotone hd
  exact ⟨by simpa only [grid_zero] using hm (Fin.zero_le r),
    by simpa only [grid_last hd] using hm (Fin.le_last r)⟩

theorem grid_succ {depth : ℕ} (l : Fin depth) :
    grid depth l.succ=grid depth l.castSucc+1/(depth : ℝ) := by
  simp only [grid,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one,add_div]

theorem cut_interval {depth : ℕ} (hd : 0<depth) (l : Fin depth) :
    0<cutLeft depth l ∧ cutLeft depth l<cutRight depth l ∧ cutRight depth l<1 := by
  have hD : 0<(depth : ℝ) := by exact_mod_cast hd
  have hl0 : 0≤(l.val : ℝ) := Nat.cast_nonneg _
  have hl1 : (l.val : ℝ)+1≤depth := by exact_mod_cast (Nat.succ_le_iff.mpr l.isLt)
  refine ⟨div_pos (by linarith only [hl0]) hD,?_,?_⟩
  · apply (div_lt_div_iff_of_pos_right hD).mpr
    norm_num
  · apply (div_lt_one hD).mpr
    linarith only [hl1]

theorem cut_intervals_separated {depth : ℕ} (hd : 0<depth) (i j : Fin depth) (hij : i<j) :
    cutRight depth i≤cutLeft depth j := by
  have hD : 0<(depth : ℝ) := by exact_mod_cast hd
  have hStep : (i.val : ℝ)+1≤j.val := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
  apply (div_le_div_iff_of_pos_right hD).mpr
  linarith only [hStep]

theorem cut_bracket {depth : ℕ} (hd : 0<depth) (cuts : Fin depth → ℝ)
    (hCuts : ∀ l,cuts l∈Ioo (cutLeft depth l) (cutRight depth l)) (l : Fin depth) :
    grid depth l.castSucc≤cuts l ∧ cuts l≤grid depth l.succ := by
  have hD : 0<(depth : ℝ) := by exact_mod_cast hd
  have hLo : grid depth l.castSucc≤cutLeft depth l := by
    apply (div_le_div_iff_of_pos_right hD).mpr
    dsimp only [grid,cutLeft,Fin.val_castSucc]
    linarith
  have hHi : cutRight depth l≤grid depth l.succ := by
    apply (div_le_div_iff_of_pos_right hD).mpr
    simp only [grid,cutRight,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    linarith
  exact ⟨hLo.trans (hCuts l).1.le,(hCuts l).2.le.trans hHi⟩

theorem rounding_of_bracketed_cuts {depth : ℕ} (hd : 0<depth)
    (cuts : Fin depth → ℝ) (hCuts : ∀ l,grid depth l.castSucc≤cuts l ∧ cuts l≤grid depth l.succ)
    (r : Fin (depth+1)) {R neg : ℝ} (hNeg : 0≤neg) (hLower : -neg≤R) (hUpper : R≤1)
    (hLevel : ∀ l : Fin depth,l.val<r.val ↔ cuts l≤R) :
    |R-grid depth r|≤neg+1/(depth : ℝ) := by
  have hMesh : 0<1/(depth : ℝ) := by positivity
  apply abs_le.mpr
  constructor
  · by_cases hr : r.val=0
    · have he : r=0 := Fin.ext hr
      rw [he,grid_zero]
      linarith only [hLower,hMesh]
    · let l : Fin depth := ⟨r.val-1,by have := r.isLt; omega⟩
      have hSucc : l.succ=r := by apply Fin.ext; dsimp only [l,Fin.val_succ]; omega
      have hlt : l.val<r.val := by dsimp only [l]; omega
      have hBound := (hCuts l).1.trans ((hLevel l).mp hlt)
      have hGrid := grid_succ l
      rw [hSucc] at hGrid
      linarith only [hBound,hGrid,hNeg]
  · by_cases hr : r.val=depth
    · have he : r=Fin.last depth := Fin.ext hr
      rw [he,grid_last hd]
      linarith only [hUpper,hNeg,hMesh]
    · let l : Fin depth := ⟨r.val,by have := r.isLt; omega⟩
      have hCast : l.castSucc=r := Fin.ext rfl
      have hNot : ¬cuts l≤R := fun h ↦ (Nat.lt_irrefl r.val) ((hLevel l).mpr h)
      have hBound := (lt_of_not_ge hNot).trans_le (hCuts l).2
      have hGrid := grid_succ l
      rw [hCast] at hGrid
      linarith only [hBound,hGrid,hNeg]

end
end TensorPCA.NonRSLowerProofs.FiniteGGPositiveGrid
