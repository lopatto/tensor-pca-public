-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGBoundaryBands

/-! Separated prechosen intervals yield strictly ordered interior threshold
vectors, with one positive common lower-band width. The last threshold remains
strictly below one; no analytic terminal covariance node is changed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGMonotoneBoundaryCuts
open Set FiniteGGBoundaryBands

theorem exists_common_positive_width (depth : ℕ) (width : Fin depth → ℝ)
    (hWidth : ∀ l,0<width l) : ∃ h : ℝ,0<h ∧ ∀ l,h≤width l := by
  induction depth with
  | zero => exact ⟨1,by norm_num,fun l ↦ Fin.elim0 l⟩
  | succ depth ih =>
    obtain ⟨h,hh,hLe⟩ := ih (fun l ↦ width l.succ) (fun l ↦ hWidth l.succ)
    refine ⟨min (width 0) h,lt_min (hWidth 0) hh,?_⟩
    intro l
    exact Fin.cases (min_le_left _ _) (fun l ↦ (min_le_right _ _).trans (hLe l)) l

theorem threshold_vector_strictMono {depth J : ℕ} (a b : Fin depth → ℝ)
    (hab : ∀ l,a l<b l) (hSep : ∀ l j : Fin depth,l<j→b l≤a j)
    (index : Fin depth → Fin J) :
    StrictMono (fun l ↦ threshold (a l) (b l) J (index l)) := by
  intro l j hlj
  exact ((threshold_mem (hab l) J (index l)).2.trans_le (hSep l j hlj)).trans
    (threshold_mem (hab j) J (index j)).1

theorem threshold_vector_lt_one {depth J : ℕ} (a b : Fin depth → ℝ)
    (hab : ∀ l,a l<b l) (hb : ∀ l,b l≤1) (index : Fin depth → Fin J) (l : Fin depth) :
    threshold (a l) (b l) J (index l)<1 :=
  (threshold_mem (hab l) J (index l)).2.trans_le (hb l)

theorem lower_band_subset_closed_band {a b h : ℝ} (hab : a<b) (J : ℕ) (j : Fin J)
    (hWidth : h≤radius a b J) :
    Ico (threshold a b J j-h) (threshold a b J j)⊆band a b J j := by
  intro r hr
  have hRadius := radius_pos hab J
  exact ⟨by linarith only [hr.1,hWidth],by linarith only [hr.2,hRadius]⟩

theorem exists_common_boundary_width {depth : ℕ} (a b : Fin depth → ℝ)
    (hab : ∀ l,a l<b l) (J : ℕ) :
    ∃ h : ℝ,0<h ∧ ∀ l (j : Fin J),
      Ico (threshold (a l) (b l) J j-h) (threshold (a l) (b l) J j)⊆band (a l) (b l) J j := by
  obtain ⟨h,hh,hLe⟩ := exists_common_positive_width depth
    (fun l ↦ radius (a l) (b l) J) (fun l ↦ radius_pos (hab l) J)
  exact ⟨h,hh,fun l j ↦ lower_band_subset_closed_band (hab l) J j (hLe l)⟩

end TensorPCA.NonRSLowerProofs.FiniteGGMonotoneBoundaryCuts
