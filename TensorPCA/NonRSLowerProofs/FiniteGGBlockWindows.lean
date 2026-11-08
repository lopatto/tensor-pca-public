-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGCloningGeometry
public import Mathlib.Data.Fin.Tuple.Basic

/-! Literal two-block overlap windows for finite cloning. Cross windows
stay fixed; only the distinct within-block upper cap increases. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGBlockWindows
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def blockWindows {r s : ℕ} (x : E) (Y : Fin r → E) (Z : Fin s → E)
    (a b c eps cap : ℝ) : Prop :=
  (∀ i,|inner ℝ x (Y i)-a|≤eps) ∧
  (∀ j,|inner ℝ x (Z j)-b|≤eps) ∧
  (∀ i j,|inner ℝ (Y i) (Z j)-c|≤eps) ∧
  (∀ i j,i≠j→inner ℝ (Y i) (Y j)≤cap) ∧
  (∀ i j,i≠j→inner ℝ (Z i) (Z j)≤cap)

private theorem pairwise_snoc_bound {s : ℕ} (W : Fin s → E) (w : E) (cap : ℝ)
    (hW : ∀ i j,i≠j→inner ℝ (W i) (W j)≤cap)
    (hNew : ∀ i,inner ℝ (W i) w≤cap) :
    ∀ i j : Fin (s+1),i≠j→inner ℝ
      ((Fin.snoc W w : Fin (s+1) → E) i) ((Fin.snoc W w : Fin (s+1) → E) j)≤cap := by
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · intro h; exact False.elim (h rfl)
    · intro _
      simpa only [Fin.snoc_last,Fin.snoc_castSucc,real_inner_comm w (W l)] using hNew l
  · intro j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · intro _
      simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hNew k
    · intro h
      have hkl : k≠l := fun he ↦ h (congrArg Fin.castSucc he)
      simpa only [Fin.snoc_castSucc] using hW k l hkl

theorem blockWindows_extend_two_candidates {r s : ℕ} (x : E) (Y : Fin r → E)
    (Z : Fin s → E) (z0 z1 : E) (a b c eps cap nextCap : ℝ)
    (h0 : blockWindows x Y (Fin.snoc Z z0) a b c eps cap)
    (h1 : blockWindows x Y (Fin.snoc Z z1) a b c eps cap)
    (hCap : cap≤nextCap) (hPair : inner ℝ z0 z1≤nextCap) :
    blockWindows x Y (Fin.snoc (Fin.snoc Z z0) z1) a b c eps nextCap := by
  refine ⟨h0.1,?_,?_,?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · simpa only [Fin.snoc_last] using h1.2.1 (Fin.last s)
    · simpa only [Fin.snoc_castSucc] using h0.2.1 l
  · intro i j
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · simpa only [Fin.snoc_last] using h1.2.2.1 i (Fin.last s)
    · simpa only [Fin.snoc_castSucc] using h0.2.2.1 i l
  · intro i j hij
    exact (h0.2.2.2.1 i j hij).trans hCap
  · apply pairwise_snoc_bound
    · intro i j hij
      exact (h0.2.2.2.2 i j hij).trans hCap
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.snoc_last] using hPair
      · have H := h1.2.2.2.2 j.castSucc (Fin.last s) (Fin.castSucc_ne_last j)
        simpa only [Fin.snoc_castSucc,Fin.snoc_last] using H.trans hCap

theorem blockWindows_all_distinct_le {r s : ℕ} {x : E} {Y : Fin r → E} {Z : Fin s → E}
    {a b c eps cap : ℝ} (h : blockWindows x Y Z a b c eps cap)
    (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap) :
    (∀ i,inner ℝ x (Y i)≤cap) ∧ (∀ j,inner ℝ x (Z j)≤cap) ∧
      (∀ i j,inner ℝ (Y i) (Z j)≤cap) ∧
      (∀ i j,i≠j→inner ℝ (Y i) (Y j)≤cap) ∧
      (∀ i j,i≠j→inner ℝ (Z i) (Z j)≤cap) := by
  refine ⟨?_,?_,?_,h.2.2.2.1,h.2.2.2.2⟩
  · intro i; linarith only [(abs_le.mp (h.1 i)).2,ha]
  · intro j; linarith only [(abs_le.mp (h.2.1 j)).2,hb]
  · intro i j; linarith only [(abs_le.mp (h.2.2.1 i j)).2,hc]

theorem blockWindows_swap {r s : ℕ} {x : E} {Y : Fin r → E} {Z : Fin s → E}
    {a b c eps cap : ℝ} (h : blockWindows x Y Z a b c eps cap) :
    blockWindows x Z Y b a c eps cap := by
  refine ⟨h.2.1,h.1,?_,h.2.2.2.2,h.2.2.2.1⟩
  intro i j
  simpa only [real_inner_comm (Z i) (Y j)] using h.2.2.1 j i

theorem blockWindows_impossible_of_gap {m : ℕ} (hm : 0<m) {a b c eps g : ℝ}
    (heps : 0≤eps) (hc : -1≤c) (hGap : g≤|a-b|)
    (hBudget : 2*eps+Real.sqrt (4/(m : ℝ)+4*eps)<g)
    (x : E) (Y Z : Fin m → E) (hx : ‖x‖=1)
    (hY : ∀ i,‖Y i‖=1) (hZ : ∀ i,‖Z i‖=1) :
    ¬blockWindows x Y Z a b c eps (c+eps) := by
  intro h
  have H := FiniteGGBarycenterGeometry.separated_overlap_bound hm heps hc x Y Z hx hY hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  linarith only [H,hGap,hBudget]

theorem exists_increasing_cloning_caps {c eps : ℝ}
    (hc : -1≤c) (heps : 0<eps) (hTop : c+eps<1) (L : ℕ) :
    ∃ h : ℝ,0<h ∧
      let cap := fun j : ℕ ↦ c+eps/2+(j : ℝ)*h
      (∀ j,j≤L→-1<cap j ∧ cap j<c+eps) ∧
      ∀ j,j<L→cap j<cap j+h/3 ∧ cap j+h/3<cap j+2*h/3 ∧
        cap j+2*h/3<cap (j+1) ∧ cap (j+1)<1 := by
  let h : ℝ := eps/(2*((L : ℝ)+1))
  have hh : 0<h := div_pos heps (by positivity)
  have hEq : h*(2*((L : ℝ)+1))=eps := div_mul_cancel₀ eps (by positivity)
  have hTail : (L : ℝ)*h<eps/2 := by nlinarith only [hEq,hh]
  have hCap (j : ℕ) (hj : j≤L) : -1<c+eps/2+(j : ℝ)*h ∧ c+eps/2+(j : ℝ)*h<c+eps := by
    have hjR : (j : ℝ)≤L := by exact_mod_cast hj
    have hUpper := mul_le_mul_of_nonneg_right hjR hh.le
    have hLower : 0≤(j : ℝ)*h := mul_nonneg (Nat.cast_nonneg j) hh.le
    constructor
    · linarith only [hc,heps,hLower]
    · linarith only [hUpper,hTail]
  refine ⟨h,hh,hCap,?_⟩
  intro j hj
  have hNext := (hCap (j+1) (Nat.succ_le_iff.mpr hj)).2.trans hTop
  simp only [Nat.cast_add,Nat.cast_one] at hNext ⊢
  refine ⟨?_,?_,?_,hNext⟩ <;> nlinarith only [hh]

end
end TensorPCA.NonRSLowerProofs.FiniteGGBlockWindows
