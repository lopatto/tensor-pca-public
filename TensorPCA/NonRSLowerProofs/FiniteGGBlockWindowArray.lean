-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGBlockWindows
public import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Standard finite-array projections for the literal block windows.
The order is one fixed spin, the Y block, then the Z block. All cloning
transport is deterministic; the physical two-copy law is supplied elsewhere. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGBlockWindowArray
open FiniteGGBlockWindows
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def arrayBlockWindows (r s : ℕ) (A : Fin (r+s+1) → E) (a b c eps cap : ℝ) : Prop :=
  blockWindows (A 0) (fun i : Fin r ↦ A (Fin.castAdd s i).succ)
    (fun j : Fin s ↦ A (Fin.natAdd r j).succ) a b c eps cap

theorem cons_addCases_reconstruct (r s : ℕ) (A : Fin (r+s+1) → E) :
    Fin.cons (A 0) (Fin.addCases (fun i : Fin r ↦ A (Fin.castAdd s i).succ)
      (fun j : Fin s ↦ A (Fin.natAdd r j).succ))=A := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact Fin.cons_zero _ _
  · rw [Fin.cons_succ]
    exact Fin.addCases_castAdd_natAdd (fun j ↦ A j.succ) j

theorem arrayBlockWindows_cons {r s : ℕ} (x : E) (Y : Fin r → E) (Z : Fin s → E)
    (a b c eps cap : ℝ) :
    arrayBlockWindows r s (Fin.cons x (Fin.addCases Y Z)) a b c eps cap↔
      blockWindows x Y Z a b c eps cap := by
  simp only [arrayBlockWindows,Fin.cons_zero,Fin.cons_succ,Fin.addCases_left,Fin.addCases_right]

theorem cons_addCases_snoc {r s : ℕ} (x : E) (Y : Fin r → E) (Z : Fin s → E) (z : E) :
    (Fin.cons x (Fin.addCases (m := r) (n := s+1) (motive := fun _ ↦ E)
      Y (Fin.snoc Z z : Fin (s+1) → E)) : Fin (r+s+2) → E)=
      (Fin.snoc (Fin.cons x (Fin.addCases Y Z)) z : Fin (r+s+2) → E) := by
  change (Fin.cons x (Fin.append (m := r) (n := s+1) Y (Fin.snoc Z z : Fin (s+1) → E)) : Fin (r+s+2) → E)=
    (Fin.snoc (Fin.cons x (Fin.append Y Z)) z : Fin (r+s+2) → E)
  rw [Fin.append_snoc,Fin.cons_snoc_eq_snoc_cons]

theorem blockWindows_weaken {r s : ℕ} {x : E} {Y : Fin r → E} {Z : Fin s → E}
    {a b c eps eps' cap cap' : ℝ} (h : blockWindows x Y Z a b c eps cap)
    (hEps : eps≤eps') (hCap : cap≤cap') : blockWindows x Y Z a b c eps' cap' := by
  exact ⟨fun i ↦ (h.1 i).trans hEps,fun j ↦ (h.2.1 j).trans hEps,
    fun i j ↦ (h.2.2.1 i j).trans hEps,
    fun i j hij ↦ (h.2.2.2.1 i j hij).trans hCap,
    fun i j hij ↦ (h.2.2.2.2 i j hij).trans hCap⟩

theorem arrayBlockWindows_weaken {r s : ℕ} {A : Fin (r+s+1) → E}
    {a b c eps eps' cap cap' : ℝ} (h : arrayBlockWindows r s A a b c eps cap)
    (hEps : eps≤eps') (hCap : cap≤cap') : arrayBlockWindows r s A a b c eps' cap' :=
  blockWindows_weaken h hEps hCap

theorem arrayBlockWindows_extend_two_candidates {r s : ℕ} (A : Fin (r+s+3) → E)
    (a b c eps cap nextCap : ℝ)
    (h0 : arrayBlockWindows r (s+1) (Fin.init A) a b c eps cap)
    (h1 : arrayBlockWindows r (s+1)
      (Fin.snoc (Fin.init (Fin.init A)) (A (Fin.last (r+s+2)))) a b c eps cap)
    (hCap : cap≤nextCap)
    (hPair : inner ℝ (A (Fin.last (r+s+1)).castSucc) (A (Fin.last (r+s+2)))≤nextCap) :
    arrayBlockWindows r (s+2) A a b c eps nextCap := by
  let W : Fin (r+s+1) → E := Fin.init (Fin.init A)
  let x := W 0
  let Y : Fin r → E := fun i ↦ W (Fin.castAdd s i).succ
  let Z : Fin s → E := fun j ↦ W (Fin.natAdd r j).succ
  let z0 := A (Fin.last (r+s+1)).castSucc
  let z1 := A (Fin.last (r+s+2))
  have hW : Fin.cons x (Fin.addCases Y Z)=W := cons_addCases_reconstruct r s W
  have hOld : (Fin.snoc W z0 : Fin (r+s+2) → E)=Fin.init A := Fin.snoc_init_self (Fin.init A)
  have hNew : (Fin.snoc (Fin.init A) z1 : Fin (r+s+3) → E)=A := Fin.snoc_init_self A
  have h0eq : (Fin.cons x (Fin.addCases (m := r) (n := s+1) (motive := fun _ ↦ E)
      Y (Fin.snoc Z z0 : Fin (s+1) → E)) : Fin (r+s+2) → E)=Fin.init A := by
    rw [cons_addCases_snoc,hW,hOld]
  have h1eq : (Fin.cons x (Fin.addCases (m := r) (n := s+1) (motive := fun _ ↦ E)
      Y (Fin.snoc Z z1 : Fin (s+1) → E)) : Fin (r+s+2) → E)=
      (Fin.snoc (Fin.init (Fin.init A)) (A (Fin.last (r+s+2))) : Fin (r+s+2) → E) := by
    rw [cons_addCases_snoc,hW]
  have hFull : (Fin.cons x (Fin.addCases (m := r) (n := s+2) (motive := fun _ ↦ E)
      Y (Fin.snoc (Fin.snoc Z z0 : Fin (s+1) → E) z1 : Fin (s+2) → E)) : Fin (r+s+3) → E)=A := by
    rw [cons_addCases_snoc,h0eq,hNew]
  rw [← h0eq,arrayBlockWindows_cons] at h0
  rw [← h1eq,arrayBlockWindows_cons] at h1
  rw [← hFull,arrayBlockWindows_cons]
  exact blockWindows_extend_two_candidates x Y Z z0 z1 a b c eps cap nextCap h0 h1 hCap hPair

theorem arrayBlockWindows_offdiag_le {r s : ℕ} {A : Fin (r+s+1) → E}
    {a b c eps cap : ℝ} (h : arrayBlockWindows r s A a b c eps cap)
    (ha : a+eps≤cap) (hb : b+eps≤cap) (hc : c+eps≤cap) :
    ∀ i j,i≠j→inner ℝ (A i) (A j)≤cap := by
  have H := blockWindows_all_distinct_le h ha hb hc
  intro i
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · intro j
    refine Fin.cases ?_ (fun l ↦ ?_) j
    · intro hij; exact False.elim (hij rfl)
    · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
      · intro _; exact H.1 l
      · intro _; exact H.2.1 l
  · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k
    · intro j
      refine Fin.cases ?_ (fun l ↦ ?_) j
      · intro _
        simpa only [real_inner_comm (A (Fin.castAdd s k).succ) (A 0)] using H.1 k
      · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
        · intro hij
          exact H.2.2.2.1 k l (fun hkl ↦ hij (congrArg (fun i : Fin r ↦ (Fin.castAdd s i).succ) hkl))
        · intro _; exact H.2.2.1 k l
    · intro j
      refine Fin.cases ?_ (fun l ↦ ?_) j
      · intro _
        simpa only [real_inner_comm (A (Fin.natAdd r k).succ) (A 0)] using H.2.1 k
      · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l
        · intro _
          simpa only [real_inner_comm (A (Fin.natAdd r k).succ) (A (Fin.castAdd s l).succ)] using H.2.2.1 l k
        · intro hij
          exact H.2.2.2.2 k l (fun hkl ↦ hij (congrArg (fun i : Fin s ↦ (Fin.natAdd r i).succ) hkl))

theorem arrayBlockWindows_isClosed (r s : ℕ) (a b c eps cap : ℝ) :
    IsClosed {A : Fin (r+s+1) → E | arrayBlockWindows r s A a b c eps cap} := by
  have hWindow (i j : Fin (r+s+1)) (v : ℝ) :
      IsClosed {A : Fin (r+s+1) → E | |inner ℝ (A i) (A j)-v|≤eps} :=
    isClosed_le (((continuous_apply i).inner (continuous_apply j)).sub continuous_const).abs continuous_const
  have hUpper (i j : Fin (r+s+1)) :
      IsClosed {A : Fin (r+s+1) → E | inner ℝ (A i) (A j)≤cap} :=
    isClosed_le ((continuous_apply i).inner (continuous_apply j)) continuous_const
  have hXY : IsClosed {A : Fin (r+s+1) → E | ∀ i : Fin r,|inner ℝ (A 0) (A (Fin.castAdd s i).succ)-a|≤eps} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i ↦ hWindow 0 (Fin.castAdd s i).succ a)
  have hXZ : IsClosed {A : Fin (r+s+1) → E | ∀ j : Fin s,|inner ℝ (A 0) (A (Fin.natAdd r j).succ)-b|≤eps} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun j ↦ hWindow 0 (Fin.natAdd r j).succ b)
  have hYZ : IsClosed {A : Fin (r+s+1) → E | ∀ i : Fin r,∀ j : Fin s,
      |inner ℝ (A (Fin.castAdd s i).succ) (A (Fin.natAdd r j).succ)-c|≤eps} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ hWindow (Fin.castAdd s i).succ (Fin.natAdd r j).succ c))
  have hYY : IsClosed {A : Fin (r+s+1) → E | ∀ i j : Fin r,i≠j→
      inner ℝ (A (Fin.castAdd s i).succ) (A (Fin.castAdd s j).succ)≤cap} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ isClosed_iInter
      (fun _ : i≠j ↦ hUpper (Fin.castAdd s i).succ (Fin.castAdd s j).succ)))
  have hZZ : IsClosed {A : Fin (r+s+1) → E | ∀ i j : Fin s,i≠j→
      inner ℝ (A (Fin.natAdd r i).succ) (A (Fin.natAdd r j).succ)≤cap} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ isClosed_iInter
      (fun _ : i≠j ↦ hUpper (Fin.natAdd r i).succ (Fin.natAdd r j).succ)))
  simpa only [arrayBlockWindows,blockWindows,Set.setOf_and] using hXY.inter (hXZ.inter (hYZ.inter (hYY.inter hZZ)))

end
end TensorPCA.NonRSLowerProofs.FiniteGGBlockWindowArray
