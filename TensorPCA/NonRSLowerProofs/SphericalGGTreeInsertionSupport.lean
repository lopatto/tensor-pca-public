-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionOld
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeExtraction

/-! Exact fresh-zero cylinder support, retaining all old labels and the
literal sphere overlap. No probabilistic insertion law is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionSupport
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteNestedPartitionInsertionBlocks FiniteNestedPartitionInsertionOld
open FiniteOrderedPartitionSetoid SphericalGGTreeCylinder
open NonRSUpperProofs.SphericalPositivePerturbation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem treeCylinder_extend_cons_iff {N depth n : ℕ} (cuts : Fin depth→ℝ)
    (hcuts1 : ∀l,cuts l≤1) (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) :
    treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) (Fin.cons fresh old) ↔
      treeCylinder cuts t old ∧ ∀l : Fin depth,∀i : Fin n,
        ((l : ℕ)<coalescence ((extendEquiv depth n) ⟨t,o⟩) 0 i.succ ↔
          cuts l≤unitOverlap fresh (old i)) := by
  constructor
  · intro h
    constructor
    · intro l i j
      simpa only [Fin.cons_succ,coalescence_extend_old] using h l i.succ j.succ
    · intro l i
      simpa only [Fin.cons_zero,Fin.cons_succ] using h l 0 i.succ
  · rintro ⟨hOld,hFresh⟩ l i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        have hSelf : unitOverlap fresh fresh=1 := by
          rw [unitOverlap,real_inner_self_eq_norm_sq,fresh.property,one_pow]
        simpa only [Fin.cons_zero,coalescence_self,hSelf] using
          (iff_of_true l.isLt (hcuts1 l))
      | succ j => simpa only [Fin.cons_zero,Fin.cons_succ] using hFresh l j
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simpa only [Fin.cons_zero,Fin.cons_succ,coalescence_symm,unitOverlap,real_inner_comm] using hFresh l i
      | succ j => simpa only [Fin.cons_succ,coalescence_extend_old] using hOld l i j

theorem treeCylinder_extend_none_cons_iff {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (hcuts1 : ∀l,cuts l≤1) (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) :
    treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) (Fin.cons fresh old) ↔
      treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old ∧
        ∀l : Fin (depth+1),∀i : Fin n,unitOverlap fresh (old i)<cuts l := by
  rw [treeCylinder_extend_cons_iff cuts hcuts1]
  simp only [coalescence_extend_none_fresh c f,Nat.not_lt_zero,false_iff,not_le]

theorem treeCylinder_extend_none_cons_iff_firstCut {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N) :
    treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) (Fin.cons fresh old) ↔
      treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old ∧
        ∀i : Fin n,unitOverlap fresh (old i)<cuts 0 := by
  rw [treeCylinder_extend_none_cons_iff cuts hcuts1]
  constructor
  · rintro ⟨hc,h⟩
    exact ⟨hc,h 0⟩
  · rintro ⟨hc,h⟩
    exact ⟨hc,fun l i ↦ (h i).trans_le (hcuts (Fin.zero_le l))⟩

theorem ballSize_zero_emb {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (b : Fin c.length) (a : Fin (c.partSize b)) :
    ballSize (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) 0 (c.emb b a)=c.partSize b := by
  classical
  have H : (∑j : Fin n,if 0<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) j then (1 : ℕ) else 0)=
      ballSize (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) 0 (c.emb b a) :=
    Finset.sum_boole _ _
  rw [← H]
  rw [← Fintype.sum_equiv c.equivSigma
    (fun s ↦ if 0<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) (c.emb s.1 s.2) then (1 : ℕ) else 0)
    (fun j ↦ if 0<coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b a) j then (1 : ℕ) else 0)
    (fun _ ↦ rfl),Fintype.sum_sigma]
  simp only [← sameBlock_iff_coalescence_pos,sameBlock,index_emb]
  simp

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionSupport
