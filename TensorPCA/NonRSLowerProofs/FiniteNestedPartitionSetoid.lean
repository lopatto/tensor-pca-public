-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteOrderedPartitionSetoid
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionOverlap

/-! Literal nested ordered partitions represent nested finite equivalence
relations, using exactly the existing coalescence levels. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionSetoid
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteOrderedPartitionSetoid
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sameBlock_iff_coalescence_pos {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (i j : Fin n) :
    sameBlock c i j ↔ 0<coalescence (depth := depth+1) ⟨c,f⟩ i j := by
  obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
  by_cases h : a=b
  · subst b
    rw [coalescence_same]
    change c.index (c.emb a i)=c.index (c.emb a j) ↔ _
    simp [index_emb]
  · rw [coalescence_cross c f h]
    change c.index (c.emb a i)=c.index (c.emb b j) ↔ _
    simp [index_emb,h]

theorem eq_of_levelRelations (depth n : ℕ) (t u : NestedPartition depth n)
    (h : ∀l : Fin depth,∀i j : Fin n,
      ((l : ℕ)<coalescence t i j ↔ (l : ℕ)<coalescence u i j)) : t=u := by
  induction depth generalizing n with
  | zero =>
    change (t : PUnit)=u
    exact @Subsingleton.elim PUnit inferInstance t u
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨d,g⟩ := u
    have hcd : c=d := by
      apply eq_of_sameBlock
      intro i j
      exact (sameBlock_iff_coalescence_pos c f i j).trans
        ((h 0 i j).trans (sameBlock_iff_coalescence_pos d g i j).symm)
    subst d
    have hfg : f=g := by
      funext b
      apply ih
      intro l i j
      have H := h l.succ (c.equivSigma ⟨b,i⟩) (c.equivSigma ⟨b,j⟩)
      rw [coalescence_same,coalescence_same] at H
      simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using H
    exact congrArg (Sigma.mk c) hfg

theorem exists_nestedPartition (depth n : ℕ) (r : Fin depth→Setoid (Fin n))
    (hRefine : ∀l k : Fin depth,l≤k→∀i j : Fin n,(r k).r i j→(r l).r i j) :
    ∃t : NestedPartition depth n,∀l : Fin depth,∀i j : Fin n,
      ((l : ℕ)<coalescence t i j ↔ (r l).r i j) := by
  classical
  induction depth generalizing n with
  | zero =>
    refine ⟨default,?_⟩
    intro l
    exact Fin.elim0 l
  | succ depth ih =>
    let c := ofSetoid n (r 0)
    have hFirst (i j : Fin n) : sameBlock c i j ↔ (r 0).r i j :=
      sameBlock_ofSetoid n (r 0) i j
    let childR (b : Fin c.length) (l : Fin depth) : Setoid (Fin (c.partSize b)) :=
      ⟨fun i j ↦ (r l.succ).r (c.emb b i) (c.emb b j),
        ⟨fun i ↦ (r l.succ).refl _,fun h ↦ (r l.succ).symm h,
          fun h h' ↦ (r l.succ).trans h h'⟩⟩
    have hChildRefine (b : Fin c.length) : ∀l k : Fin depth,l≤k→
        ∀i j : Fin (c.partSize b),(childR b k).r i j→(childR b l).r i j := by
      intro l k hlk i j hij
      exact hRefine l.succ k.succ (by simpa only [Fin.succ_le_succ_iff] using hlk) _ _ hij
    have hChild (b : Fin c.length) := ih (c.partSize b) (childR b) (hChildRefine b)
    let f : Children depth c := fun b ↦ (hChild b).choose
    have hf (b : Fin c.length) (l : Fin depth) (i j : Fin (c.partSize b)) :
        ((l : ℕ)<coalescence (f b) i j ↔ (r l.succ).r (c.emb b i) (c.emb b j)) :=
      (hChild b).choose_spec l i j
    refine ⟨⟨c,f⟩,?_⟩
    intro l i j
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
    by_cases hab : a=b
    · subst b
      rw [coalescence_same]
      refine Fin.cases ?_ (fun l ↦ ?_) l
      · have H : (r 0).r (c.emb a i) (c.emb a j) :=
          (hFirst _ _).1 (by simp [sameBlock,index_emb])
        exact iff_of_true (Nat.zero_lt_succ _) H
      · change ((l.succ : ℕ)<coalescence (f a) i j+1 ↔
          (r l.succ).r (c.emb a i) (c.emb a j))
        simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using hf a l i j
    · rw [coalescence_cross c f hab]
      refine iff_of_false (Nat.not_lt_zero _) ?_
      intro hij
      have H := (hFirst _ _).2 (hRefine 0 l (Fin.zero_le l) _ _ hij)
      apply hab
      change c.index (c.emb a i)=c.index (c.emb b j) at H
      simpa only [index_emb] using H

theorem exists_unique_nestedPartition (depth n : ℕ) (r : Fin depth→Setoid (Fin n))
    (hRefine : ∀l k : Fin depth,l≤k→∀i j : Fin n,(r k).r i j→(r l).r i j) :
    ∃! t : NestedPartition depth n,∀l : Fin depth,∀i j : Fin n,
      ((l : ℕ)<coalescence t i j ↔ (r l).r i j) := by
  obtain ⟨t,ht⟩ := exists_nestedPartition depth n r hRefine
  refine ⟨t,ht,?_⟩
  intro u hu
  exact eq_of_levelRelations depth n u t (fun l i j ↦ (hu l i j).trans (ht l i j).symm)

def ofNestedSetoids (depth n : ℕ) (r : Fin depth→Setoid (Fin n))
    (hRefine : ∀l k : Fin depth,l≤k→∀i j : Fin n,(r k).r i j→(r l).r i j) :
    NestedPartition depth n := (exists_nestedPartition depth n r hRefine).choose

theorem coalescence_ofNestedSetoids (depth n : ℕ) (r : Fin depth→Setoid (Fin n))
    (hRefine : ∀l k : Fin depth,l≤k→∀i j : Fin n,(r k).r i j→(r l).r i j)
    (l : Fin depth) (i j : Fin n) :
    ((l : ℕ)<coalescence (ofNestedSetoids depth n r hRefine) i j ↔ (r l).r i j) :=
  (exists_nestedPartition depth n r hRefine).choose_spec l i j


end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionSetoid
