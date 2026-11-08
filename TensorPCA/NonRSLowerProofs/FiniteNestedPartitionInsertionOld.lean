-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionBlocks

/-! Nested insertion preserves every old coalescence level.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionOld
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteNestedDiscountedPartitionExtension FiniteOrderedPartitionSetoid
open FiniteNestedPartitionInsertionBlocks
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coalescence_heq_cast {depth a b : ℕ} (h : a=b)
    (t : NestedPartition depth a) (u : NestedPartition depth b) (htu : HEq t u)
    (i j : Fin b) : coalescence t (Fin.cast h.symm i) (Fin.cast h.symm j)=coalescence u i j := by
  cases h
  cases eq_of_heq htu
  rfl

theorem coalescence_extend_none_old {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (i j : Fin n) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) i.succ j.succ=
      coalescence (depth := depth+1) ⟨c,f⟩ i j := by
  obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
  rw [extendEquiv_none]
  change coalescence (depth := depth+1) ⟨c.extendLeft,(childrenLeftEquiv depth c).symm f⟩
    (c.emb a i).succ (c.emb b j).succ=coalescence (depth := depth+1) ⟨c,f⟩ (c.emb a i) (c.emb b j)
  by_cases hab : a=b
  · subst b
    have hsize : c.extendLeft.partSize a.succ=c.partSize a := by simp
    have hei : c.extendLeft.emb a.succ (Fin.cast hsize.symm i)=(c.emb a i).succ := by
      simp [OrderedFinpartition.extendLeft]
    have hej : c.extendLeft.emb a.succ (Fin.cast hsize.symm j)=(c.emb a j).succ := by
      simp [OrderedFinpartition.extendLeft]
    conv_lhs => rw [← hei,← hej]
    rw [coalescence_emb_same,coalescence_emb_same]
    exact congrArg (fun z : ℕ ↦ z+1) (coalescence_heq_cast hsize _ _ (HEq.rfl) i j)
  · have hNew : coalescence (depth := depth+1) ⟨c.extendLeft,(childrenLeftEquiv depth c).symm f⟩
        (c.emb a i).succ (c.emb b j).succ=0 := by
      apply coalescence_zero_of_not_sameBlock
      simpa only [sameBlock,index_extendLeft_succ,index_emb,Fin.succ_inj] using hab
    rw [hNew]
    exact (coalescence_cross c f hab i j).symm

theorem coalescence_extend_some_selected_old {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (k : Fin c.length) (o : Insertion depth (c.partSize k) (f k))
    (i j : Fin (c.partSize k)) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩) (c.emb k i).succ (c.emb k j).succ=
      coalescence ((extendEquiv depth (c.partSize k)) ⟨f k,o⟩) i.succ j.succ+1 := by
  rw [extendEquiv_some]
  let g := (childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c k) ⟨f,o⟩
  have hsize : (c.extendMiddle k).partSize k=c.partSize k+1 := by simp
  have hei : (c.extendMiddle k).emb k (Fin.cast hsize.symm i.succ)=(c.emb k i).succ := by
    simp [OrderedFinpartition.extendMiddle]
  have hej : (c.extendMiddle k).emb k (Fin.cast hsize.symm j.succ)=(c.emb k j).succ := by
    simp [OrderedFinpartition.extendMiddle]
  change coalescence (depth := depth+1) ⟨c.extendMiddle k,g⟩ (c.emb k i).succ (c.emb k j).succ=_
  conv_lhs => rw [← hei,← hej]
  rw [coalescence_emb_same]
  exact congrArg (fun z : ℕ ↦ z+1) (coalescence_heq_cast hsize _ _
    (childrenMiddle_same_heq (fun m ↦ extendEquiv depth m) c f k o) i.succ j.succ)

theorem coalescence_extend_some_unselected_old {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (k b : Fin c.length) (o : Insertion depth (c.partSize k) (f k))
    (i j : Fin (c.partSize b)) (hbk : b≠k) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩) (c.emb b i).succ (c.emb b j).succ=
      coalescence (f b) i j+1 := by
  rw [extendEquiv_some]
  let g := (childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c k) ⟨f,o⟩
  have hsize : (c.extendMiddle k).partSize b=c.partSize b := by simp [hbk]
  have hei : (c.extendMiddle k).emb b (Fin.cast hsize.symm i)=(c.emb b i).succ := by
    simp [OrderedFinpartition.extendMiddle,hbk]
  have hej : (c.extendMiddle k).emb b (Fin.cast hsize.symm j)=(c.emb b j).succ := by
    simp [OrderedFinpartition.extendMiddle,hbk]
  change coalescence (depth := depth+1) ⟨c.extendMiddle k,g⟩ (c.emb b i).succ (c.emb b j).succ=_
  conv_lhs => rw [← hei,← hej]
  rw [coalescence_emb_same]
  exact congrArg (fun z : ℕ ↦ z+1) (coalescence_heq_cast hsize _ _
    (childrenMiddle_ne_heq (fun m ↦ extendEquiv depth m) c f k b o hbk) i j)

theorem coalescence_extend_old (depth n : ℕ) (t : NestedPartition depth n)
    (o : Insertion depth n t) (i j : Fin n) :
    coalescence ((extendEquiv depth n) ⟨t,o⟩) i.succ j.succ=coalescence t i j := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => exact coalescence_extend_none_old c f i j
    | some a =>
      obtain ⟨k,o⟩ := a
      obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
      obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
      change coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩)
        (c.emb a i).succ (c.emb b j).succ=
        coalescence (depth := depth+1) ⟨c,f⟩ (c.emb a i) (c.emb b j)
      by_cases hab : a=b
      · subst b
        by_cases hak : a=k
        · subst a
          rw [coalescence_extend_some_selected_old,coalescence_emb_same,
            ih (c.partSize k) (f k) o i j]
        · rw [coalescence_extend_some_unselected_old c f k a o i j hak,coalescence_emb_same]
      · rw [extendEquiv_some]
        have hNew : coalescence (depth := depth+1)
            ⟨c.extendMiddle k,(childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c k) ⟨f,o⟩⟩
            (c.emb a i).succ (c.emb b j).succ=0 := by
          apply coalescence_zero_of_not_sameBlock
          simpa only [sameBlock,index_extendMiddle_succ,index_emb] using hab
        rw [hNew]
        exact (coalescence_cross c f hab i j).symm

theorem level_extend_old (depth n : ℕ) (t : NestedPartition depth n)
    (o : Insertion depth n t) (i j : Fin n) :
    level ((extendEquiv depth n) ⟨t,o⟩) i.succ j.succ=level t i j :=
  Fin.ext (coalescence_extend_old depth n t o i j)

theorem overlap_extend_old (depth n : ℕ) (t : NestedPartition depth n)
    (o : Insertion depth n t) (q : Fin (depth+1)→ℝ) (i j : Fin n) :
    overlap ((extendEquiv depth n) ⟨t,o⟩) q i.succ j.succ=overlap t q i j :=
  congrArg q (level_extend_old depth n t o i j)


end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionOld
