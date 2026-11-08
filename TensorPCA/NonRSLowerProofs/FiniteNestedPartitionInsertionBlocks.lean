-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionExtension
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionSetoid

/-! Exact old/fresh block support of the nested insertion equivalence. The new label is
zero and old labels are shifted by Fin.succ.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionBlocks
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteNestedDiscountedPartitionExtension FiniteOrderedPartitionSetoid
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coalescence_heq_cast {depth a b : ℕ} (h : a=b)
    (t : NestedPartition depth a) (u : NestedPartition depth b) (htu : HEq t u)
    (i j : Fin b) : coalescence t (Fin.cast h.symm i) (Fin.cast h.symm j)=coalescence u i j := by
  cases h
  cases eq_of_heq htu
  rfl

theorem coalescence_emb_same {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (b : Fin c.length) (i j : Fin (c.partSize b)) :
    coalescence (depth := depth+1) ⟨c,f⟩ (c.emb b i) (c.emb b j)=coalescence (f b) i j+1 :=
  coalescence_same c f b i j

theorem coalescence_zero_of_not_sameBlock {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (i j : Fin n) (h : ¬sameBlock c i j) :
    coalescence (depth := depth+1) ⟨c,f⟩ i j=0 := by
  have H : ¬0<coalescence (depth := depth+1) ⟨c,f⟩ i j :=
    fun hpos ↦ h ((sameBlock_iff_coalescence_pos c f i j).2 hpos)
  omega

theorem coalescence_extend_none_fresh {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (j : Fin n) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) 0 j.succ=0 := by
  rw [extendEquiv_none]
  apply coalescence_zero_of_not_sameBlock
  exact sameBlock_extendLeft_zero_succ c j

theorem coalescence_extend_some_fresh_cross {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (k b : Fin c.length)
    (o : Insertion depth (c.partSize k) (f k)) (a : Fin (c.partSize b)) (hbk : b≠k) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩) 0 (c.emb b a).succ=0 := by
  rw [extendEquiv_some]
  apply coalescence_zero_of_not_sameBlock
  rw [sameBlock_extendMiddle_zero_succ,index_emb]
  exact hbk.symm

theorem coalescence_extend_some_fresh_same {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (k : Fin c.length)
    (o : Insertion depth (c.partSize k) (f k)) (a : Fin (c.partSize k)) :
    coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩) 0 (c.emb k a).succ=
      coalescence ((extendEquiv depth (c.partSize k)) ⟨f k,o⟩) 0 a.succ+1 := by
  rw [extendEquiv_some]
  let g := (childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c k) ⟨f,o⟩
  have hsize : (c.extendMiddle k).partSize k=c.partSize k+1 := by simp
  have he0 : (c.extendMiddle k).emb k (Fin.cast hsize.symm (0 : Fin (c.partSize k+1)))=0 := by
    simp [OrderedFinpartition.extendMiddle]
  have he1 : (c.extendMiddle k).emb k (Fin.cast hsize.symm a.succ)=(c.emb k a).succ := by
    simp [OrderedFinpartition.extendMiddle]
  change coalescence (depth := depth+1) ⟨c.extendMiddle k,g⟩ 0 (c.emb k a).succ=_
  conv_lhs => rw [← he0,← he1]
  rw [coalescence_emb_same]
  exact congrArg (fun z : ℕ ↦ z+1) (coalescence_heq_cast hsize _ _
    (childrenMiddle_same_heq (fun m ↦ extendEquiv depth m) c f k o) 0 a.succ)


end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionInsertionBlocks
