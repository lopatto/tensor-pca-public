-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRootSupport

/-! Literal selected-child support under the good threshold relations. Child arrays are
the original spins along their exact ordered block embeddings.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeChildSupport
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteNestedPartitionInsertionBlocks FiniteNestedPartitionInsertionOld
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeInsertionSupport
open SphericalGGTreeRootSupport NonRSUpperProofs.SphericalPositivePerturbation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem thresholdGood_block_cons {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (c : OrderedFinpartition n) (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old)) (k : Fin c.length) :
    thresholdGood (fun l : Fin depth ↦ cuts l.succ)
      (Fin.cons fresh (fun a : Fin (c.partSize k) ↦ old (c.emb k a))) := by
  let phi : Fin (c.partSize k+1)→Fin (n+1) := Fin.cons 0 (fun a ↦ (c.emb k a).succ)
  have hVal (i : Fin (c.partSize k+1)) :
      (Fin.cons fresh old : Fin (n+1)→UnitSpin N) (phi i)=
        (Fin.cons fresh (fun a : Fin (c.partSize k) ↦ old (c.emb k a)) : Fin (c.partSize k+1)→UnitSpin N) i := by
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  intro l
  have H := (hgood l.succ).comap phi
  change Equivalence (fun i j : Fin (c.partSize k+1) ↦ cuts l.succ≤
    unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (phi i))
      ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (phi j))) at H
  simpa only [hVal] using H

theorem treeCylinder_block {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (c : OrderedFinpartition n) (f : Children depth c) (old : Fin n→UnitSpin N)
    (hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old) (k : Fin c.length) :
    treeCylinder (fun l : Fin depth ↦ cuts l.succ) (f k)
      (fun a : Fin (c.partSize k) ↦ old (c.emb k a)) := by
  intro l i j
  have H := hOld l.succ (c.emb k i) (c.emb k j)
  rw [coalescence_emb_same] at H
  simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using H

theorem selected_extension_cons_iff {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old))
    (hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old)
    (k : Fin c.length) (o : Insertion depth (c.partSize k) (f k)) :
    treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩) (Fin.cons fresh old) ↔
      cuts 0≤unitOverlap fresh (old (c.emb k ⟨0,c.partSize_pos k⟩)) ∧
      treeCylinder (fun l : Fin depth ↦ cuts l.succ)
        ((extendEquiv depth (c.partSize k)) ⟨f k,o⟩)
        (Fin.cons fresh (fun a : Fin (c.partSize k) ↦ old (c.emb k a))) := by
  constructor
  · intro hNew
    have hFresh := ((treeCylinder_extend_cons_iff cuts hcuts1 _ _ old fresh).1 hNew).2
    constructor
    · have H := hFresh 0 (c.emb k ⟨0,c.partSize_pos k⟩)
      rw [coalescence_extend_some_fresh_same] at H
      exact H.1 (Nat.zero_lt_succ _)
    · apply (treeCylinder_extend_cons_iff (fun l : Fin depth ↦ cuts l.succ)
        (fun l ↦ hcuts1 l.succ) _ _ _ fresh).2
      refine ⟨treeCylinder_block cuts c f old hOld k,?_⟩
      intro l a
      have H := hFresh l.succ (c.emb k a)
      rw [coalescence_extend_some_fresh_same] at H
      simpa only [Fin.val_succ,Nat.add_lt_add_iff_right] using H
  · rintro ⟨hb,hChild⟩
    apply (treeCylinder_extend_cons_iff cuts hcuts1 _ _ old fresh).2
    refine ⟨hOld,?_⟩
    intro l i
    obtain ⟨⟨b,a⟩,rfl⟩ := c.equivSigma.surjective i
    change ((l : ℕ)<coalescence ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩)
      0 (c.emb b a).succ ↔ cuts l≤unitOverlap fresh (old (c.emb b a)))
    by_cases hbk : b=k
    · subst b
      rw [coalescence_extend_some_fresh_same]
      cases l using Fin.cases with
      | zero =>
        exact iff_of_true (Nat.zero_lt_succ _)
          ((rootBall_sameClass_iff cuts c f old fresh hgood hOld k a).2 hb)
      | succ l =>
        have H := hChild l 0 a.succ
        simpa only [Fin.cons_zero,Fin.cons_succ,Fin.val_succ,Nat.add_lt_add_iff_right] using H
    · rw [coalescence_extend_some_fresh_cross c f k b o a hbk]
      apply iff_of_false (Nat.not_lt_zero _)
      intro hRel
      have hRoot := (hcuts (Fin.zero_le l)).trans hRel
      have hb' := (rootBall_sameClass_iff cuts c f old fresh hgood hOld b a).1 hRoot
      exact hbk (rootBall_unique cuts c f old fresh hgood hOld b k hb' hb)

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeChildSupport
