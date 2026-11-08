-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionSupport

/-! Deterministic on-good root insertion indicators, with ordered block representatives
and no division by a parent probability.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeRootSupport
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedPartitionSetoid
open FiniteOrderedPartitionSetoid SphericalGGTreeCylinder SphericalGGTreeExtraction
open SphericalGGTreeInsertionSupport NonRSUpperProofs.SphericalPositivePerturbation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

theorem rootBall_sameClass_iff {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old))
    (hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old)
    (b : Fin c.length) (a : Fin (c.partSize b)) :
    cuts 0≤unitOverlap fresh (old (c.emb b a)) ↔
      cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩)) := by
  have hClass : sameBlock c (c.emb b a) (c.emb b ⟨0,c.partSize_pos b⟩) := by
    simp only [sameBlock,index_emb]
  have H := (hOld 0 _ _).1 ((sameBlock_iff_coalescence_pos c f _ _).1 hClass)
  have hRel : cuts 0≤unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb b a).succ)
      ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb b ⟨0,c.partSize_pos b⟩).succ) := by
    simpa only [Fin.cons_succ] using H
  constructor
  · intro h
    have hf : cuts 0≤unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) 0)
        ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb b a).succ) := by
      simpa only [Fin.cons_zero,Fin.cons_succ] using h
    simpa only [Fin.cons_zero,Fin.cons_succ] using (hgood 0).trans hf hRel
  · intro h
    have hf : cuts 0≤unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) 0)
        ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb b ⟨0,c.partSize_pos b⟩).succ) := by
      simpa only [Fin.cons_zero,Fin.cons_succ] using h
    simpa only [Fin.cons_zero,Fin.cons_succ] using (hgood 0).trans hf ((hgood 0).symm hRel)

theorem rootBall_unique {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old))
    (hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old)
    (b d : Fin c.length)
    (hb : cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩)))
    (hd : cuts 0≤unitOverlap fresh (old (c.emb d ⟨0,c.partSize_pos d⟩))) : b=d := by
  have hb' : cuts 0≤unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) 0)
      ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb b ⟨0,c.partSize_pos b⟩).succ) := by
    simpa only [Fin.cons_zero,Fin.cons_succ] using hb
  have hd' : cuts 0≤unitOverlap ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) 0)
      ((Fin.cons fresh old : Fin (n+1)→UnitSpin N) (c.emb d ⟨0,c.partSize_pos d⟩).succ) := by
    simpa only [Fin.cons_zero,Fin.cons_succ] using hd
  have H : cuts 0≤unitOverlap (old (c.emb b ⟨0,c.partSize_pos b⟩))
      (old (c.emb d ⟨0,c.partSize_pos d⟩)) := by
    simpa only [Fin.cons_succ] using (hgood 0).trans ((hgood 0).symm hb') hd'
  have hClass := (sameBlock_iff_coalescence_pos c f _ _).2 ((hOld 0 _ _).2 H)
  simpa only [sameBlock,index_emb] using hClass

theorem root_new_indicator_eq {N depth n : ℕ} (cuts : Fin (depth+1)→ℝ)
    (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (c : OrderedFinpartition n) (f : Children depth c)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old)) :
    (if treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) (Fin.cons fresh old)
      then (1 : ℝ) else 0)=
      (if treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old then (1 : ℝ) else 0)*
        (1-∑b : Fin c.length,
          (if cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩)) then (1 : ℝ) else 0)) := by
  by_cases hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old
  · by_cases H : ∃b : Fin c.length,cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩))
    · obtain ⟨b,hb⟩ := H
      have hsum : (∑d : Fin c.length,
          (if cuts 0≤unitOverlap fresh (old (c.emb d ⟨0,c.partSize_pos d⟩)) then (1 : ℝ) else 0))=1 := by
        rw [Finset.sum_eq_single b]
        · simp only [if_pos hb]
        · intro d _ hdb
          have hd : ¬cuts 0≤unitOverlap fresh (old (c.emb d ⟨0,c.partSize_pos d⟩)) :=
            fun hd ↦ hdb (rootBall_unique cuts c f old fresh hgood hOld d b hd hb)
          simp only [if_neg hd]
        · intro h
          exact (h (Finset.mem_univ b)).elim
      have hNew : ¬treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) (Fin.cons fresh old) := by
        intro h
        have H := ((treeCylinder_extend_none_cons_iff_firstCut cuts hcuts hcuts1 c f old fresh).1 h).2
        exact (not_lt_of_ge hb) (H (c.emb b ⟨0,c.partSize_pos b⟩))
      simp only [if_pos hOld,if_neg hNew,hsum,sub_self,mul_zero]
    · have hsum : (∑d : Fin c.length,
          (if cuts 0≤unitOverlap fresh (old (c.emb d ⟨0,c.partSize_pos d⟩)) then (1 : ℝ) else 0))=0 := by
        apply Finset.sum_eq_zero
        intro d _
        exact if_neg (fun hd ↦ H ⟨d,hd⟩)
      have hAll : ∀i : Fin n,unitOverlap fresh (old i)<cuts 0 := by
        intro i
        obtain ⟨⟨b,a⟩,rfl⟩ := c.equivSigma.surjective i
        apply lt_of_not_ge
        intro h
        change cuts 0≤unitOverlap fresh (old (c.emb b a)) at h
        exact H ⟨b,(rootBall_sameClass_iff cuts c f old fresh hgood hOld b a).1 h⟩
      have hNew := (treeCylinder_extend_none_cons_iff_firstCut cuts hcuts hcuts1 c f old fresh).2 ⟨hOld,hAll⟩
      simp only [if_pos hOld,if_pos hNew,hsum,sub_zero,one_mul]
  · have hNew : ¬treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,none⟩) (Fin.cons fresh old) := by
      intro h
      exact hOld ((treeCylinder_extend_none_cons_iff_firstCut cuts hcuts hcuts1 c f old fresh).1 h).1
    simp only [if_neg hOld,if_neg hNew,zero_mul]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeRootSupport
