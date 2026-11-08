-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeChildSupport

/-! Literal all-depth insertion test algebra. A new-child branch is parent
membership minus child memberships; a terminal branch is parent membership.
There are no products along rare paths and no conditional-probability division. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScore
open FiniteNestedPartition FiniteNestedPartitionOverlap
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeInsertionSupport
open SphericalGGTreeRootSupport SphericalGGTreeChildSupport
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

def insertionScore {N : ℕ} : (depth n : ℕ)→(cuts : Fin depth→ℝ)→
    (t : NestedPartition depth n)→Insertion depth n t→
    (Fin n→UnitSpin N)→UnitSpin N→ℝ→ℝ
  | 0,_,_,_,_,_,_,parent => parent
  | depth+1,_,cuts,⟨c,f⟩,none,old,fresh,parent =>
      parent-∑b : Fin c.length,
        (if cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩)) then 1 else 0)
  | depth+1,_,cuts,⟨c,f⟩,some ⟨k,o⟩,old,fresh,_ =>
      insertionScore depth (c.partSize k) (fun l ↦ cuts l.succ) (f k) o
        (fun a ↦ old (c.emb k a)) fresh
        (if cuts 0≤unitOverlap fresh (old (c.emb k ⟨0,c.partSize_pos k⟩)) then 1 else 0)

theorem insertionScore_zero_of_no_balls {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hNo : ∀l : Fin depth,∀i : Fin n,¬cuts l≤unitOverlap fresh (old i)) :
    insertionScore depth n cuts t o old fresh 0=0 := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none =>
      simp only [insertionScore]
      have H : (∑b : Fin c.length,
          (if cuts 0≤unitOverlap fresh (old (c.emb b ⟨0,c.partSize_pos b⟩)) then (1 : ℝ) else 0))=0 := by
        apply Finset.sum_eq_zero
        intro b _
        exact if_neg (hNo 0 _)
      rw [H,sub_zero]
    | some a =>
      obtain ⟨k,o⟩ := a
      simp only [insertionScore,if_neg (hNo 0 (c.emb k ⟨0,c.partSize_pos k⟩))]
      exact ih (c.partSize k) (fun l ↦ cuts l.succ) (f k) o
        (fun a ↦ old (c.emb k a)) (fun l a ↦ hNo l.succ (c.emb k a))

theorem insertion_indicator_eq {N : ℕ} (depth n : ℕ) (cuts : Fin depth→ℝ)
    (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t)
    (old : Fin n→UnitSpin N) (fresh : UnitSpin N)
    (hgood : thresholdGood cuts (Fin.cons fresh old)) :
    (if treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) (Fin.cons fresh old) then (1 : ℝ) else 0)=
      (if treeCylinder cuts t old then (1 : ℝ) else 0)*insertionScore depth n cuts t o old fresh 1 := by
  induction depth generalizing n with
  | zero => simp [treeCylinder,insertionScore]
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => exact root_new_indicator_eq cuts hcuts hcuts1 c f old fresh hgood
    | some a =>
      obtain ⟨k,o⟩ := a
      by_cases hOld : treeCylinder cuts (⟨c,f⟩ : NestedPartition (depth+1) n) old
      · by_cases hb : cuts 0≤unitOverlap fresh (old (c.emb k ⟨0,c.partSize_pos k⟩))
        · have hTailMono : Monotone (fun l : Fin depth ↦ cuts l.succ) := by
            intro i j hij
            exact hcuts (by simpa only [Fin.succ_le_succ_iff] using hij)
          have hChildOld := treeCylinder_block cuts c f old hOld k
          have HI := ih (c.partSize k) (fun l ↦ cuts l.succ) hTailMono (fun l ↦ hcuts1 l.succ)
            (f k) o (fun a ↦ old (c.emb k a)) (thresholdGood_block_cons cuts c old fresh hgood k)
          have Hsupport := selected_extension_cons_iff cuts hcuts hcuts1 c f old fresh hgood hOld k o
          simp only [insertionScore,if_pos hOld,if_pos hb,one_mul]
          calc
            (if treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩)
                (Fin.cons fresh old) then (1 : ℝ) else 0)=
                (if treeCylinder (fun l : Fin depth ↦ cuts l.succ)
                  ((extendEquiv depth (c.partSize k)) ⟨f k,o⟩)
                  (Fin.cons fresh (fun a ↦ old (c.emb k a))) then 1 else 0) := by
              simp only [Hsupport,hb,true_and]
            _=insertionScore depth (c.partSize k) (fun l ↦ cuts l.succ)
                (f k) o (fun a ↦ old (c.emb k a)) fresh 1 := by
              simpa only [if_pos hChildOld,one_mul] using HI
        · have hNew : ¬treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩)
              (Fin.cons fresh old) := by
            intro h
            exact hb ((selected_extension_cons_iff cuts hcuts hcuts1 c f old fresh hgood hOld k o).1 h).1
          have hNo : ∀l : Fin depth,∀a : Fin (c.partSize k),
              ¬cuts l.succ≤unitOverlap fresh (old (c.emb k a)) := by
            intro l a h
            have Hroot := (hcuts (Fin.zero_le l.succ)).trans h
            exact hb ((rootBall_sameClass_iff cuts c f old fresh hgood hOld k a).1 Hroot)
          have Hz := insertionScore_zero_of_no_balls depth (c.partSize k) (fun l ↦ cuts l.succ)
            (f k) o (fun a ↦ old (c.emb k a)) fresh hNo
          simp only [insertionScore,if_pos hOld,if_neg hb,if_neg hNew,one_mul,Hz]
      · have hNew : ¬treeCylinder cuts ((extendEquiv (depth+1) n) ⟨⟨c,f⟩,some ⟨k,o⟩⟩)
            (Fin.cons fresh old) := by
          intro h
          exact hOld ((treeCylinder_extend_cons_iff cuts hcuts1 _ _ old fresh).1 h).1
        simp only [if_neg hOld,if_neg hNew,zero_mul]

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionScore
