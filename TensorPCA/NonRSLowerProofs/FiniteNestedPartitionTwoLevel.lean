-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Logic.Equiv.Prod

/-! Depth-two ordered finite partitions. Insertion prepends fresh label zero and shifts
old labels by Fin.succ, as in OrderedFinpartition.extendEquiv.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionTwoLevel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Children {n : ℕ} (c : OrderedFinpartition n) :=
  (i : Fin c.length)→OrderedFinpartition (c.partSize i)

abbrev TwoLevelPartition (n : ℕ) := Σc : OrderedFinpartition n,Children c

abbrev Insertion {n : ℕ} (t : TwoLevelPartition n) :=
  Option (Σi : Fin t.1.length,Option (Fin (t.2 i).length))

def childrenLeftEquiv {n : ℕ} (c : OrderedFinpartition n) :
    Children c.extendLeft ≃ Children c where
  toFun f i := f i.succ
  invFun f := Fin.cons (default : OrderedFinpartition 1) f
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · haveI : Subsingleton (OrderedFinpartition (c.extendLeft.partSize (0 : Fin (c.length+1)))) := by
        simpa only [OrderedFinpartition.extendLeft_partSize,Fin.cons_zero] using
          (inferInstance : Subsingleton (OrderedFinpartition 1))
      exact Subsingleton.elim _ _
    · rfl
  right_inv f := by funext i; rfl

def piSelectedSigmaEquiv {I : Type*} [DecidableEq I]
    (beta : I→Type*) (i : I) (gamma : beta i→Type*) :
    (Σf : (j : I)→beta j,gamma (f i)) ≃
      (Σb : beta i,gamma b)×((j : {j : I // j≠i})→beta j) := by
  let e : (Σf : (j : I)→beta j,gamma (f i)) ≃
      (Σp : beta i×((j : {j : I // j≠i})→beta j),gamma p.1) :=
    Equiv.sigmaCongr (Equiv.piSplitAt i beta) (fun _ ↦ Equiv.refl _)
  exact e.trans {
    toFun := fun p ↦ (⟨p.1.1,p.2⟩,p.1.2)
    invFun := fun p ↦ ⟨(p.1.1,p.2),p.1.2⟩
    left_inv := by rintro ⟨⟨b,f⟩,g⟩; rfl
    right_inv := by rintro ⟨⟨b,g⟩,f⟩; rfl }

def childrenMiddleSplitEquiv {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    Children (c.extendMiddle i) ≃
      OrderedFinpartition (c.partSize i+1)×
        ((j : {j : Fin c.length // j≠i})→OrderedFinpartition (c.partSize j)) := by
  refine (Equiv.piSplitAt i (fun j ↦ OrderedFinpartition ((c.extendMiddle i).partSize j))).trans ?_
  refine Equiv.prodCongr (Equiv.cast ?_) (Equiv.piCongrRight (fun j ↦ Equiv.cast ?_))
  · simp only [OrderedFinpartition.extendMiddle_partSize,Function.update_self]
  · simp only [OrderedFinpartition.extendMiddle_partSize,Function.update_of_ne j.property]

def childrenMiddleEquiv {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (Σf : Children c,Option (Fin (f i).length)) ≃ Children (c.extendMiddle i) :=
  (piSelectedSigmaEquiv (fun j ↦ OrderedFinpartition (c.partSize j)) i
    (fun b ↦ Option (Fin b.length))).trans
    ((Equiv.prodCongr (OrderedFinpartition.extendEquiv (c.partSize i)) (Equiv.refl _)).trans
      (childrenMiddleSplitEquiv c i).symm)

def insertionSplitEquiv {n : ℕ} (c : OrderedFinpartition n) :
    (Σf : Children c,Option (Σi : Fin c.length,Option (Fin (f i).length))) ≃
      Children c ⊕ (Σi : Fin c.length,Σf : Children c,Option (Fin (f i).length)) where
  toFun t := match t with
    | ⟨f,none⟩ => Sum.inl f
    | ⟨f,some ⟨i,o⟩⟩ => Sum.inr ⟨i,f,o⟩
  invFun t := match t with
    | Sum.inl f => ⟨f,none⟩
    | Sum.inr ⟨i,f,o⟩ => ⟨f,some ⟨i,o⟩⟩
  left_inv := by rintro ⟨f,_|⟨i,o⟩⟩ <;> rfl
  right_inv := by rintro (f|⟨i,f,o⟩) <;> rfl

def outerChoiceSplitEquiv {n : ℕ} (c : OrderedFinpartition n) :
    (Σo : Option (Fin c.length),Children (c.extend o)) ≃
      Children c.extendLeft ⊕ (Σi : Fin c.length,Children (c.extendMiddle i)) where
  toFun t := match t with
    | ⟨none,f⟩ => Sum.inl f
    | ⟨some i,f⟩ => Sum.inr ⟨i,f⟩
  invFun t := match t with
    | Sum.inl f => ⟨none,f⟩
    | Sum.inr ⟨i,f⟩ => ⟨some i,f⟩
  left_inv := by rintro ⟨_|i,f⟩ <;> rfl
  right_inv := by rintro (f|⟨i,f⟩) <;> rfl

def childrenInsertionEquiv {n : ℕ} (c : OrderedFinpartition n) :
    (Σf : Children c,Option (Σi : Fin c.length,Option (Fin (f i).length))) ≃
      (Σo : Option (Fin c.length),Children (c.extend o)) :=
  (insertionSplitEquiv c).trans
    ((Equiv.sumCongr (childrenLeftEquiv c).symm
      (Equiv.sigmaCongrRight (fun i ↦ childrenMiddleEquiv c i))).trans
      (outerChoiceSplitEquiv c).symm)

theorem children_atomic_zero_unique (f : Children (OrderedFinpartition.atomic 0)) :
    f=(fun _ ↦ (default : OrderedFinpartition 1)) := by
  funext i
  exact Fin.elim0 i

theorem children_atomic_one_unique (f : Children (OrderedFinpartition.atomic 1)) :
    f=(fun _ ↦ (default : OrderedFinpartition 1)) := by
  funext i
  haveI : Subsingleton (OrderedFinpartition ((OrderedFinpartition.atomic 1).partSize i)) := by
    change Subsingleton (OrderedFinpartition 1)
    infer_instance
  exact Subsingleton.elim _ _

/-- Insert a fresh label zero into both ordered levels. A new outer block has the unique
singleton child; an old outer block uses its child's standard insertion equivalence,
keeping every other child unchanged.
-/
def twoLevelExtendEquiv (n : ℕ) :
    (Σt : TwoLevelPartition n,Insertion t) ≃ TwoLevelPartition (n+1) := by
  refine (Equiv.sigmaAssoc (fun (c : OrderedFinpartition n) (f : Children c) ↦
    Insertion (⟨c,f⟩ : TwoLevelPartition n))).trans ?_
  refine (Equiv.sigmaCongrRight (fun c ↦ childrenInsertionEquiv c)).trans ?_
  exact (Equiv.sigmaAssoc (fun (c : OrderedFinpartition n) (o : Option (Fin c.length)) ↦
    Children (c.extend o))).symm.trans (Equiv.sigmaCongrLeft (OrderedFinpartition.extendEquiv n))

theorem twoLevelExtendEquiv_outer {n : ℕ} (t : TwoLevelPartition n) (o : Insertion t) :
    (twoLevelExtendEquiv n ⟨t,o⟩).1=t.1.extend (o.map (fun i ↦ i.1)) := by
  cases o with
  | none => rfl
  | some p => obtain ⟨i,o⟩ := p; rfl

end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionTwoLevel
