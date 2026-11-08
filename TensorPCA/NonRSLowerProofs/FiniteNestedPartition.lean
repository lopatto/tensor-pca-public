-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartitionTwoLevel

/-! Literal finite nested ordered partitions. Depth zero is deterministic; each later
level is one standard ordered partition with dependent child sizes. No probability
law, sampler or hierarchy interface is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def NestedPartition : ℕ→ℕ→Type
  | 0,_ => PUnit
  | depth+1,n => Σc : OrderedFinpartition n,(i : Fin c.length)→NestedPartition depth (c.partSize i)

def atomic : (depth n : ℕ)→NestedPartition depth n
  | 0,_ => PUnit.unit
  | depth+1,n => ⟨OrderedFinpartition.atomic n,fun _ ↦ atomic depth 1⟩

instance nestedInhabited (depth n : ℕ) : Inhabited (NestedPartition depth n) := ⟨atomic depth n⟩

instance nestedFintype (depth n : ℕ) : Fintype (NestedPartition depth n) := by
  induction depth generalizing n with
  | zero => change Fintype PUnit; infer_instance
  | succ depth ih =>
    change Fintype (Σc : OrderedFinpartition n,(i : Fin c.length)→NestedPartition depth (c.partSize i))
    letI (m : ℕ) : Fintype (NestedPartition depth m) := ih m
    infer_instance

instance nestedZeroSubsingleton (depth : ℕ) : Subsingleton (NestedPartition depth 0) := by
  cases depth with
  | zero => change Subsingleton PUnit; infer_instance
  | succ depth =>
    change Subsingleton (Σc : OrderedFinpartition 0,(i : Fin c.length)→NestedPartition depth (c.partSize i))
    letI (c : OrderedFinpartition 0) :
        Subsingleton ((i : Fin c.length)→NestedPartition depth (c.partSize i)) := by
      constructor
      intro f g
      funext i
      have H := c.length_le
      have HI := i.isLt
      omega
    constructor
    rintro ⟨c,f⟩ ⟨c',g⟩
    have hc : c=c' := Subsingleton.elim _ _
    subst c'
    have hf : f=g := Subsingleton.elim _ _
    cases hf
    rfl

instance nestedOneSubsingleton (depth : ℕ) : Subsingleton (NestedPartition depth 1) := by
  induction depth with
  | zero => change Subsingleton PUnit; infer_instance
  | succ depth ih =>
    change Subsingleton (Σc : OrderedFinpartition 1,(i : Fin c.length)→NestedPartition depth (c.partSize i))
    letI (c : OrderedFinpartition 1) :
        Subsingleton ((i : Fin c.length)→NestedPartition depth (c.partSize i)) := by
      constructor
      intro f g
      funext i
      have hsize : c.partSize i=1 := by
        have H := c.partSize_le i
        have HP := c.partSize_pos i
        omega
      haveI : Subsingleton (NestedPartition depth (c.partSize i)) := by rw [hsize]; exact ih
      exact Subsingleton.elim _ _
    constructor
    rintro ⟨c,f⟩ ⟨c',g⟩
    have hc : c=c' := Subsingleton.elim _ _
    subst c'
    have hf : f=g := Subsingleton.elim _ _
    cases hf
    rfl

instance nestedZeroUnique (depth : ℕ) : Unique (NestedPartition depth 0) := Unique.mk' _
instance nestedOneUnique (depth : ℕ) : Unique (NestedPartition depth 1) := Unique.mk' _

def Insertion : (depth n : ℕ)→NestedPartition depth n→Type
  | 0,_,_ => PUnit
  | depth+1,_,t => Option (Σi : Fin t.1.length,Insertion depth (t.1.partSize i) (t.2 i))

instance insertionFintype (depth n : ℕ) (t : NestedPartition depth n) : Fintype (Insertion depth n t) := by
  induction depth generalizing n with
  | zero => change Fintype PUnit; infer_instance
  | succ depth ih =>
    change Fintype (Option (Σi : Fin t.1.length,Insertion depth (t.1.partSize i) (t.2 i)))
    letI (m : ℕ) (s : NestedPartition depth m) : Fintype (Insertion depth m s) := ih m s
    infer_instance

abbrev Children {n : ℕ} (depth : ℕ) (c : OrderedFinpartition n) :=
  (i : Fin c.length)→NestedPartition depth (c.partSize i)

def childrenLeftEquiv {n : ℕ} (depth : ℕ) (c : OrderedFinpartition n) :
    Children depth c.extendLeft ≃ Children depth c where
  toFun f i := f i.succ
  invFun f := Fin.cons (default : NestedPartition depth 1) f
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · haveI : Subsingleton (NestedPartition depth (c.extendLeft.partSize (0 : Fin (c.length+1)))) := by
        simpa only [OrderedFinpartition.extendLeft_partSize,Fin.cons_zero] using
          (inferInstance : Subsingleton (NestedPartition depth 1))
      exact Subsingleton.elim _ _
    · rfl
  right_inv f := by funext i; rfl

def childrenMiddleSplitEquiv {n : ℕ} (depth : ℕ) (c : OrderedFinpartition n) (i : Fin c.length) :
    Children depth (c.extendMiddle i) ≃
      NestedPartition depth (c.partSize i+1)×
        ((j : {j : Fin c.length // j≠i})→NestedPartition depth (c.partSize j)) := by
  refine (Equiv.piSplitAt i (fun j ↦ NestedPartition depth ((c.extendMiddle i).partSize j))).trans ?_
  refine Equiv.prodCongr (Equiv.cast ?_) (Equiv.piCongrRight (fun j ↦ Equiv.cast ?_))
  · simp only [OrderedFinpartition.extendMiddle_partSize,Function.update_self]
  · simp only [OrderedFinpartition.extendMiddle_partSize,Function.update_of_ne j.property]

def childrenMiddleEquiv {n : ℕ} (depth : ℕ)
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1))
    (c : OrderedFinpartition n) (i : Fin c.length) :
    (Σf : Children depth c,Insertion depth (c.partSize i) (f i)) ≃
      Children depth (c.extendMiddle i) :=
  (FiniteNestedPartitionTwoLevel.piSelectedSigmaEquiv (fun j ↦ NestedPartition depth (c.partSize j)) i
    (Insertion depth (c.partSize i))).trans
    ((Equiv.prodCongr (E (c.partSize i)) (Equiv.refl _)).trans
      (childrenMiddleSplitEquiv depth c i).symm)

def insertionSplitEquiv {n : ℕ} (depth : ℕ) (c : OrderedFinpartition n) :
    (Σf : Children depth c,Option (Σi : Fin c.length,Insertion depth (c.partSize i) (f i))) ≃
      Children depth c ⊕ (Σi : Fin c.length,Σf : Children depth c,Insertion depth (c.partSize i) (f i)) where
  toFun t := match t with
    | ⟨f,none⟩ => Sum.inl f
    | ⟨f,some ⟨i,o⟩⟩ => Sum.inr ⟨i,f,o⟩
  invFun t := match t with
    | Sum.inl f => ⟨f,none⟩
    | Sum.inr ⟨i,f,o⟩ => ⟨f,some ⟨i,o⟩⟩
  left_inv := by rintro ⟨f,_|⟨i,o⟩⟩ <;> rfl
  right_inv := by rintro (f|⟨i,f,o⟩) <;> rfl

def outerChoiceSplitEquiv {n : ℕ} (depth : ℕ) (c : OrderedFinpartition n) :
    (Σo : Option (Fin c.length),Children depth (c.extend o)) ≃
      Children depth c.extendLeft ⊕ (Σi : Fin c.length,Children depth (c.extendMiddle i)) where
  toFun t := match t with
    | ⟨none,f⟩ => Sum.inl f
    | ⟨some i,f⟩ => Sum.inr ⟨i,f⟩
  invFun t := match t with
    | Sum.inl f => ⟨none,f⟩
    | Sum.inr ⟨i,f⟩ => ⟨some i,f⟩
  left_inv := by rintro ⟨_|i,f⟩ <;> rfl
  right_inv := by rintro (f|⟨i,f⟩) <;> rfl

def childrenInsertionEquiv {n : ℕ} (depth : ℕ)
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1))
    (c : OrderedFinpartition n) :
    (Σf : Children depth c,Option (Σi : Fin c.length,Insertion depth (c.partSize i) (f i))) ≃
      (Σo : Option (Fin c.length),Children depth (c.extend o)) :=
  (insertionSplitEquiv depth c).trans
    ((Equiv.sumCongr (childrenLeftEquiv depth c).symm
      (Equiv.sigmaCongrRight (fun i ↦ childrenMiddleEquiv depth E c i))).trans
      (outerChoiceSplitEquiv depth c).symm)

def successorExtendEquiv (depth : ℕ)
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1)) (n : ℕ) :
    (Σt : NestedPartition (depth+1) n,Insertion (depth+1) n t) ≃ NestedPartition (depth+1) (n+1) := by
  refine (Equiv.sigmaAssoc (fun (c : OrderedFinpartition n) (f : Children depth c) ↦
    Insertion (depth+1) n (⟨c,f⟩ : NestedPartition (depth+1) n))).trans ?_
  refine (Equiv.sigmaCongrRight (fun c ↦ childrenInsertionEquiv depth E c)).trans ?_
  exact (Equiv.sigmaAssoc (fun (c : OrderedFinpartition n) (o : Option (Fin c.length)) ↦
    Children depth (c.extend o))).symm.trans (Equiv.sigmaCongrLeft (OrderedFinpartition.extendEquiv n))

/-- Finite insertion equivalence, proved by induction on depth.
-/
def extendEquiv : (depth n : ℕ)→
    (Σt : NestedPartition depth n,Insertion depth n t) ≃ NestedPartition depth (n+1)
  | 0,_ => {
    toFun := fun _ ↦ PUnit.unit
    invFun := fun _ ↦ ⟨PUnit.unit,PUnit.unit⟩
    left_inv := by rintro ⟨t,o⟩; cases t; cases o; rfl
    right_inv := by intro t; cases t; rfl }
  | depth+1,n => successorExtendEquiv depth (fun m ↦ extendEquiv depth m) n

theorem extendEquiv_outer {depth n : ℕ} (t : NestedPartition (depth+1) n)
    (o : Insertion (depth+1) n t) :
    (extendEquiv (depth+1) n ⟨t,o⟩).1=t.1.extend (o.map (fun i ↦ i.1)) := by
  cases o with
  | none => rfl
  | some p => obtain ⟨i,o⟩ := p; rfl

end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartition
