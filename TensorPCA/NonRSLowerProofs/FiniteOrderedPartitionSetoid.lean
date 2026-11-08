-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-! Canonical ordered finite partitions representing finite equivalence
relations. The proofs use the existing fresh-zero insertion equivalence. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteOrderedPartitionSetoid
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sameBlock {n : ℕ} (c : OrderedFinpartition n) (i j : Fin n) : Prop :=
  c.index i=c.index j

theorem index_emb {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (a : Fin (c.partSize i)) : c.index (c.emb i a)=i :=
  congrArg Sigma.fst (c.equivSigma.symm_apply_apply ⟨i,a⟩)

theorem index_of_emb_eq {n : ℕ} (c : OrderedFinpartition n)
    (i : Fin c.length) (a : Fin (c.partSize i)) (j : Fin n) (h : c.emb i a=j) :
    c.index j=i := by rw [← h,index_emb]

theorem index_extendLeft_zero {n : ℕ} (c : OrderedFinpartition n) :
    c.extendLeft.index 0=(0 : Fin (c.length+1)) := by
  apply index_of_emb_eq c.extendLeft (0 : Fin (c.length+1)) (Fin.cast (by simp) (0 : Fin 1)) 0
  simp [OrderedFinpartition.extendLeft]

theorem index_extendLeft_succ {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    c.extendLeft.index j.succ=(c.index j).succ := by
  apply index_of_emb_eq c.extendLeft (c.index j).succ
    (Fin.cast (by simp) (c.invEmbedding j)) j.succ
  simp [OrderedFinpartition.extendLeft]

theorem index_extendMiddle_succ {n : ℕ} (c : OrderedFinpartition n)
    (k : Fin c.length) (j : Fin n) : (c.extendMiddle k).index j.succ=c.index j := by
  obtain ⟨⟨b,a⟩,rfl⟩ := c.equivSigma.surjective j
  change (c.extendMiddle k).index (c.emb b a).succ=c.index (c.emb b a)
  rw [index_emb]
  by_cases h : b=k
  · subst b
    apply index_of_emb_eq (c.extendMiddle k) k
      (Fin.cast (by simp) a.succ) (c.emb k a).succ
    simp [OrderedFinpartition.extendMiddle]
  · apply index_of_emb_eq (c.extendMiddle k) b
      (Fin.cast (by simp [h]) a) (c.emb b a).succ
    simp [OrderedFinpartition.extendMiddle,h]

theorem sameBlock_extendLeft_succ {n : ℕ} (c : OrderedFinpartition n) (i j : Fin n) :
    sameBlock c.extendLeft i.succ j.succ ↔ sameBlock c i j := by
  simp only [sameBlock,index_extendLeft_succ,Fin.succ_inj]

theorem sameBlock_extendLeft_zero_succ {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    ¬sameBlock c.extendLeft 0 j.succ := by
  simp only [sameBlock,index_extendLeft_zero,index_extendLeft_succ]
  exact (Fin.succ_ne_zero _).symm

theorem sameBlock_extendMiddle_succ {n : ℕ} (c : OrderedFinpartition n)
    (k : Fin c.length) (i j : Fin n) :
    sameBlock (c.extendMiddle k) i.succ j.succ ↔ sameBlock c i j := by
  simp only [sameBlock,index_extendMiddle_succ]

theorem sameBlock_extendMiddle_zero_succ {n : ℕ} (c : OrderedFinpartition n)
    (k : Fin c.length) (j : Fin n) :
    sameBlock (c.extendMiddle k) 0 j.succ ↔ k=c.index j := by
  simp only [sameBlock,OrderedFinpartition.index_extendMiddle_zero,index_extendMiddle_succ]

private theorem represents_of_succ_cases {n : ℕ} (d : OrderedFinpartition (n+1))
    (r : Setoid (Fin (n+1)))
    (hf : ∀j : Fin n,sameBlock d 0 j.succ ↔ r.r 0 j.succ)
    (ho : ∀i j : Fin n,sameBlock d i.succ j.succ ↔ r.r i.succ j.succ) :
    ∀i j : Fin (n+1),sameBlock d i j ↔ r.r i j := by
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ hf j) j
    exact iff_of_true rfl (r.refl 0)
  · refine Fin.cases ?_ (fun j ↦ ho i j) j
    constructor
    · intro h
      exact r.symm ((hf i).1 (by exact h.symm))
    · intro h
      exact ((hf i).2 (r.symm h)).symm

theorem exists_partition (n : ℕ) (r : Setoid (Fin n)) :
    ∃c : OrderedFinpartition n,∀i j : Fin n,sameBlock c i j ↔ r.r i j := by
  classical
  induction n with
  | zero =>
    refine ⟨default,?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    let rold : Setoid (Fin n) :=
      ⟨fun i j ↦ r.r i.succ j.succ,
        ⟨fun i ↦ r.refl i.succ,fun h ↦ r.symm h,fun h h' ↦ r.trans h h'⟩⟩
    obtain ⟨c,hc⟩ := ih rold
    by_cases H : ∃j : Fin n,r.r 0 j.succ
    · obtain ⟨j,hj⟩ := H
      refine ⟨c.extendMiddle (c.index j),represents_of_succ_cases _ r ?_ ?_⟩
      · intro b
        rw [sameBlock_extendMiddle_zero_succ]
        change sameBlock c j b ↔ r.r 0 b.succ
        rw [hc j b]
        change r.r j.succ b.succ ↔ r.r 0 b.succ
        exact ⟨fun h ↦ r.trans hj h,fun h ↦ r.trans (r.symm hj) h⟩
      · intro a b
        exact (sameBlock_extendMiddle_succ c (c.index j) a b).trans (hc a b)
    · refine ⟨c.extendLeft,represents_of_succ_cases _ r ?_ ?_⟩
      · intro b
        exact iff_of_false (sameBlock_extendLeft_zero_succ c b) (fun h ↦ H ⟨b,h⟩)
      · intro a b
        exact (sameBlock_extendLeft_succ c a b).trans (hc a b)

theorem sameBlock_extend_succ {n : ℕ} (c : OrderedFinpartition n)
    (o : Option (Fin c.length)) (i j : Fin n) :
    sameBlock (c.extend o) i.succ j.succ ↔ sameBlock c i j := by
  cases o with
  | none => exact sameBlock_extendLeft_succ c i j
  | some k => exact sameBlock_extendMiddle_succ c k i j

theorem sameBlock_extend_zero_succ {n : ℕ} (c : OrderedFinpartition n)
    (o : Option (Fin c.length)) (j : Fin n) :
    sameBlock (c.extend o) 0 j.succ ↔ o=some (c.index j) := by
  cases o with
  | none => exact iff_of_false (sameBlock_extendLeft_zero_succ c j) (by simp)
  | some k => simpa only [Option.some.injEq,OrderedFinpartition.extend] using sameBlock_extendMiddle_zero_succ c k j

private theorem insertion_eq_of_relations {n : ℕ} (c : OrderedFinpartition n)
    (o p : Option (Fin c.length))
    (h : ∀i j : Fin (n+1),sameBlock (c.extend o) i j ↔ sameBlock (c.extend p) i j) : o=p := by
  have hf (j : Fin n) : o=some (c.index j) ↔ p=some (c.index j) := by
    simpa only [sameBlock_extend_zero_succ] using h 0 j.succ
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some k =>
      have H := hf (c.emb k ⟨0,c.partSize_pos k⟩)
      rw [index_emb] at H
      have HF := H.mpr rfl
      cases HF
  | some k =>
    have H := hf (c.emb k ⟨0,c.partSize_pos k⟩)
    rw [index_emb] at H
    exact (H.mp rfl).symm

theorem eq_of_sameBlock (n : ℕ) (c d : OrderedFinpartition n)
    (h : ∀i j : Fin n,sameBlock c i j ↔ sameBlock d i j) : c=d := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    obtain ⟨⟨c,o⟩,rfl⟩ := (OrderedFinpartition.extendEquiv n).surjective c
    obtain ⟨⟨d,p⟩,rfl⟩ := (OrderedFinpartition.extendEquiv n).surjective d
    change c.extend o=d.extend p
    change ∀i j : Fin (n+1),sameBlock (c.extend o) i j ↔ sameBlock (d.extend p) i j at h
    have hcd : c=d := by
      apply ih
      intro i j
      exact (sameBlock_extend_succ c o i j).symm.trans
        ((h i.succ j.succ).trans (sameBlock_extend_succ d p i j))
    subst d
    rw [insertion_eq_of_relations c o p h]

theorem exists_unique_partition (n : ℕ) (r : Setoid (Fin n)) :
    ∃! c : OrderedFinpartition n,∀i j : Fin n,sameBlock c i j ↔ r.r i j := by
  obtain ⟨c,hc⟩ := exists_partition n r
  refine ⟨c,hc,?_⟩
  intro d hd
  exact eq_of_sameBlock n d c (fun i j ↦ (hd i j).trans (hc i j).symm)

def ofSetoid (n : ℕ) (r : Setoid (Fin n)) : OrderedFinpartition n :=
  (exists_partition n r).choose

theorem sameBlock_ofSetoid (n : ℕ) (r : Setoid (Fin n)) (i j : Fin n) :
    sameBlock (ofSetoid n r) i j ↔ r.r i j :=
  (exists_partition n r).choose_spec i j

theorem ofSetoid_unique (n : ℕ) (r : Setoid (Fin n)) (c : OrderedFinpartition n)
    (hc : ∀i j : Fin n,sameBlock c i j ↔ r.r i j) : c=ofSetoid n r :=
  eq_of_sameBlock n c _ (fun i j ↦ (hc i j).trans (sameBlock_ofSetoid n r i j).symm)


end
end TensorPCA.NonRSLowerProofs.FiniteOrderedPartitionSetoid
