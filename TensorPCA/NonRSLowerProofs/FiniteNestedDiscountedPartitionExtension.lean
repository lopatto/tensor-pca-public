-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionLaw

/-! Exact product extension for the literal nested discounted mass. The
proof multiplies factors and never divides by EPPF or block factors, which
may vanish at the terminal height one. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionExtension
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem extendEquiv_none {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c) :
    extendEquiv (depth+1) n ⟨⟨c,f⟩,none⟩=
      ⟨c.extendLeft,(childrenLeftEquiv depth c).symm f⟩ := rfl

theorem extendEquiv_some {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (i : Fin c.length) (o : Insertion depth (c.partSize i) (f i)) :
    extendEquiv (depth+1) n ⟨⟨c,f⟩,some ⟨i,o⟩⟩=
      ⟨c.extendMiddle i,(childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c i) ⟨f,o⟩⟩ := rfl

theorem childrenLeft_product {depth n : ℕ} (c : OrderedFinpartition n) (f : Children depth c)
    (v : (m : ℕ)→NestedPartition depth m→ℝ) :
    (∏j : Fin c.extendLeft.length,v (c.extendLeft.partSize j) ((childrenLeftEquiv depth c).symm f j))=
      v 1 default*∏j : Fin c.length,v (c.partSize j) (f j) := by
  change (∏j : Fin (c.length+1),v (Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize j)
    (Fin.cons (α := fun j : Fin (c.length+1) ↦
      NestedPartition depth (Fin.cons (α := fun _ ↦ ℕ) 1 c.partSize j))
      (default : NestedPartition depth 1) f j))=_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rfl

theorem childrenMiddle_same_heq {depth n : ℕ}
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1))
    (c : OrderedFinpartition n) (f : Children depth c) (i : Fin c.length)
    (o : Insertion depth (c.partSize i) (f i)) :
    HEq ((childrenMiddleEquiv depth E c i) ⟨f,o⟩ i) ((E (c.partSize i)) ⟨f i,o⟩) := by
  simp [childrenMiddleEquiv,childrenMiddleSplitEquiv,
    FiniteNestedPartitionTwoLevel.piSelectedSigmaEquiv,Equiv.piSplitAt,
    Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft,← Equiv.cast_symm]

theorem childrenMiddle_ne_heq {depth n : ℕ}
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1))
    (c : OrderedFinpartition n) (f : Children depth c) (i j : Fin c.length)
    (o : Insertion depth (c.partSize i) (f i)) (hji : j≠i) :
    HEq ((childrenMiddleEquiv depth E c i) ⟨f,o⟩ j) (f j) := by
  simp [childrenMiddleEquiv,childrenMiddleSplitEquiv,
    FiniteNestedPartitionTwoLevel.piSelectedSigmaEquiv,Equiv.piSplitAt,
    Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft,← Equiv.cast_symm,hji,hji.symm]

private theorem value_heq {depth a b : ℕ}
    (v : (m : ℕ)→NestedPartition depth m→ℝ)
    {ta : NestedPartition depth a} {tb : NestedPartition depth b}
    (hab : a=b) (h : HEq ta tb) : v a ta=v b tb := by
  cases hab
  cases eq_of_heq h
  rfl

theorem childrenMiddle_product {depth n : ℕ}
    (E : ∀m,(Σt : NestedPartition depth m,Insertion depth m t) ≃ NestedPartition depth (m+1))
    (c : OrderedFinpartition n) (f : Children depth c) (i : Fin c.length)
    (o : Insertion depth (c.partSize i) (f i))
    (v : (m : ℕ)→NestedPartition depth m→ℝ) :
    (∏j : Fin (c.extendMiddle i).length,
      v ((c.extendMiddle i).partSize j) ((childrenMiddleEquiv depth E c i) ⟨f,o⟩ j))=
      v (c.partSize i+1) ((E (c.partSize i)) ⟨f i,o⟩)*
        ∏j ∈ Finset.univ.erase i,v (c.partSize j) (f j) := by
  classical
  have hU : (fun j : Fin c.length ↦
      v ((c.extendMiddle i).partSize j) ((childrenMiddleEquiv depth E c i) ⟨f,o⟩ j))=
      Function.update (fun j : Fin c.length ↦ v (c.partSize j) (f j)) i
        (v (c.partSize i+1) ((E (c.partSize i)) ⟨f i,o⟩)) := by
    funext j
    by_cases hji : j=i
    · subst j
      rw [Function.update_self]
      exact value_heq v (by simp [OrderedFinpartition.extendMiddle_partSize])
        (childrenMiddle_same_heq E c f i o)
    · rw [Function.update_of_ne hji]
      exact value_heq v (by simp [OrderedFinpartition.extendMiddle_partSize,hji])
        (childrenMiddle_ne_heq E c f i j o hji)
  change (∏j : Fin c.length,
    v ((c.extendMiddle i).partSize j) ((childrenMiddleEquiv depth E c i) ⟨f,o⟩ j))=_
  rw [hU,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]

theorem mass_extend (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    mass depth (n+1) x p ((extendEquiv depth n) ⟨t,o⟩)=
      mass depth n x p t*insertionWeight depth n x p t o := by
  classical
  induction depth generalizing n p with
  | zero => simp only [mass,insertionWeight]; norm_num
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    have hAlpha : 0≤x 0 := hp.trans (hpx 0).le
    have hTail : ∀j : Fin depth,x 0<x j.succ :=
      fun j ↦ hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    cases o with
    | none =>
      rw [extendEquiv_none]
      change eppf (x 0) p c.extendLeft*
        (∏j : Fin c.extendLeft.length,mass depth (c.extendLeft.partSize j)
          (fun l ↦ x l.succ) (x 0) ((childrenLeftEquiv depth c).symm f j))=
        (eppf (x 0) p c*∏j : Fin c.length,
          mass depth (c.partSize j) (fun l ↦ x l.succ) (x 0) (f j))*
          FiniteDiscountedPartitionLaw.insertionWeight (x 0) p c none
      rw [childrenLeft_product c f (fun m t ↦ mass depth m (fun l ↦ x l.succ) (x 0) t),mass_one depth (fun l ↦ x l.succ) (x 0)
        hAlpha hTail hTailMono (fun l ↦ hx1 l.succ)]
      have H := FiniteDiscountedPartitionLaw.eppf_extend hp (hpx 0) (hx1 0) c none
      simp only [OrderedFinpartition.extend] at H
      rw [H]
      ring
    | some a =>
      obtain ⟨i,o⟩ := a
      rw [extendEquiv_some]
      change eppf (x 0) p (c.extendMiddle i)*
        (∏j : Fin (c.extendMiddle i).length,mass depth ((c.extendMiddle i).partSize j)
          (fun l ↦ x l.succ) (x 0)
          ((childrenMiddleEquiv depth (fun m ↦ extendEquiv depth m) c i) ⟨f,o⟩ j))=
        (eppf (x 0) p c*∏j : Fin c.length,
          mass depth (c.partSize j) (fun l ↦ x l.succ) (x 0) (f j))*
          (FiniteDiscountedPartitionLaw.insertionWeight (x 0) p c (some i)*
            insertionWeight depth (c.partSize i) (fun l ↦ x l.succ) (x 0) (f i) o)
      rw [childrenMiddle_product (fun m ↦ extendEquiv depth m) c f i o
        (fun m t ↦ mass depth m (fun l ↦ x l.succ) (x 0) t),ih (c.partSize i) (fun l ↦ x l.succ) (x 0)
        hAlpha hTail hTailMono (fun l ↦ hx1 l.succ) (f i) o]
      have H := FiniteDiscountedPartitionLaw.eppf_extend hp (hpx 0) (hx1 0) c (some i)
      simp only [OrderedFinpartition.extend] at H
      rw [H]
      have Hprod := Finset.mul_prod_erase Finset.univ
        (fun j : Fin c.length ↦ mass depth (c.partSize j) (fun l ↦ x l.succ) (x 0) (f j))
        (Finset.mem_univ i)
      rw [← Hprod]
      ring

theorem partitionPMF_extend (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    partitionPMF depth (n+1) x p hp hpx hxm hx1 ((extendEquiv depth n) ⟨t,o⟩)=
      partitionPMF depth n x p hp hpx hxm hx1 t*
        insertionPMF depth n x p hp hpx hxm hx1 t o := by
  rw [partitionPMF_apply,partitionPMF_apply,insertionPMF_apply,
    mass_extend depth n x p hp hpx hxm hx1 t o,
    ENNReal.ofReal_mul (mass_nonneg depth n x p hp hpx hxm hx1 t)]

theorem exists_unique_extension (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) :
    ∃! q : PMF (NestedPartition depth (n+1)),
      ∀t : NestedPartition depth n,∀o : Insertion depth n t,
      q ((extendEquiv depth n) ⟨t,o⟩)=
        partitionPMF depth n x p hp hpx hxm hx1 t*
          insertionPMF depth n x p hp hpx hxm hx1 t o := by
  refine ⟨partitionPMF depth (n+1) x p hp hpx hxm hx1,?_,?_⟩
  · exact partitionPMF_extend depth n x p hp hpx hxm hx1
  · intro q hq
    ext u
    obtain ⟨s,hs⟩ := (extendEquiv depth n).surjective u
    rw [← hs,hq]
    exact (partitionPMF_extend depth n x p hp hpx hxm hx1 s.1 s.2).symm


end
end TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionExtension
