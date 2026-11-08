-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartition
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionLaw
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Literal finite nested discounted partition masses. Every internal factor
is the authoritative one-level EPPF; terminal depth is deterministic. No
independent sampler or physical hierarchy identification is introduced. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionLaw
open FiniteNestedPartition FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def mass : (depth n : ℕ)→(Fin depth→ℝ)→ℝ→NestedPartition depth n→ℝ
  | 0,_,_,_,_ => 1
  | depth+1,_,x,p,t => eppf (x 0) p t.1*
      ∏i : Fin t.1.length,mass depth (t.1.partSize i) (fun j ↦ x j.succ) (x 0) (t.2 i)

def insertionWeight : (depth n : ℕ)→(x : Fin depth→ℝ)→(p : ℝ)→
    (t : NestedPartition depth n)→Insertion depth n t→ℝ
  | 0,_,_,_,_,_ => 1
  | depth+1,_,x,p,t,none => FiniteDiscountedPartitionLaw.insertionWeight (x 0) p t.1 none
  | depth+1,_,x,p,t,some ⟨i,o⟩ =>
      FiniteDiscountedPartitionLaw.insertionWeight (x 0) p t.1 (some i)*
        insertionWeight depth (t.1.partSize i) (fun j ↦ x j.succ) (x 0) (t.2 i) o

theorem mass_nonneg (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) : 0≤mass depth n x p t := by
  induction depth generalizing n p with
  | zero => simp only [mass]; norm_num
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    have hAlpha : 0≤x 0 := hp.trans (hpx 0).le
    have hTail : ∀j : Fin depth,x 0<x j.succ := fun j ↦ hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    apply mul_nonneg (eppf_nonneg hp (hpx 0) (hx1 0) c)
    exact Finset.prod_nonneg (fun i _ ↦ ih (c.partSize i) (fun j ↦ x j.succ) (x 0)
      hAlpha hTail hTailMono (fun j ↦ hx1 j.succ) (f i))

theorem mass_sum (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) :
    (∑t : NestedPartition depth n,mass depth n x p t)=1 := by
  classical
  induction depth generalizing n p with
  | zero => simp [NestedPartition,mass]
  | succ depth ih =>
    have hAlpha : 0≤x 0 := hp.trans (hpx 0).le
    have hTail : ∀j : Fin depth,x 0<x j.succ := fun j ↦ hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    change (∑t : (Σc : OrderedFinpartition n,Children depth c),
      eppf (x 0) p t.1*∏i : Fin t.1.length,mass depth (t.1.partSize i) (fun j ↦ x j.succ) (x 0) (t.2 i))=1
    rw [Fintype.sum_sigma]
    have hInner (c : OrderedFinpartition n) :
        (∑f : Children depth c,∏i : Fin c.length,mass depth (c.partSize i) (fun j ↦ x j.succ) (x 0) (f i))=1 := by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro i _
      exact ih (c.partSize i) (fun j ↦ x j.succ) (x 0) hAlpha hTail hTailMono (fun j ↦ hx1 j.succ)
    simp_rw [← Finset.mul_sum,hInner,mul_one]
    exact FiniteDiscountedPartitionLaw.eppf_sum hp (hpx 0) (hx1 0) n

theorem mass_zero (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth 0) : mass depth 0 x p t=1 := by
  have H := mass_sum depth 0 x p hp hpx hxm hx1
  simp only [Finset.univ_unique,Finset.sum_singleton] at H
  have ht : t=default := Subsingleton.elim _ _
  simpa only [ht] using H

theorem mass_one (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth 1) : mass depth 1 x p t=1 := by
  have H := mass_sum depth 1 x p hp hpx hxm hx1
  simp only [Finset.univ_unique,Finset.sum_singleton] at H
  have ht : t=default := Subsingleton.elim _ _
  simpa only [ht] using H

theorem insertionWeight_nonneg (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t) : 0 ≤ insertionWeight depth n x p t o := by
  induction depth generalizing n p with
  | zero => simp only [insertionWeight]; norm_num
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    have hAlpha : 0≤x 0 := hp.trans (hpx 0).le
    have hTail : ∀j : Fin depth,x 0<x j.succ := fun j ↦ hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    cases o with
    | none => exact FiniteDiscountedPartitionLaw.insertionWeight_nonneg hp (hpx 0) (hx1 0) c none
    | some a =>
      obtain ⟨i,o⟩ := a
      exact mul_nonneg (FiniteDiscountedPartitionLaw.insertionWeight_nonneg hp (hpx 0) (hx1 0) c (some i))
        (ih (c.partSize i) (fun j ↦ x j.succ) (x 0) hAlpha hTail hTailMono (fun j ↦ hx1 j.succ) (f i) o)

theorem insertionWeight_sum (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) : (∑o : Insertion depth n t,insertionWeight depth n x p t o)=1 := by
  classical
  induction depth generalizing n p with
  | zero => simp [Insertion,insertionWeight]
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    have hAlpha : 0≤x 0 := hp.trans (hpx 0).le
    have hTail : ∀j : Fin depth,x 0<x j.succ := fun j ↦ hxm (by change (0 : ℕ)<(j : ℕ)+1; omega)
    have hTailMono : StrictMono (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_lt_succ_iff] using hij)
    change (∑o : Option (Σi : Fin c.length,Insertion depth (c.partSize i) (f i)),
      insertionWeight (depth+1) n x p ⟨c,f⟩ o)=1
    rw [Fintype.sum_option]
    simp only [insertionWeight]
    rw [Fintype.sum_sigma]
    have hInner (i : Fin c.length) :
        (∑o : Insertion depth (c.partSize i) (f i),insertionWeight depth (c.partSize i)
          (fun j ↦ x j.succ) (x 0) (f i) o)=1 :=
      ih (c.partSize i) (fun j ↦ x j.succ) (x 0) hAlpha hTail hTailMono (fun j ↦ hx1 j.succ) (f i)
    simp_rw [← Finset.mul_sum,hInner,mul_one]
    have H := FiniteDiscountedPartitionLaw.insertionWeight_sum hp (hpx 0) (hx1 0) c
    simpa only [Fintype.sum_option] using H

def partitionPMF (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) :
    PMF (NestedPartition depth n) :=
  PMF.ofFintype (fun t ↦ ENNReal.ofReal (mass depth n x p t)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ ↦ mass_nonneg depth n x p hp hpx hxm hx1 t),
      mass_sum depth n x p hp hpx hxm hx1]
    exact ENNReal.ofReal_one)

theorem partitionPMF_apply (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) :
    partitionPMF depth n x p hp hpx hxm hx1 t=ENNReal.ofReal (mass depth n x p t) := rfl

def insertionPMF (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) : PMF (Insertion depth n t) :=
  PMF.ofFintype (fun o ↦ ENNReal.ofReal (insertionWeight depth n x p t o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ ↦ insertionWeight_nonneg depth n x p hp hpx hxm hx1 t o),
      insertionWeight_sum depth n x p hp hpx hxm hx1 t]
    exact ENNReal.ofReal_one)

theorem insertionPMF_apply (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    insertionPMF depth n x p hp hpx hxm hx1 t o=ENNReal.ofReal (insertionWeight depth n x p t o) := rfl

theorem partitionPMF_zero (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth 0) : partitionPMF depth 0 x p hp hpx hxm hx1 t=1 := by
  rw [partitionPMF_apply,mass_zero depth x p hp hpx hxm hx1,ENNReal.ofReal_one]

theorem partitionPMF_one (depth : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth 1) : partitionPMF depth 1 x p hp hpx hxm hx1 t=1 := by
  rw [partitionPMF_apply,mass_one depth x p hp hpx hxm hx1,ENNReal.ofReal_one]

end
end TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionLaw
