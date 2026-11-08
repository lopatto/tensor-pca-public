-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedPartition

/-! Literal coalescence levels and overlap matrices of the existing finite
nested ordered partition. Depth zero means one common terminal mark. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedPartitionOverlap
open FiniteNestedPartition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def blockLevel {I : Type*} [DecidableEq I] (size : I→ℕ)
    (v : (b : I)→Fin (size b)→Fin (size b)→ℕ)
    (a b : Σi : I,Fin (size i)) : ℕ :=
  if h : a.1=b.1 then v a.1 a.2 (Fin.cast (congrArg size h.symm) b.2)+1 else 0

def coalescence : {depth n : ℕ}→NestedPartition depth n→Fin n→Fin n→ℕ
  | 0,_,_,_,_ => 0
  | depth+1,_,t,i,j => blockLevel t.1.partSize (fun b => coalescence (t.2 b))
      (t.1.equivSigma.symm i) (t.1.equivSigma.symm j)

theorem coalescence_zero {n : ℕ} (t : NestedPartition 0 n) (i j : Fin n) :
    coalescence t i j=0 := rfl

theorem coalescence_same {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (b : Fin c.length) (i j : Fin (c.partSize b)) :
    coalescence (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)
      (c.equivSigma ⟨b,i⟩) (c.equivSigma ⟨b,j⟩)=coalescence (f b) i j+1 := by
  simp only [coalescence,Equiv.symm_apply_apply]
  simp [blockLevel]

theorem coalescence_cross {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) {a b : Fin c.length} (hab : a≠b)
    (i : Fin (c.partSize a)) (j : Fin (c.partSize b)) :
    coalescence (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n)
      (c.equivSigma ⟨a,i⟩) (c.equivSigma ⟨b,j⟩)=0 := by
  simp [coalescence,blockLevel,hab]

theorem coalescence_le {depth n : ℕ} (t : NestedPartition depth n) (i j : Fin n) :
    coalescence t i j≤depth := by
  induction depth generalizing n with
  | zero => exact le_refl _
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
    by_cases h : a=b
    · subst b
      rw [coalescence_same]
      exact Nat.add_le_add_right (ih (f a) i j) 1
    · rw [coalescence_cross c f h]
      omega

theorem coalescence_self {depth n : ℕ} (t : NestedPartition depth n) (i : Fin n) :
    coalescence t i i=depth := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    rw [coalescence_same,ih]

theorem coalescence_symm {depth n : ℕ} (t : NestedPartition depth n) (i j : Fin n) :
    coalescence t i j=coalescence t j i := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    obtain ⟨⟨a,i⟩,rfl⟩ := c.equivSigma.surjective i
    obtain ⟨⟨b,j⟩,rfl⟩ := c.equivSigma.surjective j
    by_cases h : a=b
    · subst b
      rw [coalescence_same,coalescence_same,ih]
    · rw [coalescence_cross c f h,coalescence_cross c f (Ne.symm h)]

def level {depth n : ℕ} (t : NestedPartition depth n) (i j : Fin n) : Fin (depth+1) :=
  ⟨coalescence t i j,Nat.lt_succ_of_le (coalescence_le t i j)⟩

def overlap {depth n : ℕ} (t : NestedPartition depth n) (q : Fin (depth+1)→ℝ) :
    Fin n→Fin n→ℝ := fun i j => q (level t i j)

theorem overlap_zero {n : ℕ} (t : NestedPartition 0 n) (q : Fin 1→ℝ) (i j : Fin n) :
    overlap t q i j=q 0 := rfl

theorem overlap_self {depth n : ℕ} (t : NestedPartition depth n)
    (q : Fin (depth+1)→ℝ) (i : Fin n) : overlap t q i i=q (Fin.last depth) := by
  apply congrArg q
  exact Fin.ext (coalescence_self t i)

theorem overlap_symm {depth n : ℕ} (t : NestedPartition depth n)
    (q : Fin (depth+1)→ℝ) (i j : Fin n) : overlap t q i j=overlap t q j i := by
  apply congrArg q
  exact Fin.ext (coalescence_symm t i j)

theorem overlap_same {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (q : Fin (depth+2)→ℝ)
    (b : Fin c.length) (i j : Fin (c.partSize b)) :
    overlap (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) q
      (c.equivSigma ⟨b,i⟩) (c.equivSigma ⟨b,j⟩)=
      overlap (f b) (fun l => q l.succ) i j := by
  apply congrArg q
  exact Fin.ext (coalescence_same c f b i j)

theorem overlap_cross {depth n : ℕ} (c : OrderedFinpartition n)
    (f : Children depth c) (q : Fin (depth+2)→ℝ)
    {a b : Fin c.length} (hab : a≠b) (i : Fin (c.partSize a)) (j : Fin (c.partSize b)) :
    overlap (depth := depth+1) (⟨c,f⟩ : NestedPartition (depth+1) n) q
      (c.equivSigma ⟨a,i⟩) (c.equivSigma ⟨b,j⟩)=q 0 := by
  apply congrArg q
  exact Fin.ext (coalescence_cross c f hab i j)

theorem overlap_mem {depth n : ℕ} (t : NestedPartition depth n)
    {q : Fin (depth+1)→ℝ} (hq : Monotone q) (i j : Fin n) :
    overlap t q i j∈Set.Icc (q 0) (q (Fin.last depth)) :=
  ⟨hq (Fin.zero_le _),hq (Fin.le_last _)⟩

end
end TensorPCA.NonRSLowerProofs.FiniteNestedPartitionOverlap
