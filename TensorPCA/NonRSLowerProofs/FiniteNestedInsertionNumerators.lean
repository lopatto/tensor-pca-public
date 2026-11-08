-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedDiscountedPartitionExtension

/-! Global finite nested insertion numerators. The eventual root denominator is
only the number of old replicas; terminal child weight one is handled without
cancelling a potentially zero singleton denominator. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedInsertionNumerators
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def numerator : (depth n : ℕ)→(x : Fin depth→ℝ)→(p : ℝ)→
    (t : NestedPartition depth n)→Insertion depth n t→ℝ
  | 0,n,_,p,_,_ => (n : ℝ)-p
  | depth+1,_,x,p,t,none => (t.1.length : ℝ)*x 0-p
  | depth+1,_,x,_,t,some ⟨i,o⟩ =>
      numerator depth (t.1.partSize i) (fun j ↦ x j.succ) (x 0) (t.2 i) o

theorem numerator_sum (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (t : NestedPartition depth n) :
    (∑o : Insertion depth n t,numerator depth n x p t o)=(n : ℝ)-p := by
  classical
  induction depth generalizing n p with
  | zero => simp [Insertion,numerator]
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    change (∑o : Option (Σi : Fin c.length,Insertion depth (c.partSize i) (f i)),
      numerator (depth+1) n x p ⟨c,f⟩ o)=(n : ℝ)-p
    rw [Fintype.sum_option]
    simp only [numerator]
    rw [Fintype.sum_sigma]
    simp_rw [ih]
    have hSizes : (∑i : Fin c.length,(c.partSize i : ℝ))=(n : ℝ) := by
      exact_mod_cast sum_partSize c
    rw [Finset.sum_sub_distrib,hSizes]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring

theorem numerator_nonneg (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hn : 0<n) (hp : 0≤p) (hp1 : p≤1) (hpx : ∀j,p≤x j)
    (hxm : Monotone x) (hx1 : ∀j,x j≤1)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    0 ≤ numerator depth n x p t o := by
  induction depth generalizing n p with
  | zero =>
    have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
    simp only [numerator]
    linarith
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    have hAlpha : 0≤x 0 := hp.trans (hpx 0)
    have hTail : ∀j : Fin depth,x 0≤x j.succ :=
      fun j ↦ hxm (by change (0 : ℕ)≤(j : ℕ)+1; omega)
    have hTailMono : Monotone (fun j : Fin depth ↦ x j.succ) := by
      intro i j hij
      exact hxm (by simpa only [Fin.succ_le_succ_iff] using hij)
    cases o with
    | none =>
      simp only [numerator]
      have hc1 : (1 : ℝ)≤c.length := by exact_mod_cast c.length_pos hn
      have H := mul_le_mul_of_nonneg_right hc1 hAlpha
      norm_num only [one_mul] at H
      linarith only [H,hpx 0]
    | some a =>
      obtain ⟨i,o⟩ := a
      exact ih (c.partSize i) (fun j ↦ x j.succ) (x 0) (c.partSize_pos i)
        hAlpha (hx1 0) hTail hTailMono (fun j ↦ hx1 j.succ) (f i) o

/-- The nonzero denominator is essential at terminal depth: terminal singleton
parent one has weight one, whereas its numerator and denominator both vanish. -/
theorem insertionWeight_eq_div (depth n : ℕ) (x : Fin depth→ℝ) (p : ℝ)
    (hp : 0≤p) (hpx : ∀j,p<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (hn : 0<n) (hden : (n : ℝ)-p≠0)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    insertionWeight depth n x p t o=numerator depth n x p t o/((n : ℝ)-p) := by
  induction depth generalizing n p with
  | zero => simp only [insertionWeight,numerator,div_self hden]
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
      simp only [insertionWeight,numerator,FiniteDiscountedPartitionLaw.insertionWeight,
        if_neg hn.ne']
    | some a =>
      obtain ⟨i,o⟩ := a
      cases depth with
      | zero =>
        simp only [insertionWeight,numerator,FiniteDiscountedPartitionLaw.insertionWeight,
          if_neg hn.ne',mul_one]
      | succ depth =>
        have hChildDen : (c.partSize i : ℝ)-x 0≠0 :=
          (FiniteDiscountedPartitionLaw.dimension_sub_pos (hTail 0)
            (hx1 (0 : Fin (depth+1)).succ) (c.partSize_pos i)).ne'
        simp only [insertionWeight,numerator]
        rw [ih (c.partSize i) (fun j ↦ x j.succ) (x 0) hAlpha hTail hTailMono
          (fun j ↦ hx1 j.succ) (c.partSize_pos i) hChildDen (f i) o]
        simp only [FiniteDiscountedPartitionLaw.insertionWeight,if_neg hn.ne']
        field_simp [hChildDen]

/-- At the physical root, only the full old replica count occurs below the
fraction bar. No inverse parent-height gap enters this exact transition. -/
theorem root_insertionWeight_eq_div (depth n : ℕ) (x : Fin depth→ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1) (hn : 0<n)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    insertionWeight depth n x 0 t o=numerator depth n x 0 t o/(n : ℝ) := by
  have hden : (n : ℝ)-0≠0 := by
    rw [sub_zero]
    exact_mod_cast hn.ne'
  simpa only [sub_zero] using
    insertionWeight_eq_div depth n x 0 (le_refl 0) hx hxm hx1 hn hden t o


end
end TensorPCA.NonRSLowerProofs.FiniteNestedInsertionNumerators
