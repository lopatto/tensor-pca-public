-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedInsertionNumerators

/-! Height stability of the global insertion numerators. Constants involve only finite
depth and replica count; no inverse height gap is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedInsertionStability
open FiniteNestedPartition FiniteNestedInsertionNumerators FiniteNestedDiscountedPartitionLaw
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem numerator_sub_abs_le (depth n : ℕ) (x y : Fin depth→ℝ) (p q eps : ℝ)
    (heps : 0≤eps) (hpq : |p-q|≤eps) (hxy : ∀j,|x j-y j|≤eps)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    |numerator depth n x p t o-numerator depth n y q t o|≤((n : ℝ)+1)*eps := by
  induction depth generalizing n p q with
  | zero =>
    simp only [numerator]
    have H : |((n : ℝ)-p)-((n : ℝ)-q)|=|p-q| := by
      rw [show ((n : ℝ)-p)-((n : ℝ)-q)=-(p-q) by ring,abs_neg]
    rw [H]
    exact hpq.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    cases o with
    | none =>
      simp only [numerator]
      have H : ((c.length : ℝ)*x 0-p)-((c.length : ℝ)*y 0-q)=
          (c.length : ℝ)*(x 0-y 0)-(p-q) := by ring
      rw [H]
      calc
        |(c.length : ℝ)*(x 0-y 0)-(p-q)|≤
            |(c.length : ℝ)*(x 0-y 0)|+|p-q| := abs_sub _ _
        _=(c.length : ℝ)*|x 0-y 0|+|p-q| := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg c.length)]
        _≤(c.length : ℝ)*eps+eps := add_le_add
          (mul_le_mul_of_nonneg_left (hxy 0) (Nat.cast_nonneg c.length)) hpq
        _≤((n : ℝ)+1)*eps := by
          have Hc : (c.length : ℝ)≤n := by exact_mod_cast c.length_le
          nlinarith
    | some a =>
      obtain ⟨i,o⟩ := a
      have H := ih (c.partSize i) (fun j ↦ x j.succ) (fun j ↦ y j.succ)
        (x 0) (y 0) (hxy 0) (fun j ↦ hxy j.succ) (f i) o
      exact H.trans (by
        have Hi : (c.partSize i : ℝ)≤n := by exact_mod_cast c.partSize_le i
        nlinarith)

theorem insertion_card_le (depth n : ℕ) (t : NestedPartition depth n) :
    Fintype.card (Insertion depth n t)≤n*depth+1 := by
  classical
  induction depth generalizing n with
  | zero => simp [Insertion]
  | succ depth ih =>
    rcases t with ⟨c,f⟩
    change Fintype.card (Option (Σi : Fin c.length,Insertion depth (c.partSize i) (f i)))≤_
    rw [Fintype.card_option,Fintype.card_sigma]
    calc
      (∑i : Fin c.length,Fintype.card (Insertion depth (c.partSize i) (f i)))+1≤
          (∑i : Fin c.length,(c.partSize i*depth+1))+1 := by
        exact Nat.add_le_add_right (Finset.sum_le_sum (fun i _ ↦ ih (c.partSize i) (f i))) 1
      _=n*depth+c.length+1 := by
        rw [Finset.sum_add_distrib,← Finset.sum_mul,
          FiniteDiscountedPartitionProofs.sum_partSize]
        simp
      _≤n*(depth+1)+1 := by
        have H := c.length_le
        nlinarith

theorem root_row_l1_le (depth n : ℕ) (x y : Fin depth→ℝ) (eps : ℝ)
    (heps : 0≤eps) (hxy : ∀j,|x j-y j|≤eps) (hn : 0<n)
    (t : NestedPartition depth n) :
    (∑o : Insertion depth n t,
      |numerator depth n x 0 t o/(n : ℝ)-numerator depth n y 0 t o/(n : ℝ)|)≤
      ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ)) := by
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  have hBound : 0≤((n : ℝ)+1)*eps/(n : ℝ) := by positivity
  calc
    (∑o : Insertion depth n t,
        |numerator depth n x 0 t o/(n : ℝ)-numerator depth n y 0 t o/(n : ℝ)|)≤
        ∑_o : Insertion depth n t,(((n : ℝ)+1)*eps/(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro o _
      rw [← sub_div,abs_div,abs_of_pos hnR]
      apply div_le_div_of_nonneg_right _ hnR.le
      exact numerator_sub_abs_le depth n x y 0 0 eps heps (by simpa using heps) hxy t o
    _=(Fintype.card (Insertion depth n t) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ)) := by
      simp
    _≤((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hBound
      exact_mod_cast insertion_card_le depth n t

/-- A strict-height row can be compared directly with weak-height coefficients; these
coefficients do not define a second sampler.
-/
theorem strict_row_l1_le (depth n : ℕ) (x y : Fin depth→ℝ) (eps : ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (heps : 0≤eps) (hxy : ∀j,|x j-y j|≤eps) (hn : 0<n)
    (t : NestedPartition depth n) :
    (∑o : Insertion depth n t,
      |insertionWeight depth n x 0 t o-numerator depth n y 0 t o/(n : ℝ)|)≤
      ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ)) := by
  simp_rw [root_insertionWeight_eq_div depth n x hx hxm hx1 hn]
  exact root_row_l1_le depth n x y eps heps hxy hn t


end
end TensorPCA.NonRSLowerProofs.FiniteNestedInsertionStability
