-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedInsertionStability

/-! Comparison of a finite PMF family with the exact strict-height nested law. Weak-
height numbers appear only in an explicitly measured recurrence residual; no weak-
height sampler is introduced.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedLawComparison
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw
open FiniteNestedDiscountedPartitionExtension FiniteNestedInsertionNumerators
open FiniteNestedInsertionStability
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def l1Distance {A : Type*} [Fintype A] (P Q : PMF A) : ℝ :=
  ∑t : A,|(P t).toReal-(Q t).toReal|

def recurrenceResidual (depth n : ℕ) (y : Fin depth→ℝ)
    (P : PMF (NestedPartition depth n)) (Pnext : PMF (NestedPartition depth (n+1))) : ℝ :=
  ∑t : NestedPartition depth n,∑o : Insertion depth n t,
    |(Pnext ((extendEquiv depth n) ⟨t,o⟩)).toReal-
      (P t).toReal*(numerator depth n y 0 t o/(n : ℝ))|

private theorem pmf_real_sum {A : Type*} [Fintype A] (P : PMF A) :
    (∑t : A,(P t).toReal)=1 := by
  rw [← ENNReal.toReal_sum (fun t _ ↦ P.apply_ne_top t)]
  have H : (∑t : A,P t)=1 := by simpa only [tsum_fintype] using P.tsum_coe
  rw [H,ENNReal.toReal_one]

private theorem scalar_step_abs_le (a b p q u w : ℝ) (hp : 0≤p) (hw : 0≤w)
    (hb : b=q*w) :
    |a-b|≤|a-p*u|+p*|u-w|+|p-q| *w := by
  rw [hb]
  have H : a-q*w=(a-p*u)+p*(u-w)+(p-q)*w := by ring
  rw [H]
  calc
    |(a-p*u)+p*(u-w)+(p-q)*w|≤|(a-p*u)+p*(u-w)|+|(p-q)*w| := abs_add_le _ _
    _≤|a-p*u|+|p*(u-w)|+|(p-q)*w| := by linarith only [abs_add_le (a-p*u) (p*(u-w))]
    _=|a-p*u|+p*|u-w|+|p-q| *w := by rw [abs_mul,abs_of_nonneg hp,abs_mul,abs_of_nonneg hw]

private theorem sum_extensions (depth n : ℕ) (F : NestedPartition depth (n+1)→ℝ) :
    (∑u : NestedPartition depth (n+1),F u)=
      ∑t : NestedPartition depth n,∑o : Insertion depth n t,F ((extendEquiv depth n) ⟨t,o⟩) := by
  rw [← Fintype.sum_equiv (extendEquiv depth n)
    (fun s ↦ F ((extendEquiv depth n) s)) F (fun _ ↦ rfl)]
  rw [Fintype.sum_sigma]

theorem l1Distance_step_le (depth n : ℕ) (x y : Fin depth→ℝ) (eps : ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (heps : 0≤eps) (hxy : ∀j,|x j-y j|≤eps) (hn : 0<n)
    (P : PMF (NestedPartition depth n)) (Pnext : PMF (NestedPartition depth (n+1))) :
    l1Distance Pnext (partitionPMF depth (n+1) x 0 (le_refl 0) hx hxm hx1)≤
      recurrenceResidual depth n y P Pnext+
      ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ))+
      l1Distance P (partitionPMF depth n x 0 (le_refl 0) hx hxm hx1) := by
  classical
  let Q := partitionPMF depth n x 0 (le_refl 0) hx hxm hx1
  let Qnext := partitionPMF depth (n+1) x 0 (le_refl 0) hx hxm hx1
  let w := fun (t : NestedPartition depth n) (o : Insertion depth n t) ↦
    insertionWeight depth n x 0 t o
  let u := fun (t : NestedPartition depth n) (o : Insertion depth n t) ↦
    numerator depth n y 0 t o/(n : ℝ)
  let S := ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ))
  have hw (t : NestedPartition depth n) (o : Insertion depth n t) : 0≤w t o :=
    insertionWeight_nonneg depth n x 0 (le_refl 0) hx hxm hx1 t o
  have hwSum (t : NestedPartition depth n) : (∑o : Insertion depth n t,w t o)=1 :=
    insertionWeight_sum depth n x 0 (le_refl 0) hx hxm hx1 t
  have hQ (t : NestedPartition depth n) (o : Insertion depth n t) :
      (Qnext ((extendEquiv depth n) ⟨t,o⟩)).toReal=(Q t).toReal*w t o := by
    dsimp only [Qnext,Q,w]
    rw [partitionPMF_extend,ENNReal.toReal_mul,insertionPMF_apply,
      ENNReal.toReal_ofReal (insertionWeight_nonneg depth n x 0 (le_refl 0) hx hxm hx1 t o)]
  have hRow (t : NestedPartition depth n) : (∑o : Insertion depth n t,|u t o-w t o|)≤S := by
    simp only [u,w,abs_sub_comm]
    exact strict_row_l1_le depth n x y eps hx hxm hx1 heps hxy hn t
  have hMiddle : (∑t : NestedPartition depth n,∑o : Insertion depth n t,
      (P t).toReal*|u t o-w t o|)≤S := by
    simp_rw [← Finset.mul_sum]
    calc
      (∑t : NestedPartition depth n,(P t).toReal*(∑o : Insertion depth n t,|u t o-w t o|))≤
          ∑t : NestedPartition depth n,(P t).toReal*S := by
        exact Finset.sum_le_sum (fun t _ ↦ mul_le_mul_of_nonneg_left (hRow t) ENNReal.toReal_nonneg)
      _=S := by rw [← Finset.sum_mul,pmf_real_sum,one_mul]
  have hOld : (∑t : NestedPartition depth n,∑o : Insertion depth n t,
      |(P t).toReal-(Q t).toReal| * w t o)=l1Distance P Q := by
    simp_rw [← Finset.mul_sum,hwSum,mul_one]
    rfl
  change l1Distance Pnext Qnext≤recurrenceResidual depth n y P Pnext+S+l1Distance P Q
  rw [l1Distance,sum_extensions]
  calc
    (∑t : NestedPartition depth n,∑o : Insertion depth n t,
      |(Pnext ((extendEquiv depth n) ⟨t,o⟩)).toReal-
        (Qnext ((extendEquiv depth n) ⟨t,o⟩)).toReal|)≤
        ∑t : NestedPartition depth n,∑o : Insertion depth n t,
          (|(Pnext ((extendEquiv depth n) ⟨t,o⟩)).toReal-(P t).toReal*u t o|+
            (P t).toReal*|u t o-w t o|+|(P t).toReal-(Q t).toReal| * w t o) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro o _
      exact scalar_step_abs_le _ _ _ _ _ _ ENNReal.toReal_nonneg (hw t o) (hQ t o)
    _=recurrenceResidual depth n y P Pnext+
        (∑t : NestedPartition depth n,∑o : Insertion depth n t,(P t).toReal*|u t o-w t o|)+
        l1Distance P Q := by
      simp_rw [Finset.sum_add_distrib]
      rw [← hOld]
      rfl
    _≤recurrenceResidual depth n y P Pnext+S+l1Distance P Q :=
      by linarith only [hMiddle]

private theorem l1Distance_eq_zero_of_unique {A : Type*} [Fintype A] [Unique A]
    (P Q : PMF A) : l1Distance P Q=0 := by
  have hP := pmf_real_sum P
  have hQ := pmf_real_sum Q
  simp only [Finset.univ_unique,Finset.sum_singleton] at hP hQ
  simp only [l1Distance,Finset.univ_unique,Finset.sum_singleton,hP,hQ,sub_self,abs_zero]

/-- Propagate family error from the deterministic singleton law. The finite recurrence
residual is an explicit input to the estimate.
-/
theorem l1Distance_family_le (depth N : ℕ) (x y : Fin depth→ℝ) (eps : ℝ)
    (hx : ∀j,0<x j) (hxm : StrictMono x) (hx1 : ∀j,x j≤1)
    (heps : 0≤eps) (hxy : ∀j,|x j-y j|≤eps)
    (P : (n : ℕ)→PMF (NestedPartition depth n)) (hN : 0<N) :
    l1Distance (P N) (partitionPMF depth N x 0 (le_refl 0) hx hxm hx1)≤
      ∑n ∈ Finset.Ico 1 N,
        (recurrenceResidual depth n y (P n) (P (n+1))+
          ((n*depth+1 : ℕ) : ℝ)*(((n : ℝ)+1)*eps/(n : ℝ))) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N=0
    · subst N
      have H := l1Distance_eq_zero_of_unique (P 1)
        (partitionPMF depth 1 x 0 (le_refl 0) hx hxm hx1)
      simpa only [Finset.Ico_self,Finset.sum_empty] using H.le
    · have hNpos : 0<N := Nat.pos_of_ne_zero hN0
      have H := l1Distance_step_le depth N x y eps hx hxm hx1 heps hxy hNpos (P N) (P (N+1))
      have HI := ih hNpos
      rw [Finset.sum_Ico_succ_top hNpos]
      linarith only [H,HI]

theorem bounded_test_difference_le_l1 {A : Type*} [Fintype A] (P Q : PMF A)
    (H : A→ℝ) (C : ℝ) (hC : 0≤C) (hH : ∀t,|H t|≤C) :
    |(∑t : A,(P t).toReal*H t)-(∑t : A,(Q t).toReal*H t)|≤C*l1Distance P Q := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑t : A,((P t).toReal*H t-(Q t).toReal*H t)|≤
        ∑t : A,|(P t).toReal*H t-(Q t).toReal*H t| :=
      Finset.abs_sum_le_sum_abs _ _
    _=∑t : A,(|(P t).toReal-(Q t).toReal| * |H t|) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [show (P t).toReal*H t-(Q t).toReal*H t=
        ((P t).toReal-(Q t).toReal)*H t by ring,abs_mul]
    _≤∑t : A,(|(P t).toReal-(Q t).toReal| * C) :=
      Finset.sum_le_sum (fun t _ ↦ mul_le_mul_of_nonneg_left (hH t) (abs_nonneg _))
    _=C*l1Distance P Q := by rw [← Finset.sum_mul,mul_comm]; rfl


end
end TensorPCA.NonRSLowerProofs.FiniteNestedLawComparison
