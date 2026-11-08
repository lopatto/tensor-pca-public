-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecisionTrial

/-! Exact finite-depth weighted-moment cancellation at the Gaussian precision root.
Every boundary atom, including the terminal atom, is retained.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthMoment
open FiniteCSGaussianDepthPrecision FiniteCSGaussianDepthAtomicLaw
open FiniteCSGaussianPushforwardAlgebra
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def increments {d : ℕ} (y : Fin (d+1)→ℝ) (j : Fin d) : ℝ := y j.succ-y j.castSucc

theorem weighted_array_sum_by_parts {d : ℕ} (x : Fin d→ℝ) (a : Fin (d+1)→ℝ) :
    (∑i : Fin (d+1),atomWeight x i*a i)=a (Fin.last d)-
      ∑j : Fin d,x j*(a j.succ-a j.castSucc) := by
  simpa only [id_eq] using weighted_sum_by_parts x a id

theorem sum_adjacent_sub {d : ℕ} (a : Fin (d+1)→ℝ) :
    (∑j : Fin d,(a j.succ-a j.castSucc))=a (Fin.last d)-a 0 := by
  have h0 := Fin.sum_univ_succ a
  have hd := Fin.sum_univ_castSucc a
  rw [Finset.sum_sub_distrib]
  linarith only [h0,hd]

theorem precision_weighted_moment {d : ℕ} (x : Fin d→ℝ) (y : Fin (d+1)→ℝ) {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ increments y j)
    (hB : tail (fun j => x j*increments y j) 0< B)
    (hroot : y 0/(precision x (increments y) B 0)^2+
      (∑j : Fin d,increments y j/(precision x (increments y) B j*precision x (increments y) B ((j : ℕ)+1)))=1-1/B) :
    (∑i : Fin (d+1),atomWeight x i*node x (increments y) (y 0) B i*y i)=y (Fin.last d)-B+1 := by
  let r : Fin (d+1)→ℝ := fun i => node x (increments y) (y 0) B i
  let D : Fin (d+1)→ℝ := fun i => precision x (increments y) B i
  have hP (i : Fin (d+1)) : 0< D i := precision_pos hx hDelta hB i
  have hBpos : 0< B := (tail_nonneg (fun j => mul_nonneg (hx j).le (hDelta j)) 0).trans_lt hB
  have hstep (j : Fin d) : x j*(r j.succ*y j.succ-r j.castSucc*y j.castSucc)=
      (r j.succ*D j.succ-y j.succ/D j.succ)-(r j.castSucc*D j.castSucc-y j.castSucc/D j.castSucc) := by
    have hp : D j.succ-D j.castSucc=x j*(y j.succ-y j.castSucc) := precision_succ x (increments y) B j
    have hn : r j.succ-r j.castSucc=(y j.succ-y j.castSucc)/(D j.castSucc*D j.succ) := node_succ x (increments y) (y 0) B j
    have H := weighted_increment_telescope (hP j.castSucc).ne' (hP j.succ).ne' hp hn
    linarith only [H]
  have hsum : (∑j : Fin d,x j*(r j.succ*y j.succ-r j.castSucc*y j.castSucc))=
      (r (Fin.last d)*D (Fin.last d)-y (Fin.last d)/D (Fin.last d))-(r 0*D 0-y 0/D 0) := by
    calc
      _=∑j : Fin d,((r j.succ*D j.succ-y j.succ/D j.succ)-(r j.castSucc*D j.castSucc-y j.castSucc/D j.castSucc)) :=
        Finset.sum_congr rfl (fun j _ => hstep j)
      _=_ := sum_adjacent_sub (fun i => r i*D i-y i/D i)
  have hhead : r 0*D 0=y 0/D 0 := by
    dsimp only [r,D,node]
    rw [Fin.val_zero,prefix_zero,add_zero]
    field_simp [(hP 0).ne']
  have hlast : r (Fin.last d)=1-1/B := node_end_eq hroot
  have hDlast : D (Fin.last d)=B := precision_end _ _ _
  have H := weighted_array_sum_by_parts x (fun i => r i*y i)
  rw [hsum,hhead,hlast,hDlast] at H
  change (∑i : Fin (d+1),atomWeight x i*r i*y i)=_
  have heq : (∑i : Fin (d+1),atomWeight x i*r i*y i)=∑i : Fin (d+1),atomWeight x i*(r i*y i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq,H]
  field_simp [hBpos.ne']
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthMoment
