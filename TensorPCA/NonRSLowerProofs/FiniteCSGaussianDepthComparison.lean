-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthMoment
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomComparison

/-! Exact finite-depth Gaussian cost minus the constructed CS value. The
original overlap chain ends at one, and every terminal atom is retained. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthComparison
open Set FiniteCSGaussianDepthPrecision FiniteCSGaussianDepthMoment FiniteCSGaussianDepthAtomicLaw
open FiniteCSGaussianThreeAtomComparison
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def gaussianCost {d : ℕ} (x : Fin d→ℝ) (q : Fin (d+1)→ℝ) (f : ℝ→ℝ) (y : Fin (d+1)→ℝ) (B : ℝ) : ℝ :=
  depthCost x (increments y) (y 0) B-
    ∑j : Fin d,x j*((q j.succ*y j.succ-f (q j.succ))-(q j.castSucc*y j.castSucc-f (q j.castSucc)))

theorem gaussian_sub_cs_eq_weighted_bregman {d : ℕ} (f : ℝ→ℝ)
    (x : Fin d→ℝ) (q y : Fin (d+1)→ℝ) {B : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤ increments y j) (hqend : q (Fin.last d)=1)
    (hB : tail (fun j => x j*increments y j) 0< B)
    (hroot : y 0/(precision x (increments y) B 0)^2+
      (∑j : Fin d,increments y j/(precision x (increments y) B j*precision x (increments y) B ((j : ℕ)+1)))=1-1/B) :
    gaussianCost x q f y B-
      (f 1-(∑i : Fin (d+1),atomWeight x i*f (node x (increments y) (y 0) B i))+
        y 0/precision x (increments y) B 0+
        (∑j : Fin d,Real.log (precision x (increments y) B ((j : ℕ)+1)/precision x (increments y) B j)/x j)-Real.log B)=
      ∑i : Fin (d+1),atomWeight x i*(f (node x (increments y) (y 0) B i)-f (q i)-
        y i*(node x (increments y) (y 0) B i-q i)) := by
  let r : Fin (d+1)→ℝ := fun i => node x (increments y) (y 0) B i
  have hP := precision_pos hx hDelta hB
  have hlogs : (∑j : Fin d,(Real.log (precision x (increments y) B ((j : ℕ)+1))-
      Real.log (precision x (increments y) B j))/x j)=
      ∑j : Fin d,Real.log (precision x (increments y) B ((j : ℕ)+1)/precision x (increments y) B j)/x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.log_div (hP ((j : ℕ)+1)).ne' (hP j).ne']
  have hmoment := precision_weighted_moment x y hx hDelta hB hroot
  change (∑i : Fin (d+1),atomWeight x i*r i*y i)=y (Fin.last d)-B+1 at hmoment
  have htheta := weighted_array_sum_by_parts x (fun i => q i*y i-f (q i))
  rw [hqend,one_mul] at htheta
  have hreg : (∑i : Fin (d+1),atomWeight x i*(f (r i)-f (q i)-y i*(r i-q i)))=
      (∑i : Fin (d+1),atomWeight x i*f (r i))+
      (∑i : Fin (d+1),atomWeight x i*(q i*y i-f (q i)))-
      (∑i : Fin (d+1),atomWeight x i*r i*y i) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change gaussianCost x q f y B-
      (f 1-(∑i : Fin (d+1),atomWeight x i*f (r i))+y 0/precision x (increments y) B 0+
        (∑j : Fin d,Real.log (precision x (increments y) B ((j : ℕ)+1)/precision x (increments y) B j)/x j)-Real.log B)=_
  rw [gaussianCost,depthCost_eq,hlogs,hreg]
  linear_combination -htheta+hmoment

theorem gaussian_cs_comparison {d : ℕ} (f : ℝ→ℝ) (hf : ConvexOn ℝ (Ici 0) f)
    (x : Fin d→ℝ) (q y : Fin (d+1)→ℝ) {B : ℝ}
    (hx : ∀j,0< x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hDelta : ∀j,0≤ increments y j)
    (hy : 0< y 0) (hq : ∀i,0≤ q i) (hqend : q (Fin.last d)=1) (hd : ∀i,HasDerivAt f (y i) (q i))
    (hB : tail (fun j => x j*increments y j) 0< B)
    (hroot : y 0/(precision x (increments y) B 0)^2+
      (∑j : Fin d,increments y j/(precision x (increments y) B j*precision x (increments y) B ((j : ℕ)+1)))=1-1/B) :
    f 1-(∑i : Fin (d+1),atomWeight x i*f (node x (increments y) (y 0) B i))+
      y 0/precision x (increments y) B 0+
      (∑j : Fin d,Real.log (precision x (increments y) B ((j : ℕ)+1)/precision x (increments y) B j)/x j)-Real.log B≤
      gaussianCost x q f y B := by
  have H := gaussian_sub_cs_eq_weighted_bregman f x q y hx hDelta hqend hB hroot
  have hsum : 0≤∑i : Fin (d+1),atomWeight x i*(f (node x (increments y) (y 0) B i)-f (q i)-
      y i*(node x (increments y) (y 0) B i-q i)) := by
    apply Finset.sum_nonneg
    intro i _
    have hr : 0≤ node x (increments y) (y 0) B i :=
      (nodes_pos_le_end_lt_one hx hDelta hy hB hroot (i := (i : ℕ)) (by omega)).1.le
    exact mul_nonneg (atomWeight_nonneg (fun j => (hx j).le) hx1 hxm i) (convex_bregman_nonneg hf hr (hq i) (hd i))
  linarith only [H,hsum]

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthComparison
