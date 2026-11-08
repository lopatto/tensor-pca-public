-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianBMinimization

/-! All finite depths of the Gaussian precision minimum and its constructive
pushed nodes. Indices of masses/increments are Fin d; endpoint nodes are
ordinary natural indices bounded by d. No hierarchy or CS minimum is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecision
open FiniteCSGaussianBMinimization
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The finite prefixSum, with the endpoint i=d allowed. -/
def prefixSum {d : ℕ} (f : Fin d→ℝ) (i : ℕ) : ℝ := ∑j : Fin d,if (j : ℕ)< i then f j else 0

/-- The finite tail, including the empty terminal tail i=d. -/
def tail {d : ℕ} (f : Fin d→ℝ) (i : ℕ) : ℝ := ∑j : Fin d,if i≤(j : ℕ) then f j else 0

theorem prefix_zero {d : ℕ} (f : Fin d→ℝ) : prefixSum f 0=0 := by simp [prefixSum]
theorem tail_zero {d : ℕ} (f : Fin d→ℝ) : tail f 0=∑j,f j := by simp [tail]
theorem prefix_end {d : ℕ} (f : Fin d→ℝ) : prefixSum f d=∑j,f j := by simp [prefixSum]
theorem tail_end {d : ℕ} (f : Fin d→ℝ) : tail f d=0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp only [show ¬d≤(j : ℕ) by omega,ite_false]

theorem prefix_add_tail {d : ℕ} (f : Fin d→ℝ) (i : ℕ) : prefixSum f i+tail f i=∑j,f j := by
  rw [prefixSum,tail,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : (j : ℕ)< i
  · simp only [h,show ¬i≤(j : ℕ) by omega,ite_true,ite_false,add_zero]
  · simp only [h,show i≤(j : ℕ) by omega,ite_true,ite_false,zero_add]

theorem prefix_succ {d : ℕ} (f : Fin d→ℝ) {i : ℕ} (hi : i< d) :
    prefixSum f (i+1)=prefixSum f i+f ⟨i,hi⟩ := by
  have hsingle : (∑j : Fin d,if (j : ℕ)=i then f j else 0)=f ⟨i,hi⟩ := by
    rw [Finset.sum_eq_single ⟨i,hi⟩]
    · simp only [ite_true]
    · intro j _ hj
      have hjv : (j : ℕ)≠i := by intro h; apply hj; exact Fin.ext h
      simp only [hjv,ite_false]
    · simp
  calc
    _=∑j : Fin d,((if (j : ℕ)< i then f j else 0)+(if (j : ℕ)=i then f j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hlt : (j : ℕ)< i
      · simp only [hlt,show (j : ℕ)< i+1 by omega,show ¬(j : ℕ)=i by omega,ite_true,ite_false,add_zero]
      · by_cases heq : (j : ℕ)=i
        · simp [heq]
        · simp only [hlt,heq,show ¬(j : ℕ)< i+1 by omega,ite_false,add_zero]
    _=_ := by rw [Finset.sum_add_distrib,hsingle]; rfl

theorem tail_succ {d : ℕ} (f : Fin d→ℝ) {i : ℕ} (hi : i< d) :
    tail f i=f ⟨i,hi⟩+tail f (i+1) := by
  have h0 := prefix_add_tail f i
  have h1 := prefix_add_tail f (i+1)
  rw [prefix_succ f hi] at h1
  linarith only [h0,h1]

theorem tail_nonneg {d : ℕ} {f : Fin d→ℝ} (hf : ∀j,0≤f j) (i : ℕ) : 0≤tail f i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hf j
  · exact le_rfl

theorem tail_le_zero {d : ℕ} {f : Fin d→ℝ} (hf : ∀j,0≤f j) (i : ℕ) : tail f i≤tail f 0 := by
  rw [tail_zero]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact hf j

/-- The scalar cost specialized from the proved arbitrary finite-index precision
minimum.
-/
def depthCost {d : ℕ} (x Delta : Fin d→ℝ) (y0 B : ℝ) : ℝ :=
  cost (tail (fun j => x j*Delta j) 0) y0 (fun j => 1/x j)
    (fun j => tail (fun l => x l*Delta l) j)
    (fun j => tail (fun l => x l*Delta l) ((j : ℕ)+1)) B

/-- Precision at every endpoint index. -/
def precision {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) (i : ℕ) : ℝ :=
  B-tail (fun j => x j*Delta j) i

theorem depthCost_eq {d : ℕ} (x Delta : Fin d→ℝ) (y0 B : ℝ) :
    depthCost x Delta y0 B=B-1-Real.log B+y0/precision x Delta B 0+
      ∑j : Fin d,(Real.log (precision x Delta B ((j : ℕ)+1))-Real.log (precision x Delta B j))/x j := by
  unfold depthCost cost precision
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem precision_pos {d : ℕ} {x Delta : Fin d→ℝ} (hx : ∀j,0< x j) (hDelta : ∀j,0≤Delta j)
    {B : ℝ} (hB : tail (fun j => x j*Delta j) 0< B) (i : ℕ) : 0< precision x Delta B i := by
  have H := tail_le_zero (fun j => mul_nonneg (hx j).le (hDelta j)) i
  unfold precision
  linarith only [H,hB]

theorem precision_end {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) : precision x Delta B d=B := by
  rw [precision,tail_end,sub_zero]

theorem precision_succ {d : ℕ} (x Delta : Fin d→ℝ) (B : ℝ) (i : Fin d) :
    precision x Delta B ((i : ℕ)+1)-precision x Delta B i=x i*Delta i := by
  have H := tail_succ (fun j => x j*Delta j) i.isLt
  simpa only [precision] using (show (B-tail (fun j => x j*Delta j) ((i : ℕ)+1))-
    (B-tail (fun j => x j*Delta j) i)=x i*Delta i by linarith only [H])

theorem exists_depth_minimizing_root {d : ℕ} (x Delta : Fin d→ℝ) {y0 : ℝ}
    (hx : ∀j,0< x j) (hDelta : ∀j,0≤Delta j) (hy : 0< y0) :
    ∃B : ℝ,tail (fun j => x j*Delta j) 0< B ∧
      y0/(precision x Delta B 0)^2+
        (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B ∧
      ∀C : ℝ,tail (fun j => x j*Delta j) 0< C→depthCost x Delta y0 B≤depthCost x Delta y0 C := by
  have hnonneg (j : Fin d) : 0≤x j*Delta j := mul_nonneg (hx j).le (hDelta j)
  have hst (j : Fin d) : tail (fun l => x l*Delta l) ((j : ℕ)+1)≤tail (fun l => x l*Delta l) j ∧
      tail (fun l => x l*Delta l) j≤tail (fun l => x l*Delta l) 0 := by
    refine ⟨?_,tail_le_zero hnonneg _⟩
    have H := tail_succ (fun l => x l*Delta l) j.isLt
    linarith only [H,hnonneg j]
  obtain ⟨B,hB,hroot,hmin⟩ := exists_minimizing_root (fun j => 1/x j)
    (fun j => tail (fun l => x l*Delta l) j) (fun j => tail (fun l => x l*Delta l) ((j : ℕ)+1))
    (tail_nonneg hnonneg 0) hy (fun j => one_div_nonneg.mpr (hx j).le) hst
  refine ⟨B,hB,?_,hmin⟩
  have hs : (∑j : Fin d,(1/x j)*(tail (fun l => x l*Delta l) j-tail (fun l => x l*Delta l) ((j : ℕ)+1))/
      (precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=
      ∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) := by
    apply Finset.sum_congr rfl
    intro j _
    have H := tail_succ (fun l => x l*Delta l) j.isLt
    have he : (1/x j)*(tail (fun l => x l*Delta l) j-tail (fun l => x l*Delta l) ((j : ℕ)+1))=Delta j := by
      rw [H]
      field_simp [(hx j).ne']
      ring
    rw [he]
  change 1-1/B-y0/(precision x Delta B 0)^2-
    (∑j : Fin d,(1/x j)*(tail (fun l => x l*Delta l) j-tail (fun l => x l*Delta l) ((j : ℕ)+1))/
      (precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=0 at hroot
  rw [hs] at hroot
  linarith only [hroot]

theorem prefix_nonneg {d : ℕ} {f : Fin d→ℝ} (hf : ∀j,0≤f j) (i : ℕ) : 0≤prefixSum f i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hf j
  · exact le_rfl

theorem prefix_mono {d : ℕ} {f : Fin d→ℝ} (hf : ∀j,0≤f j) {i l : ℕ} (hil : i≤l) :
    prefixSum f i≤prefixSum f l := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : (j : ℕ)< i
  · simp only [hj,show (j : ℕ)< l by omega,ite_true,le_refl]
  · by_cases hjl : (j : ℕ)< l
    · simp only [hj,hjl,ite_false,ite_true,hf j]
    · simp only [hj,hjl,ite_false,le_refl]

theorem prefix_differences {d : ℕ} (f : ℕ→ℝ) :
    ∀i : ℕ,i≤d→prefixSum (fun j : Fin d => f j-f ((j : ℕ)+1)) i=f 0-f i := by
  intro i
  induction i with
  | zero => intro _; rw [prefix_zero,sub_self]
  | succ i ih =>
    intro hi
    have hid : i< d := by omega
    rw [prefix_succ _ hid,ih (by omega)]
    dsimp only
    ring

theorem tail_differences {d : ℕ} (f : ℕ→ℝ) {i : ℕ} (hi : i≤d) :
    tail (fun j : Fin d => f j-f ((j : ℕ)+1)) i=f i-f d := by
  have h0 := prefix_differences f i hi
  have hd := prefix_differences f d le_rfl
  have H := prefix_add_tail (fun j : Fin d => f j-f ((j : ℕ)+1)) i
  rw [prefix_end] at hd
  linarith only [h0,hd,H]

/-- The pushed node at each of the d+1 endpoints. -/
def node {d : ℕ} (x Delta : Fin d→ℝ) (y0 B : ℝ) (i : ℕ) : ℝ :=
  y0/(precision x Delta B 0)^2+
    prefixSum (fun j => Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1))) i

theorem node_succ {d : ℕ} (x Delta : Fin d→ℝ) (y0 B : ℝ) (j : Fin d) :
    node x Delta y0 B ((j : ℕ)+1)-node x Delta y0 B j=
      Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) := by
  unfold node
  rw [prefix_succ _ j.isLt]
  ring

theorem node_mono {d : ℕ} {x Delta : Fin d→ℝ} (y0 : ℝ) {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j) (hB : tail (fun j => x j*Delta j) 0<B)
    {i l : ℕ} (hil : i≤l) : node x Delta y0 B i≤node x Delta y0 B l := by
  have hP := precision_pos hx hDelta hB
  unfold node
  apply add_le_add le_rfl
  exact prefix_mono (fun j => div_nonneg (hDelta j) (mul_nonneg (hP j).le (hP ((j : ℕ)+1)).le)) hil

theorem node_end_eq {d : ℕ} {x Delta : Fin d→ℝ} {y0 B : ℝ}
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B) :
    node x Delta y0 B d=1-1/B := by
  simpa only [node,prefix_end] using hroot

theorem nodes_pos_le_end_lt_one {d : ℕ} {x Delta : Fin d→ℝ} {y0 B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j) (hy : 0<y0)
    (hB : tail (fun j => x j*Delta j) 0<B)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    {i : ℕ} (hi : i≤d) :
    0<node x Delta y0 B i ∧ node x Delta y0 B i≤node x Delta y0 B d ∧ node x Delta y0 B d<1 := by
  have hP := precision_pos hx hDelta hB
  have hf (j : Fin d) : 0≤Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)) :=
    div_nonneg (hDelta j) (mul_nonneg (hP j).le (hP ((j : ℕ)+1)).le)
  have h0 : 0<y0/(precision x Delta B 0)^2 := div_pos hy (sq_pos_of_pos (hP 0))
  have hp := prefix_nonneg hf i
  have hle := prefix_mono hf hi
  have hBp : 0<B := (tail_nonneg (fun j => mul_nonneg (hx j).le (hDelta j)) 0).trans_lt hB
  refine ⟨by unfold node; linarith only [h0,hp],?_,?_⟩
  · unfold node
    exact add_le_add le_rfl hle
  · rw [node_end_eq hroot]
    linarith only [one_div_pos.mpr hBp]

theorem weighted_node_succ {d : ℕ} {x Delta : Fin d→ℝ} (y0 : ℝ) {B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j) (hB : tail (fun j => x j*Delta j) 0<B) (j : Fin d) :
    x j*(node x Delta y0 B ((j : ℕ)+1)-node x Delta y0 B j)=
      1/precision x Delta B j-1/precision x Delta B ((j : ℕ)+1) := by
  have hj := precision_pos hx hDelta hB j
  have hj1 := precision_pos hx hDelta hB ((j : ℕ)+1)
  have H := precision_succ x Delta B j
  rw [node_succ]
  field_simp [hj.ne',hj1.ne']
  linarith only [H]

theorem node_tail_precision_identity {d : ℕ} {x Delta : Fin d→ℝ} {y0 B : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j) (hB : tail (fun j => x j*Delta j) 0<B)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    {i : ℕ} (hi : i≤d) :
    1-node x Delta y0 B d+
      tail (fun j => x j*(node x Delta y0 B ((j : ℕ)+1)-node x Delta y0 B j)) i=
      1/precision x Delta B i := by
  have ht : tail (fun j => x j*(node x Delta y0 B ((j : ℕ)+1)-node x Delta y0 B j)) i=
      tail (fun j : Fin d => 1/precision x Delta B j-1/precision x Delta B ((j : ℕ)+1)) i := by
    unfold tail
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [weighted_node_succ y0 hx hDelta hB j]
  rw [ht,tail_differences (fun l => 1/precision x Delta B l) hi,precision_end,node_end_eq hroot]
  ring

theorem exists_depth_minimizing_root_nodes {d : ℕ} (x Delta : Fin d→ℝ) {y0 : ℝ}
    (hx : ∀j,0<x j) (hDelta : ∀j,0≤Delta j) (hy : 0<y0) :
    ∃B : ℝ,tail (fun j => x j*Delta j) 0<B ∧
      node x Delta y0 B d=1-1/B ∧
      (∀i : ℕ,i≤d→0<node x Delta y0 B i ∧ node x Delta y0 B i≤node x Delta y0 B d ∧ node x Delta y0 B d<1) ∧
      (∀i : ℕ,i≤d→1-node x Delta y0 B d+
        tail (fun j => x j*(node x Delta y0 B ((j : ℕ)+1)-node x Delta y0 B j)) i=1/precision x Delta B i) ∧
      ∀C : ℝ,tail (fun j => x j*Delta j) 0<C→depthCost x Delta y0 B≤depthCost x Delta y0 C := by
  obtain ⟨B,hB,hroot,hmin⟩ := exists_depth_minimizing_root x Delta hx hDelta hy
  exact ⟨B,hB,node_end_eq hroot,fun _ hi => nodes_pos_le_end_lt_one hx hDelta hy hB hroot hi,
    fun _ hi => node_tail_precision_identity hx hDelta hB hroot hi,hmin⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecision
