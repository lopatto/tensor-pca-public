-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthAtomicEntropy

/-! Bind the arbitrary-depth atomic CS law to the proved Gaussian precision root.
Integrated-CDF identities are discharged by the constructive finite reciprocal
telescope; no profile or entropy identity is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecisionTrial
open MeasureTheory ProbabilityTheory Set
open FiniteCS RetainedCountProofs.CrisantiSommers
open FiniteCSGaussianDepthPrecision FiniteCSGaussianDepthAtomicLaw FiniteCSGaussianDepthAtomicEntropy
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem precision_atomicLaw_xHat {d : ℕ} {x Delta : Fin d→ℝ} {y0 B : ℝ}
    (hx : ∀j,0<x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hDelta : ∀j,0≤Delta j)
    (hB : tail (fun j => x j*Delta j) 0<B)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (i : Fin (d+1)) :
    xHat (atomicLaw x (fun j : Fin (d+1) => node x Delta y0 B j)) (node x Delta y0 B i)=
      1/precision x Delta B i := by
  have hrm : Monotone (fun j : Fin (d+1) => node x Delta y0 B j) :=
    fun j l hjl => node_mono y0 hx hDelta hB hjl
  rw [xHat_atomicLaw_at_node (fun j => (hx j).le) hx1 hxm hrm i]
  have H := node_tail_precision_identity hx hDelta hB hroot (i := (i : ℕ)) (by omega)
  simpa only [Fin.val_last,Fin.val_castSucc,Fin.val_succ] using H

theorem functional_precision_atomicLaw_eval {d : ℕ} {x Delta : Fin d→ℝ} {y0 B : ℝ}
    (hx : ∀j,0<x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hDelta : ∀j,0≤Delta j) (hy : 0<y0)
    (hB : tail (fun j => x j*Delta j) 0<B)
    (hroot : y0/(precision x Delta B 0)^2+
      (∑j : Fin d,Delta j/(precision x Delta B j*precision x Delta B ((j : ℕ)+1)))=1-1/B)
    (beta : ℝ) (xi : ℝ→ℝ) :
    2*functional beta xi (atomicLaw x (fun i : Fin (d+1) => node x Delta y0 B i)) (node x Delta y0 B d)=
      beta^2*(xi 1-∑i : Fin (d+1),atomWeight x i*xi (node x Delta y0 B i))+
      y0/precision x Delta B 0+
      (∑j : Fin d,Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j)-Real.log B := by
  have hr0 : 0≤node x Delta y0 B 0 := (nodes_pos_le_end_lt_one hx hDelta hy hB hroot (i := 0) (Nat.zero_le _)).1.le
  have hrm : Monotone (fun j : Fin (d+1) => node x Delta y0 B j) :=
    fun j l hjl => node_mono y0 hx hDelta hB hjl
  have hr1 := (nodes_pos_le_end_lt_one hx hDelta hy hB hroot (i := d) le_rfl).2.2
  have hD (i : Fin (d+1)) : 0<precision x Delta B i := precision_pos hx hDelta hB i
  have hh := precision_atomicLaw_xHat hx hx1 hxm hDelta hB hroot
  have H := functional_atomicLaw_eval hx hx1 hxm hr0 hrm hr1 hD hh beta xi
  simp only [Fin.val_zero,Fin.val_last,Fin.val_castSucc,Fin.val_succ] at H
  have hhead : node x Delta y0 B 0*precision x Delta B 0=y0/precision x Delta B 0 := by
    unfold node
    rw [prefix_zero,add_zero]
    field_simp [(precision_pos hx hDelta hB 0).ne']
  rw [hhead,precision_end] at H
  exact H

/-- Every finite positive-height Gaussian precision minimum constructs a
standard CS trial, with its complete ordinary functional value proved. -/
theorem exists_minimizing_precision_atomicTrial {d : ℕ} (x Delta : Fin d→ℝ) {y0 : ℝ}
    (hx : ∀j,0<x j) (hx1 : ∀j,x j≤1) (hxm : Monotone x) (hDelta : ∀j,0≤Delta j) (hy : 0<y0) :
    ∃(B : ℝ) (nu : Trial),tail (fun j => x j*Delta j) 0<B ∧
      realLaw nu=atomicLaw x (fun i : Fin (d+1) => node x Delta y0 B i) ∧
      node x Delta y0 B d=1-1/B ∧
      (∀C : ℝ,tail (fun j => x j*Delta j) 0<C→depthCost x Delta y0 B≤depthCost x Delta y0 C) ∧
      ∀(beta : ℝ) (xi : ℝ→ℝ),
        2*functional beta xi (realLaw nu) (node x Delta y0 B d)=
          beta^2*(xi 1-∑i : Fin (d+1),atomWeight x i*xi (node x Delta y0 B i))+
          y0/precision x Delta B 0+
          (∑j : Fin d,Real.log (precision x Delta B ((j : ℕ)+1)/precision x Delta B j)/x j)-Real.log B := by
  obtain ⟨B,hB,hroot,hmin⟩ := exists_depth_minimizing_root x Delta hx hDelta hy
  have hr0 : 0≤node x Delta y0 B 0 := (nodes_pos_le_end_lt_one hx hDelta hy hB hroot (i := 0) (Nat.zero_le _)).1.le
  have hrm : Monotone (fun j : Fin (d+1) => node x Delta y0 B j) :=
    fun j l hjl => node_mono y0 hx hDelta hB hjl
  have hr1 := (nodes_pos_le_end_lt_one hx hDelta hy hB hroot (i := d) le_rfl).2.2
  let nu := atomicTrial x (fun i : Fin (d+1) => node x Delta y0 B i) (fun j => (hx j).le) hx1 hxm hr0 hrm hr1
  have hlaw : realLaw nu=atomicLaw x (fun i : Fin (d+1) => node x Delta y0 B i) := realLaw_atomicTrial _ _ _ _ _ _ _ _
  refine ⟨B,nu,hB,hlaw,node_end_eq hroot,hmin,?_⟩
  intro beta xi
  rw [hlaw]
  exact functional_precision_atomicLaw_eval hx hx1 hxm hDelta hy hB hroot beta xi

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthPrecisionTrial
