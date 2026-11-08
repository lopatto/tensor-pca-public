-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Linarith

/-! The literal finite discounted partition coefficients on Mathlib's
canonical ordered partitions. Product recurrences include the alpha=1
endpoint without dividing by a possibly zero block weight. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionProofs
open Set
open scoped BigOperators
noncomputable section

def clusterFactor (alpha p : ℝ) (b : ℕ) : ℝ := ∏j∈Finset.Ico 1 b,((j : ℝ)*alpha-p)
def blockFactor (alpha : ℝ) (s : ℕ) : ℝ := ∏j∈Finset.Ico 1 s,((j : ℝ)-alpha)
def normalizer (p : ℝ) (n : ℕ) : ℝ := ∏j∈Finset.Ico 1 n,((j : ℝ)-p)

def eppf (alpha p : ℝ) {n : ℕ} (c : OrderedFinpartition n) : ℝ :=
  clusterFactor alpha p c.length*(∏i : Fin c.length,blockFactor alpha (c.partSize i))/normalizer p n

theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) : (∑i : Fin c.length,c.partSize i)=n := by
  have H := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_sigma,Fintype.card_fin] using H

theorem sum_extensions (n : ℕ) (F : OrderedFinpartition (n+1)→ℝ) :
    (∑d : OrderedFinpartition (n+1),F d)=
      ∑c : OrderedFinpartition n,(F c.extendLeft+∑i : Fin c.length,F (c.extendMiddle i)) := by
  rw [← Fintype.sum_equiv (OrderedFinpartition.extendEquiv n)
    (fun s => F ((OrderedFinpartition.extendEquiv n) s)) F (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp [Fintype.sum_option,OrderedFinpartition.extendEquiv_apply,OrderedFinpartition.extend]

theorem clusterFactor_succ (alpha p : ℝ) (b : ℕ) (hb : 1≤b) :
    clusterFactor alpha p (b+1)=clusterFactor alpha p b*((b : ℝ)*alpha-p) := by
  exact Finset.prod_Ico_succ_top hb _

theorem blockFactor_succ (alpha : ℝ) (s : ℕ) (hs : 1≤s) :
    blockFactor alpha (s+1)=blockFactor alpha s*((s : ℝ)-alpha) := by
  exact Finset.prod_Ico_succ_top hs _

theorem normalizer_succ (p : ℝ) (n : ℕ) (hn : 1≤n) :
    normalizer p (n+1)=normalizer p n*((n : ℝ)-p) := by
  exact Finset.prod_Ico_succ_top hn _

theorem clusterFactor_pos {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (b : ℕ) :
    0<clusterFactor alpha p b := by
  apply Finset.prod_pos
  intro j hj
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  have ha : 0<alpha := hp.trans_lt hpa
  have H := mul_le_mul_of_nonneg_right hj1 ha.le
  norm_num only [one_mul] at H
  linarith only [H,hpa]

theorem blockFactor_nonneg {alpha : ℝ} (ha : alpha≤1) (s : ℕ) : 0≤blockFactor alpha s := by
  apply Finset.prod_nonneg
  intro j hj
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  linarith only [hj1,ha]

theorem blockFactor_pos {alpha : ℝ} (ha : alpha<1) (s : ℕ) : 0<blockFactor alpha s := by
  apply Finset.prod_pos
  intro j hj
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  linarith only [hj1,ha]

theorem normalizer_pos {p : ℝ} (hp : p<1) (n : ℕ) : 0<normalizer p n := by
  apply Finset.prod_pos
  intro j hj
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  linarith only [hj1,hp]

theorem eppf_nonneg {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) : 0≤eppf alpha p c := by
  exact div_nonneg (mul_nonneg (clusterFactor_pos hp hpa _).le
    (Finset.prod_nonneg (fun _ _ => blockFactor_nonneg ha _)))
    (normalizer_pos (hpa.trans_le ha) n).le

theorem eppf_pos {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha<1)
    {n : ℕ} (c : OrderedFinpartition n) : 0<eppf alpha p c := by
  exact div_pos (mul_pos (clusterFactor_pos hp hpa _)
    (Finset.prod_pos (fun _ _ => blockFactor_pos ha _))) (normalizer_pos (hpa.trans ha) n)

theorem eppf_zero (alpha p : ℝ) (c : OrderedFinpartition 0) : eppf alpha p c=1 := by
  have h : c=OrderedFinpartition.atomic 0 := Subsingleton.elim _ _
  rw [h]
  norm_num [eppf,clusterFactor,blockFactor,normalizer,OrderedFinpartition.atomic]

theorem eppf_one (alpha p : ℝ) (c : OrderedFinpartition 1) : eppf alpha p c=1 := by
  have h : c=OrderedFinpartition.atomic 1 := Subsingleton.elim _ _
  rw [h]
  norm_num [eppf,clusterFactor,blockFactor,normalizer,OrderedFinpartition.atomic]

theorem blockProduct_extendLeft (alpha : ℝ) {n : ℕ} (c : OrderedFinpartition n) :
    (∏i : Fin c.extendLeft.length,blockFactor alpha (c.extendLeft.partSize i))=
      ∏i : Fin c.length,blockFactor alpha (c.partSize i) := by
  change (∏i : Fin (c.length+1),blockFactor alpha (Fin.cons (α := fun _ => ℕ) 1 c.partSize i))=_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  norm_num [blockFactor]

theorem blockProduct_extendMiddle (alpha : ℝ) {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    (∏j : Fin (c.extendMiddle i).length,blockFactor alpha ((c.extendMiddle i).partSize j))=
      ((c.partSize i : ℝ)-alpha)*(∏j : Fin c.length,blockFactor alpha (c.partSize j)) := by
  classical
  change (∏j : Fin c.length,blockFactor alpha (Function.update c.partSize i (c.partSize i+1) j))=_
  have hU : (fun j : Fin c.length => blockFactor alpha (Function.update c.partSize i (c.partSize i+1) j))=
      Function.update (fun j : Fin c.length => blockFactor alpha (c.partSize j)) i
        (blockFactor alpha (c.partSize i+1)) := by
    funext j
    by_cases h : j=i <;> simp [h]
  rw [hU,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase,
    blockFactor_succ alpha (c.partSize i) (c.partSize_pos i)]
  have H := Finset.mul_prod_erase Finset.univ (fun j : Fin c.length => blockFactor alpha (c.partSize j))
    (Finset.mem_univ i)
  rw [← H]
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionProofs
