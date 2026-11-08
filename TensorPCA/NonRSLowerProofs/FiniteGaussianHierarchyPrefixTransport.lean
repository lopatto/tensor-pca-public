-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticUniformEndpoint
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianDepthMoment

/-! Exact original-node prefix/suffix transport for finite Gaussian hierarchies.
The original final endpoint is retained in every suffix. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixTransport
open FiniteCSGaussianDepthMoment
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def prefixValues {r s : ℕ} (y : Fin (r+s+1)→ℝ) : Fin (r+1)→ℝ :=
  fun i => y ⟨i,by omega⟩

def suffixValues {r s : ℕ} (y : Fin (r+s+1)→ℝ) : Fin (s+1)→ℝ :=
  fun i => y ⟨r+i,by omega⟩

theorem prefix_zero {r s : ℕ} (y : Fin (r+s+1)→ℝ) : prefixValues y 0=y 0 := rfl

theorem prefix_last_eq_suffix_zero {r s : ℕ} (y : Fin (r+s+1)→ℝ) :
    prefixValues y (Fin.last r)=suffixValues y 0 := rfl

theorem suffix_last {r s : ℕ} (y : Fin (r+s+1)→ℝ) :
    suffixValues y (Fin.last s)=y (Fin.last (r+s)) := rfl

theorem increments_prefix {r s : ℕ} (y : Fin (r+s+1)→ℝ) (j : Fin r) :
    increments (prefixValues y) j=increments y (j.castAdd s) := rfl

theorem increments_suffix {r s : ℕ} (y : Fin (r+s+1)→ℝ) (j : Fin s) :
    increments (suffixValues y) j=increments y (j.natAdd r) := rfl

theorem variance_layers_split {r s : ℕ} (x : Fin (r+s)→ℝ) (y : Fin (r+s+1)→ℝ) :
    List.ofFn (fun j : Fin (r+s) => (x j,increments y j))=
      List.ofFn (fun j : Fin r => (x (j.castAdd s),increments (prefixValues y) j))++
        List.ofFn (fun j : Fin s => (x (j.natAdd r),increments (suffixValues y) j)) := List.ofFn_add

theorem sum_fin_split {r s : ℕ} (f : Fin (r+s)→ℝ) :
    (∑j : Fin (r+s),f j)=(∑j : Fin r,f (j.castAdd s))+(∑j : Fin s,f (j.natAdd r)) := by
  exact Fin.sum_univ_add f

theorem prefixValues_monotone {r s : ℕ} {y : Fin (r+s+1)→ℝ} (hy : Monotone y) :
    Monotone (prefixValues y) := fun i j hij => hy hij

theorem suffixValues_monotone {r s : ℕ} {y : Fin (r+s+1)→ℝ} (hy : Monotone y) :
    Monotone (suffixValues y) := by
  intro i j hij
  apply hy
  change r+(i : ℕ)≤r+(j : ℕ)
  omega

theorem head_add_prefix_increments {r s : ℕ} (y : Fin (r+s+1)→ℝ) :
    y 0+(∑j : Fin r,increments (prefixValues y) j)=suffixValues y 0 := by
  have H := sum_adjacent_sub (prefixValues y)
  rw [prefix_zero,prefix_last_eq_suffix_zero] at H
  change (∑j : Fin r,increments (prefixValues y) j)=suffixValues y 0-y 0 at H
  linarith only [H]

theorem suffix_head_add_increments {r s : ℕ} (y : Fin (r+s+1)→ℝ) :
    suffixValues y 0+(∑j : Fin s,increments (suffixValues y) j)=y (Fin.last (r+s)) := by
  have H := sum_adjacent_sub (suffixValues y)
  rw [suffix_last] at H
  change (∑j : Fin s,increments (suffixValues y) j)=y (Fin.last (r+s))-suffixValues y 0 at H
  linarith only [H]

theorem weighted_correction_split {r s : ℕ} (x : Fin (r+s)→ℝ) (z : Fin (r+s+1)→ℝ) :
    (∑j : Fin (r+s),x j*increments z j)=
      (∑j : Fin r,x (j.castAdd s)*increments (prefixValues z) j)+
        (∑j : Fin s,x (j.natAdd r)*increments (suffixValues z) j) := by
  simpa only [increments_prefix,increments_suffix] using
    sum_fin_split (fun j => x j*increments z j)

theorem prefix_weighted_correction_le {r s : ℕ} (x : Fin (r+s)→ℝ) (z : Fin (r+s+1)→ℝ)
    {delta : ℝ} (hdelta : 0≤delta) (hsmall : ∀j : Fin r,x (j.castAdd s)≤delta)
    (hz : Monotone z) :
    (∑j : Fin r,x (j.castAdd s)*increments (prefixValues z) j)≤
      delta*(z (Fin.last (r+s))-z 0) := by
  have HInc (j : Fin r) : 0≤ increments (prefixValues z) j :=
    sub_nonneg.mpr (prefixValues_monotone hz (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  have HSum : (∑j : Fin r,x (j.castAdd s)*increments (prefixValues z) j)≤
      delta*(∑j : Fin r,increments (prefixValues z) j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hsmall j) (HInc j))
  have HT := sum_adjacent_sub (prefixValues z)
  rw [prefix_zero] at HT
  change (∑j : Fin r,increments (prefixValues z) j)=prefixValues z (Fin.last r)-z 0 at HT
  have HLast : prefixValues z (Fin.last r)≤z (Fin.last (r+s)) := hz (Fin.le_last _)
  apply HSum.trans
  rw [HT]
  apply mul_le_mul_of_nonneg_left _ hdelta
  linarith only [HLast]

theorem weighted_correction_suffix_loss {r s : ℕ} (x : Fin (r+s)→ℝ) (z : Fin (r+s+1)→ℝ)
    {delta : ℝ} (hdelta : 0≤delta) (hx : ∀j,0≤x j)
    (hsmall : ∀j : Fin r,x (j.castAdd s)≤delta) (hz : Monotone z) :
    0≤(∑j : Fin (r+s),x j*increments z j)-
        (∑j : Fin s,x (j.natAdd r)*increments (suffixValues z) j) ∧
      (∑j : Fin (r+s),x j*increments z j)-
        (∑j : Fin s,x (j.natAdd r)*increments (suffixValues z) j)≤
          delta*(z (Fin.last (r+s))-z 0) := by
  rw [weighted_correction_split,add_sub_cancel_right]
  constructor
  · apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hx _)
    exact sub_nonneg.mpr (prefixValues_monotone hz (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  · exact prefix_weighted_correction_le x z hdelta hsmall hz

theorem exists_height_cut (delta : ℝ) : ∀(d : ℕ) (x : Fin d→ℝ),Monotone x→
    ∃r : ℕ,r≤d ∧ (∀j : Fin d,(j : ℕ)<r→x j≤delta) ∧
      (∀j : Fin d,r≤(j : ℕ)→delta<x j) := by
  intro d
  induction d with
  | zero =>
    intro x hx
    exact ⟨0,le_refl _,fun j => Fin.elim0 j,fun j => Fin.elim0 j⟩
  | succ d ih =>
    intro x hx
    by_cases h0 : x 0≤delta
    · have hTail : Monotone (fun j : Fin d => x j.succ) := by
        intro i j hij
        apply hx
        change (i : ℕ)+1≤(j : ℕ)+1
        exact Nat.succ_le_succ hij
      obtain ⟨r,hr,hsmall,hlarge⟩ := ih (fun j => x j.succ) hTail
      refine ⟨r+1,Nat.succ_le_succ hr,?_,?_⟩
      · intro j hj
        cases j using Fin.cases with
        | zero => exact h0
        | succ j => exact hsmall j (by change (j : ℕ)+1<r+1 at hj; omega)
      · intro j hj
        cases j using Fin.cases with
        | zero => change r+1≤0 at hj; omega
        | succ j => exact hlarge j (by change r+1≤(j : ℕ)+1 at hj; omega)
    · refine ⟨0,Nat.zero_le _,?_,?_⟩
      · intro j hj
        omega
      · intro j hj
        exact (lt_of_not_ge h0).trans_le (hx (Fin.zero_le j))

theorem exists_height_split {d : ℕ} (x : Fin d→ℝ) (hx : Monotone x) (delta : ℝ) :
    ∃(r s : ℕ) (e : r+s=d),
      (∀j : Fin r,x (Fin.cast e (j.castAdd s))≤delta) ∧
        (∀j : Fin s,delta<x (Fin.cast e (j.natAdd r))) := by
  obtain ⟨r,hr,hsmall,hlarge⟩ := exists_height_cut delta d x hx
  let s := d-r
  have e : r+s=d := Nat.add_sub_of_le hr
  refine ⟨r,s,e,?_,?_⟩
  · intro j
    apply hsmall
    exact j.isLt
  · intro j
    apply hlarge
    change r≤r+(j : ℕ)
    omega

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixTransport
