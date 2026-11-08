-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionProofs

/-! The finite discounted CRP/EPPF law on standard ordered partitions, including
deterministic empty/first-singleton initialization.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionLaw
open Set FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section

def insertionWeight (alpha p : ℝ) {n : ℕ} (c : OrderedFinpartition n) (o : Option (Fin c.length)) : ℝ :=
  if n=0 then (if o=none then 1 else 0) else
    match o with
    | none => ((c.length : ℝ)*alpha-p)/((n : ℝ)-p)
    | some i => ((c.partSize i : ℝ)-alpha)/((n : ℝ)-p)

theorem dimension_sub_pos {alpha p : ℝ} (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (hn : 0<n) : 0<(n : ℝ)-p := by
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  linarith only [hn1,hpa,ha]

theorem eppf_extendLeft {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n) :
    eppf alpha p c.extendLeft=eppf alpha p c*((c.length : ℝ)*alpha-p)/((n : ℝ)-p) := by
  unfold eppf
  rw [blockProduct_extendLeft,OrderedFinpartition.extendLeft_length,
    clusterFactor_succ alpha p c.length (c.length_pos hn),normalizer_succ p n hn]
  have hD := (normalizer_pos (hpa.trans_le ha) n).ne'
  have hnp := (dimension_sub_pos hpa ha hn).ne'
  field_simp [hD,hnp] <;> ring

theorem eppf_extendMiddle {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n) (i : Fin c.length) :
    eppf alpha p (c.extendMiddle i)=eppf alpha p c*((c.partSize i : ℝ)-alpha)/((n : ℝ)-p) := by
  unfold eppf
  rw [blockProduct_extendMiddle,OrderedFinpartition.extendMiddle_length,normalizer_succ p n hn]
  have hD := (normalizer_pos (hpa.trans_le ha) n).ne'
  have hnp := (dimension_sub_pos hpa ha hn).ne'
  field_simp [hD,hnp] <;> ring

theorem insertionWeight_nonneg {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) (o : Option (Fin c.length)) : 0 ≤ insertionWeight alpha p c o := by
  by_cases hn : n=0
  · cases o <;> simp [insertionWeight,hn]
  · have hnpos : 0<n := Nat.pos_of_ne_zero hn
    have hden := (dimension_sub_pos hpa ha hnpos).le
    cases o with
    | none =>
      simp only [insertionWeight,if_neg hn]
      apply div_nonneg _ hden
      have hc1 : (1 : ℝ)≤c.length := by exact_mod_cast c.length_pos hnpos
      have H := mul_le_mul_of_nonneg_right hc1 (hp.trans_lt hpa).le
      norm_num only [one_mul] at H
      linarith only [H,hpa]
    | some i =>
      simp only [insertionWeight,if_neg hn]
      apply div_nonneg _ hden
      have hsi : (1 : ℝ)≤c.partSize i := by exact_mod_cast c.partSize_pos i
      linarith only [hsi,ha]

theorem insertionWeight_sum {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) : (∑o : Option (Fin c.length),insertionWeight alpha p c o)=1 := by
  classical
  by_cases hn : n=0
  · have hc0 : c.length=0 := by have H := c.length_le; omega
    simp [insertionWeight,hn,hc0]
  · have hnpos : 0<n := Nat.pos_of_ne_zero hn
    have hnp := (dimension_sub_pos hpa ha hnpos).ne'
    have hSizes : (∑i : Fin c.length,(c.partSize i : ℝ))=(n : ℝ) := by
      exact_mod_cast sum_partSize c
    have hSum : (∑i : Fin c.length,((c.partSize i : ℝ)-alpha))=(n : ℝ)-(c.length : ℝ)*alpha := by
      rw [Finset.sum_sub_distrib,hSizes]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [Fintype.sum_option]
    simp only [insertionWeight,if_neg hn]
    rw [← Finset.sum_div,hSum]
    field_simp [hnp] <;> ring

theorem eppf_extend {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) (o : Option (Fin c.length)) :
    eppf alpha p (c.extend o)=eppf alpha p c*insertionWeight alpha p c o := by
  by_cases hn : n=0
  · subst n
    cases o with
    | none => simp [OrderedFinpartition.extend,eppf_zero,eppf_one,insertionWeight]
    | some i => have H := c.length_le; have HI := i.isLt; omega
  · have hnpos : 0<n := Nat.pos_of_ne_zero hn
    cases o with
    | none =>
      simp only [OrderedFinpartition.extend,insertionWeight,if_neg hn]
      convert eppf_extendLeft hp hpa ha hnpos c using 1 <;> ring
    | some i =>
      simp only [OrderedFinpartition.extend,insertionWeight,if_neg hn]
      convert eppf_extendMiddle hp hpa ha hnpos c i using 1 <;> ring

theorem eppf_sum {alpha p : ℝ} (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1) (n : ℕ) :
    (∑c : OrderedFinpartition n,eppf alpha p c)=1 := by
  classical
  induction n with
  | zero => simp [eppf_zero]
  | succ n ih =>
    rw [sum_extensions]
    have hInside (c : OrderedFinpartition n) :
        eppf alpha p c.extendLeft+(∑i : Fin c.length,eppf alpha p (c.extendMiddle i))=eppf alpha p c := by
      have hNone := eppf_extend hp hpa ha c none
      have hSome (i : Fin c.length) := eppf_extend hp hpa ha c (some i)
      simp only [OrderedFinpartition.extend] at hNone hSome
      rw [hNone]
      simp_rw [hSome]
      rw [← Finset.mul_sum,← mul_add]
      have H := insertionWeight_sum hp hpa ha c
      rw [Fintype.sum_option] at H
      rw [H,mul_one]
    simp_rw [hInside]
    exact ih

def discountedPartitionPMF (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1) (n : ℕ) :
    PMF (OrderedFinpartition n) :=
  PMF.ofFintype (fun c => ENNReal.ofReal (eppf alpha p c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => eppf_nonneg hp hpa ha c),eppf_sum hp hpa ha]
    exact ENNReal.ofReal_one)

theorem discountedPartitionPMF_apply (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    (n : ℕ) (c : OrderedFinpartition n) :
    discountedPartitionPMF alpha p hp hpa ha n c=ENNReal.ofReal (eppf alpha p c) := rfl

theorem discountedPartitionPMF_extend (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) (o : Option (Fin c.length)) :
    discountedPartitionPMF alpha p hp hpa ha (n+1) (c.extend o)=
      discountedPartitionPMF alpha p hp hpa ha n c*ENNReal.ofReal (insertionWeight alpha p c o) := by
  rw [discountedPartitionPMF_apply,discountedPartitionPMF_apply,eppf_extend hp hpa ha,
    ENNReal.ofReal_mul (eppf_nonneg hp hpa ha c)]

def insertionPMF (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) : PMF (Option (Fin c.length)) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (insertionWeight alpha p c o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => insertionWeight_nonneg hp hpa ha c o),
      insertionWeight_sum hp hpa ha]
    exact ENNReal.ofReal_one)

theorem insertionPMF_apply (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    {n : ℕ} (c : OrderedFinpartition n) (o : Option (Fin c.length)) :
    insertionPMF alpha p hp hpa ha c o=ENNReal.ofReal (insertionWeight alpha p c o) := rfl

theorem insertionPMF_zero_none (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    (c : OrderedFinpartition 0) : insertionPMF alpha p hp hpa ha c none=1 := by
  rw [insertionPMF_apply]
  simp [insertionWeight]

theorem discountedPartitionPMF_zero (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    (c : OrderedFinpartition 0) : discountedPartitionPMF alpha p hp hpa ha 0 c=1 := by
  rw [discountedPartitionPMF_apply,eppf_zero,ENNReal.ofReal_one]

theorem discountedPartitionPMF_one (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1)
    (c : OrderedFinpartition 1) : discountedPartitionPMF alpha p hp hpa ha 1 c=1 := by
  rw [discountedPartitionPMF_apply,eppf_one,ENNReal.ofReal_one]

theorem exists_unique_extension (alpha p : ℝ) (hp : 0≤p) (hpa : p<alpha) (ha : alpha≤1) (n : ℕ) :
    ∃! q : PMF (OrderedFinpartition (n+1)),∀c : OrderedFinpartition n,∀o : Option (Fin c.length),
      q (c.extend o)=discountedPartitionPMF alpha p hp hpa ha n c*insertionPMF alpha p hp hpa ha c o := by
  refine ⟨discountedPartitionPMF alpha p hp hpa ha (n+1),?_,?_⟩
  · intro c o
    rw [insertionPMF_apply]
    exact discountedPartitionPMF_extend alpha p hp hpa ha c o
  · intro q hq
    ext d
    obtain ⟨s,hs⟩ := (OrderedFinpartition.extendEquiv n).surjective d
    rw [← hs]
    change q (s.1.extend s.2)=discountedPartitionPMF alpha p hp hpa ha (n+1) (s.1.extend s.2)
    rw [hq,insertionPMF_apply]
    exact (discountedPartitionPMF_extend alpha p hp hpa ha s.1 s.2).symm

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionLaw
