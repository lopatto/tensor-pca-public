-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionProofs
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Exact Pochhammer coefficients for the finite discounted partition law.
The logarithmic root is treated separately, so no root identity divides by p. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionCoefficients
open FiniteDiscountedPartitionProofs
open scoped BigOperators
noncomputable section

theorem asc_neg_eq_normalizer (p : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n+1)).eval (-p) = -p*normalizer p (n+1) := by
  induction n with
  | zero => simp [normalizer]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, normalizer_succ p (n+1) (by omega), ih]
    ring

theorem signed_desc_eq_blockFactor (alpha : ℝ) (n : ℕ) :
    (-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval alpha =
      -alpha*blockFactor alpha (n+1) := by
  induction n with
  | zero => simp [blockFactor]
  | succ n ih =>
    rw [descPochhammer_succ_eval, pow_succ,
      blockFactor_succ alpha (n+1) (by omega)]
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      (-1 : ℝ)^(n+1)*(-1)*((descPochhammer ℝ (n+1)).eval alpha*(alpha-(n+1))) =
          ((-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval alpha)*((n+1)-alpha) := by ring
      _ = _ := by rw [ih]; ring

theorem scaled_desc_eq_clusterFactor {alpha : ℝ} (ha : alpha≠0) (p : ℝ) (n : ℕ) :
    (-alpha)^(n+1)*(descPochhammer ℝ (n+1)).eval (p/alpha) =
      -p*clusterFactor alpha p (n+1) := by
  induction n with
  | zero => simp [clusterFactor]; field_simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, pow_succ,
      clusterFactor_succ alpha p (n+1) (by omega)]
    simp only [Nat.cast_add,Nat.cast_one]
    have H : (-alpha)*(p/alpha-(n+1)) = (n+1)*alpha-p := by
      field_simp
      <;> ring
    calc
      (-alpha)^(n+1)*(-alpha)*((descPochhammer ℝ (n+1)).eval (p/alpha)*(p/alpha-(n+1))) =
          ((-alpha)^(n+1)*(descPochhammer ℝ (n+1)).eval (p/alpha))*
            ((-alpha)*(p/alpha-(n+1))) := by ring
      _ = _ := by rw [H,ih]; ring

theorem normalizer_zero_eq_factorial (n : ℕ) :
    normalizer 0 (n+1) = (n.factorial : ℝ) := by
  induction n with
  | zero => simp [normalizer]
  | succ n ih =>
    rw [normalizer_succ 0 (n+1) (by omega),ih,Nat.factorial_succ]
    simp only [sub_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem clusterFactor_zero_eq_factorial (alpha : ℝ) (n : ℕ) :
    clusterFactor alpha 0 (n+1) = alpha^n*(n.factorial : ℝ) := by
  induction n with
  | zero => simp [clusterFactor]
  | succ n ih =>
    rw [clusterFactor_succ alpha 0 (n+1) (by omega),ih,pow_succ,Nat.factorial_succ]
    simp only [sub_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem logarithmic_scaled_coefficient {alpha : ℝ} (ha : alpha≠0) (n : ℕ) :
    (((-1 : ℝ)^n*(n.factorial : ℝ))/alpha)*(-alpha)^(n+1) =
      -clusterFactor alpha 0 (n+1) := by
  rw [clusterFactor_zero_eq_factorial,pow_succ]
  have H : (-1 : ℝ)^n*(-alpha)^n = alpha^n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (((-1 : ℝ)^n*(n.factorial : ℝ))/alpha)*((-alpha)^n*(-alpha)) =
      -(((-1 : ℝ)^n*(-alpha)^n)*(n.factorial : ℝ)) := by field_simp
    _ = _ := by rw [H]

theorem block_product_eq (alpha : ℝ) {n : ℕ} (c : OrderedFinpartition n)
    (z : Fin c.length→ℝ) :
    (∏i,((-1 : ℝ)^(c.partSize i)*(descPochhammer ℝ (c.partSize i)).eval alpha)*z i) =
      (-alpha)^c.length*(∏i,blockFactor alpha (c.partSize i))*(∏i,z i) := by
  classical
  have H (i : Fin c.length) :
      (-1 : ℝ)^(c.partSize i)*(descPochhammer ℝ (c.partSize i)).eval alpha =
        -alpha*blockFactor alpha (c.partSize i) := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (c.partSize_pos i))
    rw [hs]
    exact signed_desc_eq_blockFactor alpha s
  simp_rw [H]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem outer_partition_coefficient {alpha p : ℝ} (ha : alpha≠0) (hp : p<1)
    {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n) (z : Fin c.length→ℝ) :
    (descPochhammer ℝ c.length).eval (p/alpha)*
        (∏i,((-1 : ℝ)^(c.partSize i)*(descPochhammer ℝ (c.partSize i)).eval alpha)*z i) =
      (-p*normalizer p n)*(eppf alpha p c*(∏i,z i)) := by
  have H : (-alpha)^c.length*(descPochhammer ℝ c.length).eval (p/alpha) =
      -p*clusterFactor alpha p c.length := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (c.length_pos hn))
    rw [hs]
    exact scaled_desc_eq_clusterFactor ha p s
  rw [block_product_eq]
  calc
    (descPochhammer ℝ c.length).eval (p/alpha)*
        ((-alpha)^c.length*(∏i,blockFactor alpha (c.partSize i))*(∏i,z i)) =
      ((-alpha)^c.length*(descPochhammer ℝ c.length).eval (p/alpha))*
        (∏i,blockFactor alpha (c.partSize i))*(∏i,z i) := by ring
    _ = (-p*clusterFactor alpha p c.length)*
        (∏i,blockFactor alpha (c.partSize i))*(∏i,z i) := by rw [H]
    _ = _ := by
      unfold eppf
      field_simp [ne_of_gt (normalizer_pos hp n)]

theorem logarithmic_partition_coefficient {alpha : ℝ} (ha : alpha≠0)
    {n : ℕ} (hn : 0<n) (c : OrderedFinpartition n) (z : Fin c.length→ℝ) :
    (((-1 : ℝ)^(c.length-1)*((c.length-1).factorial : ℝ))/alpha)*
        (∏i,((-1 : ℝ)^(c.partSize i)*(descPochhammer ℝ (c.partSize i)).eval alpha)*z i) =
      -normalizer 0 n*(eppf alpha 0 c*(∏i,z i)) := by
  have H : (((-1 : ℝ)^(c.length-1)*((c.length-1).factorial : ℝ))/alpha)*
      (-alpha)^c.length = -clusterFactor alpha 0 c.length := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (c.length_pos hn))
    rw [hs]
    simpa using logarithmic_scaled_coefficient ha s
  rw [block_product_eq]
  calc
    (((-1 : ℝ)^(c.length-1)*((c.length-1).factorial : ℝ))/alpha)*
        ((-alpha)^c.length*(∏i,blockFactor alpha (c.partSize i))*(∏i,z i)) =
      ((((-1 : ℝ)^(c.length-1)*((c.length-1).factorial : ℝ))/alpha)*(-alpha)^c.length)*
        (∏i,blockFactor alpha (c.partSize i))*(∏i,z i) := by ring
    _ = (-clusterFactor alpha 0 c.length)*
        (∏i,blockFactor alpha (c.partSize i))*(∏i,z i) := by rw [H]
    _ = _ := by
      unfold eppf
      field_simp [ne_of_gt (normalizer_pos (by norm_num : (0:ℝ)<1) n)]

end
end TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionCoefficients
