-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.TensorOrbitCountProofs
public import TensorPCA.TensorTupleCountProofs
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact signed ordered/unordered tensor overlap kernels and their finite
collision error. No Gaussian law or covariance identity is assumed. -/
@[expose] public section
namespace TensorPCA.TensorOverlapKernelProofs
open TensorOrbitCountProofs TensorTupleCountProofs
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem ordered_product_sum (N k : ℕ) (g : Fin N → ℝ) :
    (∑ i : Fin k → Fin N, ∏ j : Fin k, g (i j)) = (∑ n : Fin N, g n)^k :=
  (Fintype.sum_pow g k).symm

theorem distinct_product_sum (N k : ℕ) (g : Fin N → ℝ) :
    (∑ i : DistinctTuple N k, ∏ j : Fin k, g (i.1 j)) =
      (Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, g n) := by
  simp_rw [prod_tuple_eq_prod_range]
  rw [← Fintype.sum_fiberwise' (@tupleRange N k) (fun S ↦ ∏ n ∈ S.1, g n)]
  simp only [Finset.sum_const, Finset.card_univ, tupleRange_fiber_card, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem ordered_product_decomposition (N k : ℕ) (g : Fin N → ℝ) :
    (∑ n : Fin N, g n)^k =
      (Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, g n)+
        ∑ i ∈ repeatedTuples N k, ∏ j : Fin k, g (i j) := by
  have H := Fintype.sum_subtype_add_sum_subtype
    (Function.Injective : (Fin k → Fin N) → Prop) (fun i ↦ ∏ j : Fin k, g (i j))
  have hr : (∑ i : {i : Fin k → Fin N // ¬Function.Injective i}, ∏ j : Fin k, g (i.1 j)) =
      ∑ i ∈ repeatedTuples N k, ∏ j : Fin k, g (i j) := by
    symm
    exact Finset.sum_subtype (repeatedTuples N k) (by simp [repeatedTuples]) _
  rw [← ordered_product_sum N k g, ← distinct_product_sum N k g]
  rw [hr] at H
  exact H.symm

theorem abs_tuple_product_le {N k : ℕ} (g : Fin N → ℝ) {B : ℝ}
    (hb : ∀ n, |g n| ≤ B) (i : Fin k → Fin N) :
    |∏ j : Fin k, g (i j)| ≤ B^k := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _j : Fin k, B := Finset.prod_le_prod₀ (fun j _ ↦ abs_nonneg _) (fun j _ ↦ hb (i j))
    _ = _ := by simp

/-- The absolute collision error is valid for signed coordinates and all
N,k, including the degree-zero and degree-one cases. -/
theorem abs_distinct_sum_error_le {N k : ℕ} (g : Fin N → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ n, |g n| ≤ B) :
    |(Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, g n)-(∑ n : Fin N, g n)^k| ≤
      (k : ℝ)^2*(N : ℝ)^(k-1)*B^k := by
  have he : (Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, g n)-
      (∑ n : Fin N, g n)^k = -(∑ i ∈ repeatedTuples N k, ∏ j : Fin k, g (i j)) := by
    linarith [ordered_product_decomposition N k g]
  rw [he, abs_neg]
  have hc : ((repeatedTuples N k).card : ℝ) ≤ (k : ℝ)^2*(N : ℝ)^(k-1) := by
    exact_mod_cast repeatedTuples_card_le N k
  calc
    _ ≤ ∑ i ∈ repeatedTuples N k, |∏ j : Fin k, g (i j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ repeatedTuples N k, B^k :=
      Finset.sum_le_sum (fun i _ ↦ abs_tuple_product_le g hb i)
    _ = ((repeatedTuples N k).card : ℝ)*B^k := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (pow_nonneg hB _)

theorem abs_covariance_kernel_error_le {N k : ℕ} (v w : Fin N → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hv : ∀ n, |v n| ≤ K) (hw : ∀ n, |w n| ≤ K) :
    |(Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, v n*w n)-
      (∑ n : Fin N, v n*w n)^k| ≤ (k : ℝ)^2*(N : ℝ)^(k-1)*K^(2*k) := by
  have H := abs_distinct_sum_error_le (k := k) (fun n ↦ v n*w n) (sq_nonneg K) (fun n ↦ by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hv n) (hw n) (abs_nonneg _) hK)
  simpa only [← pow_mul] using H

/-- The actual normalized unordered monomial kernel differs from the
kth power of the normalized overlap by an explicit O(1/N) collision error. -/
theorem abs_normalized_covariance_kernel_error_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (v w : Fin N → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ n, |v n| ≤ K) (hw : ∀ n, |w n| ≤ K) :
    |((Nat.factorial k : ℝ)*(∑ S : KSubset N k, ∏ n ∈ S.1, v n*w n))/(N : ℝ)^k-
      ((∑ n : Fin N, v n*w n)/(N : ℝ))^k| ≤ (k : ℝ)^2*K^(2*k)/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_pow, ← sub_div, abs_div, abs_of_pos (pow_pos hn k)]
  calc
    _ ≤ ((k : ℝ)^2*(N : ℝ)^(k-1)*K^(2*k))/(N : ℝ)^k :=
      div_le_div_of_nonneg_right (abs_covariance_kernel_error_le v w hK hv hw) (pow_nonneg hn.le _)
    _ = _ := by
      have hp : (N : ℝ)^k = (N : ℝ)^(k-1)*(N : ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hp]
      field_simp [hn.ne']

end
end TensorPCA.TensorOverlapKernelProofs
