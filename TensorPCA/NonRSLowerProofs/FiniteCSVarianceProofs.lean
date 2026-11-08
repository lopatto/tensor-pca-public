-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianNormProofs

/-! Nonnegative thermal Gaussian covariance increments. The complete slice covariance is
used, including its positive linear contribution.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set
noncomputable section

theorem xiSlice_deriv_mono_nonneg_overlap (k : ℕ) {m s t : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (hs : 0 ≤ s) (hst : s ≤ t) :
    deriv (Scalar.xiSlice k m) s ≤ deriv (Scalar.xiSlice k m) t := by
  have hB := VariationalProofs.one_sub_sq_nonneg hm
  have hbase : 0 ≤ m ^ 2 + (1 - m ^ 2) * s := add_nonneg (sq_nonneg m) (mul_nonneg hB hs)
  have hle : m ^ 2 + (1 - m ^ 2) * s ≤ m ^ 2 + (1 - m ^ 2) * t :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hst hB)
  rw [VariationalProofs.deriv_xiSlice, VariationalProofs.deriv_xiSlice]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hle (k - 1))
    (mul_nonneg (Nat.cast_nonneg k) hB)

theorem xiSlice_deriv_pos_nonneg_overlap (k : ℕ) (hk : 1 ≤ k) {m t : ℝ}
    (hm0 : 0 < |m|) (hm1 : |m| < 1) (ht : 0 ≤ t) :
    0 < deriv (Scalar.xiSlice k m) t := by
  have hB : 0 < 1 - m ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm1)
  have hbase : 0 < m ^ 2 + (1 - m ^ 2) * t :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (abs_pos.mp hm0)) (mul_nonneg hB.le ht)
  rw [VariationalProofs.deriv_xiSlice]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr (by omega)) hB) (pow_pos hbase _)

theorem actual_thermal_covariance_parameters_admissible (k : ℕ) (hk : 1 ≤ k)
    {beta m q0 q1 : ℝ} (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1)
    (hq0 : 0 ≤ q0) (hq : q0 ≤ q1) (hq1 : q1 ≤ 1) :
    0 < beta ^ 2 * deriv (Scalar.xiSlice k m) q0 ∧
      0 ≤ beta ^ 2 * (deriv (Scalar.xiSlice k m) q1 - deriv (Scalar.xiSlice k m) q0) ∧
      0 ≤ beta ^ 2 * (deriv (Scalar.xiSlice k m) 1 - deriv (Scalar.xiSlice k m) q1) := by
  have hm : m ∈ Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  exact ⟨mul_pos (sq_pos_of_pos hbeta) (xiSlice_deriv_pos_nonneg_overlap k hk hm0 hm1 hq0),
    mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr (xiSlice_deriv_mono_nonneg_overlap k hm hq0 hq)),
    mul_nonneg (sq_nonneg beta)
      (sub_nonneg.mpr (xiSlice_deriv_mono_nonneg_overlap k hm (hq0.trans hq) hq1))⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCS
