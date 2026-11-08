-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.JTAnalyticProofs
public import TensorPCA.VariationalProofs

/-! Positive curvature of the slice covariance comparator used by JT. -/
@[expose] public section
namespace TensorPCA.JTModelCurvatureProofs
open Set Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

def shiftedPower (C A B : ℝ) (n : ℕ) (t : ℝ) : ℝ := C*(A+B*t)^n

theorem hasDerivAt_shiftedPower_ratio (C A B : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 < A+B*t) :
    HasDerivAt (shiftedPower C A B n)
      ((n : ℝ)*B*shiftedPower C A B n t/(A+B*t)) t := by
  have hbase : HasDerivAt (fun u : ℝ => A+B*u) B t :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul B).const_add A
  cases n with
  | zero =>
    have he : shiftedPower C A B 0 = fun _ : ℝ => C := by
      funext u
      simp [shiftedPower]
    rw [he]
    simp only [Nat.cast_zero,zero_mul,zero_div]
    exact hasDerivAt_const t C
  | succ n =>
    have hp := (hbase.pow (n+1)).const_mul C
    apply hp.congr_deriv
    simp only [Nat.add_sub_cancel,shiftedPower]
    rw [pow_succ]
    field_simp [ht.ne']

theorem hasDerivAt_deriv_shiftedPower_ratio (C A B : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 < A+B*t) :
    HasDerivAt (deriv (shiftedPower C A B n))
      ((n : ℝ)*((n : ℝ)-1)*B^2*shiftedPower C A B n t/(A+B*t)^2) t := by
  have hbase : HasDerivAt (fun u : ℝ => A+B*u) B t :=
    by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul B).const_add A
  have hv := hasDerivAt_shiftedPower_ratio C A B n ht
  have heq : deriv (shiftedPower C A B n) =ᶠ[𝓝 t]
      (fun u : ℝ => (n : ℝ)*B*shiftedPower C A B n u/(A+B*u)) := by
    have hc : Continuous (fun u : ℝ => A+B*u) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds ht)] with u hu
    exact (hasDerivAt_shiftedPower_ratio C A B n hu).deriv
  have hh : HasDerivAt (fun u : ℝ => (n : ℝ)*B*shiftedPower C A B n u/(A+B*u))
      ((n : ℝ)*((n : ℝ)-1)*B^2*shiftedPower C A B n t/(A+B*t)^2) t := by
    apply (((hv.const_mul ((n : ℝ)*B)).div hbase ht.ne')).congr_deriv
    field_simp [ht.ne']
  exact hh.congr_of_eventuallyEq heq

theorem shiftedPower_curvature_numerator_pos {C A B : ℝ} (hC : 0 < C) (hB : 0 < B)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < A+B*t) :
    0 < 3*(deriv (shiftedPower C A B n) t)^2-
      2*shiftedPower C A B n t*deriv (deriv (shiftedPower C A B n)) t := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hvpos : 0 < shiftedPower C A B n t := mul_pos hC (pow_pos ht n)
  rw [(hasDerivAt_shiftedPower_ratio C A B n ht).deriv,
    (hasDerivAt_deriv_shiftedPower_ratio C A B n ht).deriv]
  have he : 3*((n : ℝ)*B*shiftedPower C A B n t/(A+B*t))^2-
      2*shiftedPower C A B n t*
        ((n : ℝ)*((n : ℝ)-1)*B^2*shiftedPower C A B n t/(A+B*t)^2) =
      (n : ℝ)*((n : ℝ)+2)*B^2*(shiftedPower C A B n t)^2/(A+B*t)^2 := by
    field_simp [ht.ne']
    ring
  rw [he]
  positivity

theorem strictConvexOn_inverseSqrt_shiftedPower {C A B : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (hB : 0 < B) {n : ℕ} (hn : 1 ≤ n) :
    StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (JTAnalyticProofs.inverseSqrt (shiftedPower C A B n)) := by
  have hbase (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < A+B*t :=
    add_pos_of_nonneg_of_pos hA (mul_pos hB ht.1)
  have hc : Continuous (shiftedPower C A B n) := by unfold shiftedPower; fun_prop
  apply JTAnalyticProofs.strictConvexOn_inverseSqrt (convex_Ioo (0 : ℝ) 1) hc.continuousOn
  · intro t ht
    exact mul_pos hC (pow_pos (hbase t ht) n)
  · intro t ht
    exact (hasDerivAt_shiftedPower_ratio C A B n (hbase t (interior_subset ht))).differentiableAt
  · intro t ht
    exact (hasDerivAt_deriv_shiftedPower_ratio C A B n (hbase t (interior_subset ht))).differentiableAt
  · intro t ht
    exact shiftedPower_curvature_numerator_pos hC hB hn (hbase t (interior_subset ht))

theorem deriv2_inverseSqrt_shiftedPower_pos {C A B : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (hB : 0 < B) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (deriv (JTAnalyticProofs.inverseSqrt (shiftedPower C A B n))) t := by
  have hbase (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < A+B*u :=
    add_pos_of_nonneg_of_pos hA (mul_pos hB hu.1)
  apply JTAnalyticProofs.deriv2_inverseSqrt_pos isOpen_Ioo
    (fun u hu => mul_pos hC (pow_pos (hbase u hu) n))
    (fun u hu => (hasDerivAt_shiftedPower_ratio C A B n (hbase u hu)).differentiableAt) ht
    (hasDerivAt_deriv_shiftedPower_ratio C A B n (hbase t ht)).differentiableAt
  exact shiftedPower_curvature_numerator_pos hC hB hn (hbase t ht)

theorem secondDeriv_xiSlice_eq_shiftedPower {k : ℕ} (hk : 1 ≤ k) (m : ℝ) :
    deriv (deriv (Scalar.xiSlice k m)) =
      shiftedPower ((k : ℝ)*((k : ℝ)-1)*(1-m^2)^2) (m^2) (1-m^2) (k-2) := by
  funext t
  exact (VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).deriv

theorem xiSlice_comparator_strictConvex (k : ℕ) (hk : 3 ≤ k) {m : ℝ} (hm : |m| < 1) :
    StrictConvexOn ℝ (Ioo (0 : ℝ) 1)
      (fun t => (Real.sqrt (deriv (deriv (Scalar.xiSlice k m)) t))⁻¹) := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  have hC : 0 < (k : ℝ)*((k : ℝ)-1)*(1-m^2)^2 :=
    mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos hB)
  change StrictConvexOn ℝ (Ioo (0 : ℝ) 1)
    (JTAnalyticProofs.inverseSqrt (deriv (deriv (Scalar.xiSlice k m))))
  rw [secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
  exact strictConvexOn_inverseSqrt_shiftedPower hC (sq_nonneg m) hB (by omega)

/-- The literal positive-curvature hypothesis used in JT's contact-set theorem
holds for every nondegenerate slice, including m=0 away from the endpoint0. -/
theorem xiSlice_comparator_secondDeriv_pos (k : ℕ) (hk : 3 ≤ k) {m t : ℝ}
    (hm : |m| < 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (deriv (fun u => (Real.sqrt (deriv (deriv (Scalar.xiSlice k m)) u))⁻¹)) t := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hB : 0 < 1-m^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one m).mpr hm)
  have hC : 0 < (k : ℝ)*((k : ℝ)-1)*(1-m^2)^2 :=
    mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos hB)
  change 0 < deriv (deriv (JTAnalyticProofs.inverseSqrt (deriv (deriv (Scalar.xiSlice k m))))) t
  rw [secondDeriv_xiSlice_eq_shiftedPower (by omega : 1 ≤ k) m]
  exact deriv2_inverseSqrt_shiftedPower_pos hC (sq_nonneg m) hB (by omega) ht


end
end TensorPCA.JTModelCurvatureProofs
