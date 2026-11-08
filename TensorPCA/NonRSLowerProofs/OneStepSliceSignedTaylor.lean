-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepSliceSignedDerivative

/-! A signed-domain quadratic Taylor bound for the slice polynomial. The coefficient
one, rather than one half, avoids any additional Taylor machinery and is sufficient
for the finite cavity reference estimate.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepSliceSignedTaylor
open Set VariationalProofs OneStepSliceSignedDerivative
noncomputable section

theorem secondDeriv_one_nonneg (k : ℕ) (hk : 3≤k) {m : ℝ}
    (hm : m∈Icc (-1 : ℝ) 1) : 0≤deriv (deriv (Scalar.xiSlice k m)) 1 :=
  (abs_nonneg _).trans (abs_secondDeriv_le k hk (u := 1) (q := 1) hm (by constructor <;> norm_num)
    (by constructor <;> norm_num))

theorem deriv_lipschitz_unit (k : ℕ) (hk : 3≤k) {m r s : ℝ}
    (hm : m∈Icc (-1 : ℝ) 1) (hr : r∈Icc (-1 : ℝ) 1) (hs : s∈Icc (-1 : ℝ) 1) :
    |deriv (Scalar.xiSlice k m) r-deriv (Scalar.xiSlice k m) s|≤
      deriv (deriv (Scalar.xiSlice k m)) 1*|r-s| := by
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t∈Icc (-1 : ℝ) 1) =>
      (hasDerivAt_deriv_xiSlice (by omega : 1≤k) m t).differentiableAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using
      abs_secondDeriv_le k hk hm (show (1 : ℝ)∈Icc 0 1 by constructor <;> norm_num) ht)
    (convex_Icc (-1 : ℝ) 1) hs hr
  simpa only [Real.norm_eq_abs] using H

theorem xiSlice_taylor_abs_le (k : ℕ) (hk : 3≤k) {m r s : ℝ}
    (hm : m∈Icc (-1 : ℝ) 1) (hr : r∈Icc (-1 : ℝ) 1) (hs : s∈Icc (-1 : ℝ) 1) :
    |Scalar.xiSlice k m r-Scalar.xiSlice k m s-deriv (Scalar.xiSlice k m) s*(r-s)|≤
      deriv (deriv (Scalar.xiSlice k m)) 1*(r-s)^2 := by
  let f := Scalar.xiSlice k m
  let K := deriv (deriv f) 1
  let G : ℝ→ℝ := fun t => f t-f s-deriv f s*(t-s)
  have hK : 0≤K := secondDeriv_one_nonneg k hk hm
  have hG (t : ℝ) : HasDerivAt G (deriv f t-deriv f s) t := by
    simpa only [G,f,Pi.sub_def,id_eq,mul_one] using
      (((hasDerivAt_xiSlice k m t).differentiableAt.hasDerivAt).sub_const (f s)).sub
        (((hasDerivAt_id t).sub_const s).const_mul (deriv f s))
  have hunit (t : ℝ) (ht : t∈Icc (min s r) (max s r)) : t∈Icc (-1 : ℝ) 1 := by
    constructor
    · exact (le_min hs.1 hr.1).trans ht.1
    · exact ht.2.trans (max_le hs.2 hr.2)
  have hdist (t : ℝ) (ht : t∈Icc (min s r) (max s r)) : |t-s|≤|r-s| := by
    rcases le_total s r with hsr|hrs
    · simp only [min_eq_left hsr,max_eq_right hsr] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1),abs_of_nonneg (sub_nonneg.mpr hsr)]
      linarith only [ht.2]
    · simp only [min_eq_right hrs,max_eq_left hrs] at ht
      rw [abs_of_nonpos (sub_nonpos.mpr ht.2),abs_of_nonpos (sub_nonpos.mpr hrs)]
      linarith only [ht.1]
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t∈Icc (min s r) (max s r)) => (hG t).differentiableAt)
    (fun t ht => by
      rw [(hG t).deriv,Real.norm_eq_abs]
      exact (deriv_lipschitz_unit k hk hm (hunit t ht) hs).trans
        (mul_le_mul_of_nonneg_left (hdist t ht) hK))
    (convex_Icc (min s r) (max s r))
    (show s∈Icc (min s r) (max s r) from ⟨min_le_left _ _,le_max_left _ _⟩)
    (show r∈Icc (min s r) (max s r) from ⟨min_le_right _ _,le_max_right _ _⟩)
  have H' : |f r-f s-deriv f s*(r-s)|≤K*|r-s| *|r-s| := by
    simpa only [G,Real.norm_eq_abs,sub_self,mul_zero,sub_zero] using H
  change |f r-f s-deriv f s*(r-s)|≤K*(r-s)^2
  calc
    _ ≤ K*|r-s| *|r-s| := H'
    _ = _ := by rw [mul_assoc,← pow_two,sq_abs]

theorem thermal_xiSlice_taylor_abs_le (k : ℕ) (hk : 3≤k) {m r s : ℝ}
    (hm : m∈Icc (-1 : ℝ) 1) (hr : r∈Icc (-1 : ℝ) 1) (hs : s∈Icc (-1 : ℝ) 1)
    (beta : ℝ) :
    |beta^2*(Scalar.xiSlice k m r-Scalar.xiSlice k m s-deriv (Scalar.xiSlice k m) s*(r-s))|≤
      beta^2*deriv (deriv (Scalar.xiSlice k m)) 1*(r-s)^2 := by
  rw [abs_mul,abs_of_nonneg (sq_nonneg beta)]
  exact (mul_le_mul_of_nonneg_left (xiSlice_taylor_abs_le k hk hm hr hs) (sq_nonneg beta)).trans_eq (by ring)


end
end TensorPCA.NonRSLowerProofs.OneStepSliceSignedTaylor
