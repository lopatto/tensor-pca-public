-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingScalar
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Two-sided clipping for POSITIVE compensation marks. The mark need
not exceed one. Lower-tail errors retain an inverse-mark factor. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingScalar
open Set
open NumeratorMarkClippingScalar
noncomputable section

theorem lower_rpow_error_le {alpha y b : ℝ} (ha0 : 0≤alpha) (ha1 : alpha≤1)
    (hy : 0<y) (hyb : y≤b) (hb1 : b≤1) :
    |b^alpha-y^alpha|≤alpha*(b/y) := by
  have HD := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t^alpha) (f' := fun t => alpha*t^(alpha-1)) (C := alpha/y)
    (fun t ht => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hy.trans_le ht.1)))).hasDerivWithinAt)
    (fun t ht => by
      have ht0 : 0<t := hy.trans_le ht.1
      have HP : t^(alpha-1)≤y⁻¹ := by
        have H := Real.rpow_le_rpow_of_exponent_ge ht0 (ht.2.trans hb1)
          (show (-1 : ℝ)≤alpha-1 by linarith only [ha0])
        rw [Real.rpow_neg_one] at H
        exact H.trans (inv_anti₀ hy ht.1)
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ha0,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _),div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left HP ha0)
    (convex_Icc y b) (left_mem_Icc.mpr hyb) (right_mem_Icc.mpr hyb)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hyb)] at HD
  calc
    _ ≤ (alpha/y)*(b-y) := HD
    _ ≤ (alpha/y)*b := mul_le_mul_of_nonneg_left (by linarith only [hy]) (div_nonneg ha0 hy.le)
    _ = _ := by ring

theorem clipped_pos {y b L : ℝ} (hb : 0<b) : 0<max b (min y L) := hb.trans_le (le_max_left _ _)

theorem clipped_le_upper {y b L : ℝ} (hb1 : b≤1) (hL : 1≤L) : max b (min y L)≤L :=
  max_le (hb1.trans hL) (min_le_right _ _)

theorem clipped_power_error_le {alpha y b L : ℝ} (ha0 : 0≤alpha) (ha1 : alpha≤1)
    (hy : 0<y) (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    |y^alpha-(max b (min y L))^alpha|≤alpha*(y^2/L+b/y) := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hsquare : 0≤y^2/L := div_nonneg (sq_nonneg _) hL0.le
  have hinv : 0≤b/y := (div_pos hb hy).le
  by_cases hLy : L≤y
  · rw [min_eq_right hLy,max_eq_right (hb1.trans hL)]
    have H := (clip_power_error_le ha0 ha1 (hL.trans hLy) hL).2
    rw [min_eq_right hLy] at H
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hL0.le hLy ha0))]
    exact H.trans (mul_le_mul_of_nonneg_left
      (by have HT := (clip_tail_le_square_div y hL0).2; rw [min_eq_right hLy] at HT; linarith only [HT,hinv]) ha0)
  · have hyL : y≤L := le_of_not_ge hLy
    rw [min_eq_left hyL]
    by_cases hyb : y≤b
    · rw [max_eq_left hyb,abs_sub_comm]
      exact (lower_rpow_error_le ha0 ha1 hy hyb hb1).trans
        (mul_le_mul_of_nonneg_left (by linarith only [hsquare]) ha0)
    · rw [max_eq_right (le_of_not_ge hyb),sub_self,abs_zero]
      exact mul_nonneg ha0 (add_nonneg hsquare hinv)

theorem clipped_abs_log_le {y b L : ℝ} (hy : 0<y) (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    |Real.log (max b (min y L))|≤|Real.log y| := by
  by_cases hLy : L≤y
  · rw [min_eq_right hLy,max_eq_right (hb1.trans hL),abs_of_nonneg (Real.log_nonneg hL),
      abs_of_nonneg (Real.log_nonneg (hL.trans hLy))]
    exact Real.log_le_log (zero_lt_one.trans_le hL) hLy
  · have hyL : y≤L := le_of_not_ge hLy
    rw [min_eq_left hyL]
    by_cases hyb : y≤b
    · rw [max_eq_left hyb,abs_of_nonpos (Real.log_nonpos hb.le hb1),
        abs_of_nonpos (Real.log_nonpos hy.le (hyb.trans hb1))]
      exact neg_le_neg (Real.log_le_log hy hyb)
    · rw [max_eq_right (le_of_not_ge hyb)]

theorem abs_log_sub_le_div {m x y : ℝ} (hm : 0<m) (hx : m≤x) (hy : m≤y) :
    |Real.log y-Real.log x|≤|y-x|/m := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun t => t⁻¹) (C := m⁻¹)
    (fun t ht => (Real.hasDerivAt_log (ne_of_gt (hm.trans_le ht))).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (hm.le.trans ht))]
      exact inv_anti₀ hm ht)
    (convex_Ici m) hx hy
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_comm] using H

theorem abs_rpow_sub_le_div {m x y q : ℝ} (hm : 0<m) (hm1 : m≤1)
    (hq0 : 0≤q) (hq1 : q≤1) (hx : m≤x) (hy : m≤y) :
    |y^q-x^q|≤(q/m)*|y-x| := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t^q) (f' := fun t => q*t^(q-1)) (C := q/m)
    (fun t ht => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hm.trans_le ht)))).hasDerivWithinAt)
    (fun t ht => by
      have ht0 : 0<t := hm.trans_le ht
      have HP : t^(q-1)≤m⁻¹ := by
        have H := Real.rpow_le_rpow_of_nonpos hm ht (sub_nonpos.mpr hq1)
        have Hm := Real.rpow_le_rpow_of_exponent_ge hm hm1 (show (-1 : ℝ)≤q-1 by linarith only [hq0])
        rw [Real.rpow_neg_one] at Hm
        exact H.trans Hm
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hq0,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht0.le _),div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left HP hq0)
    (convex_Ici m) hx hy
  simpa only [Real.norm_eq_abs] using H

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingScalar
