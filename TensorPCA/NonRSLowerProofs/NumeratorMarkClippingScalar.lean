-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityLogEmpiricalMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Scalar numerator-mark clipping. The hypotheses Y>=1 are essential;
these estimates do not apply to the unaveraged compensation exponential. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.NumeratorMarkClippingScalar
open MeasureTheory ProbabilityTheory Set
open FiniteCavityLogEmpiricalMoments
noncomputable section

theorem clip_tail_le_square_div (y : ℝ) {L : ℝ} (hL : 0<L) :
    0≤y-min y L ∧ y-min y L≤y^2/L := by
  by_cases hyL : y≤L
  · rw [min_eq_left hyL,sub_self]
    exact ⟨le_rfl,div_nonneg (sq_nonneg _) hL.le⟩
  · have hLy := le_of_not_ge hyL
    rw [min_eq_right hLy]
    refine ⟨sub_nonneg.mpr hLy,(le_div_iff₀ hL).mpr ?_⟩
    have hy : 0≤y := hL.le.trans hLy
    have H := mul_le_mul_of_nonneg_left hLy (sub_nonneg.mpr hLy)
    nlinarith only [H,mul_nonneg hL.le hy]

theorem abs_rpow_sub_le {p x y : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (hx : 1≤x) (hy : 1≤y) :
    |y^p-x^p|≤p*|y-x| := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ => t^p) (f' := fun t => p*t^(p-1)) (C := p)
    (fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)))).hasDerivWithinAt)
    (fun t ht => by
      have ht0 : 0≤t := zero_le_one.trans ht
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hp0,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ht0 _)]
      exact mul_le_of_le_one_right hp0 (Real.rpow_le_one_of_one_le_of_nonpos ht (sub_nonpos.mpr hp1)))
    (convex_Ici (1 : ℝ)) hx hy
  simpa only [Real.norm_eq_abs] using H

theorem clip_log_error_le {y L : ℝ} (hy : 1≤y) (hL : 1≤L) :
    0≤Real.log y-Real.log (min y L) ∧ Real.log y-Real.log (min y L)≤y-min y L := by
  have hm : 1≤min y L := le_min hy hL
  have H := abs_log_sub_le_abs_sub hy hm
  have hnonneg : 0≤Real.log y-Real.log (min y L) :=
    sub_nonneg.mpr (Real.log_le_log (lt_of_lt_of_le zero_lt_one hm) (min_le_left _ _))
  rw [abs_of_nonneg hnonneg,abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))] at H
  exact ⟨hnonneg,H⟩

theorem clip_power_error_le {p y L : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (hy : 1≤y) (hL : 1≤L) :
    0≤y^p-(min y L)^p ∧ y^p-(min y L)^p≤p*(y-min y L) := by
  have hm : 1≤min y L := le_min hy hL
  have H := abs_rpow_sub_le hp0 hp1 hm hy
  have hnonneg : 0≤y^p-(min y L)^p := sub_nonneg.mpr
    (Real.rpow_le_rpow (zero_le_one.trans hm) (min_le_left _ _) hp0)
  rw [abs_of_nonneg hnonneg,abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))] at H
  exact ⟨hnonneg,H⟩

end
end TensorPCA.NonRSLowerProofs.NumeratorMarkClippingScalar
