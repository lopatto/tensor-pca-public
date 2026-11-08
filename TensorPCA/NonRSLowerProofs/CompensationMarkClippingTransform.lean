-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingJensen

/-! Two-sided compensation clipping for the normalized nonlinear transforms. Constants
are uniform as the positive child or parent mass approaches zero; all divisions
require only that the divided mass is positive.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingTransform
open MeasureTheory ProbabilityTheory
open CompensationMarkClippingScalar CompensationMarkClippingMeasure CompensationMarkClippingJensen
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem normalized_log_clipping_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) (hinv : Integrable (fun v => (Y v)⁻¹) nu)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    |Real.log (∫v,(Y v)^alpha ∂nu)-Real.log (∫v,(max b (min (Y v) L))^alpha ∂nu)|/alpha≤
      Real.exp (∫v,|Real.log (Y v)| ∂nu)*((∫v,(Y v)^2 ∂nu)/L+b*(∫v,(Y v)⁻¹ ∂nu)) := by
  let C := ∫v,|Real.log (Y v)| ∂nu
  let m := Real.exp (-C)
  have H := common_power_mean_lower nu hY hpos hY2 hlog hb hb1 hL ha0.le ha1
  change 0<m ∧ m≤1 ∧ m≤(∫v,(Y v)^alpha ∂nu) ∧ m≤(∫v,(max b (min (Y v) L))^alpha ∂nu) at H
  have hinvm : m⁻¹=Real.exp C := by dsimp [m]; rw [← Real.exp_neg,neg_neg]
  have HE := expected_power_clipping_error_le nu hY hpos hY2 hinv hb hb1 hL ha0.le ha1
  have HL := abs_log_sub_le_div H.1 H.2.2.2 H.2.2.1
  rw [div_le_iff₀ ha0]
  calc
    _ ≤ |(∫v,(Y v)^alpha ∂nu)-(∫v,(max b (min (Y v) L))^alpha ∂nu)|/m := HL
    _ ≤ (alpha*((∫v,(Y v)^2 ∂nu)/L+b*(∫v,(Y v)⁻¹ ∂nu)))/m :=
      div_le_div_of_nonneg_right HE H.1.le
    _ = _ := by rw [div_eq_mul_inv,hinvm]; dsimp only [C]; ring

theorem normalized_parent_clipping_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) (hinv : Integrable (fun v => (Y v)⁻¹) nu)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {b L alpha p : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L)
    (hp : 0<p) (hpa : p≤alpha) (ha1 : alpha≤1) :
    |(∫v,(Y v)^alpha ∂nu)^(p/alpha)-(∫v,(max b (min (Y v) L))^alpha ∂nu)^(p/alpha)|/p≤
      Real.exp (∫v,|Real.log (Y v)| ∂nu)*((∫v,(Y v)^2 ∂nu)/L+b*(∫v,(Y v)⁻¹ ∂nu)) := by
  have ha0 : 0<alpha := hp.trans_le hpa
  let C := ∫v,|Real.log (Y v)| ∂nu
  let m := Real.exp (-C)
  have H := common_power_mean_lower nu hY hpos hY2 hlog hb hb1 hL ha0.le ha1
  change 0<m ∧ m≤1 ∧ m≤(∫v,(Y v)^alpha ∂nu) ∧ m≤(∫v,(max b (min (Y v) L))^alpha ∂nu) at H
  have hinvm : m⁻¹=Real.exp C := by dsimp [m]; rw [← Real.exp_neg,neg_neg]
  have HE := expected_power_clipping_error_le nu hY hpos hY2 hinv hb hb1 hL ha0.le ha1
  have HL := abs_rpow_sub_le_div H.1 H.2.1 (div_nonneg hp.le ha0.le)
    ((div_le_one ha0).mpr hpa) H.2.2.2 H.2.2.1
  rw [div_le_iff₀ hp]
  calc
    _ ≤ ((p/alpha)/m)*|(∫v,(Y v)^alpha ∂nu)-(∫v,(max b (min (Y v) L))^alpha ∂nu)| := HL
    _ ≤ ((p/alpha)/m)*(alpha*((∫v,(Y v)^2 ∂nu)/L+b*(∫v,(Y v)⁻¹ ∂nu))) :=
      mul_le_mul_of_nonneg_left HE (div_nonneg (div_nonneg hp.le ha0.le) H.1.le)
    _ = _ := by rw [div_eq_mul_inv (p/alpha),hinvm]; dsimp only [C]; field_simp [ne_of_gt ha0] <;> ring

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingTransform
