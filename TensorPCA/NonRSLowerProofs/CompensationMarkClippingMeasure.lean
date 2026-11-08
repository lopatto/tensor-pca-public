-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingScalar

/-! Positive compensation-mark clipping under probability measures. Square and inverse
means control the two tails; logarithmic integrability is carried explicitly for the
later uniform Jensen lower bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingMeasure
open MeasureTheory ProbabilityTheory Filter
open CompensationMarkClippingScalar
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem power_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) {alpha : ℝ} (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    Integrable (fun v => (Y v)^alpha) nu := by
  apply ((integrable_const (1 : ℝ)).add hY2).mono' (hY.pow_const alpha).aestronglyMeasurable
  filter_upwards [hpos] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hv.le alpha)]
  change (Y v)^alpha≤1+(Y v)^2
  by_cases hy1 : Y v≤1
  · exact (Real.rpow_le_one hv.le hy1 ha0).trans (by nlinarith only [sq_nonneg (Y v)])
  · have H := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy1)
      (ha1.trans (by norm_num : (1 : ℝ)≤2))
    rw [Real.rpow_two] at H
    exact H.trans (by linarith)

theorem clipped_power_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L)
    (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    Integrable (fun v => (max b (min (Y v) L))^alpha) nu := by
  apply Integrable.of_bound ((measurable_const.max (hY.min measurable_const)).pow_const alpha).aestronglyMeasurable L
  filter_upwards [] with v
  have hp := clipped_pos (y := Y v) (L := L) hb
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp.le alpha)]
  have H := Real.rpow_le_rpow hp.le (clipped_le_upper (y := Y v) hb1 hL) ha0
  exact H.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL ha1)

theorem clipped_log_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {b L : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    Integrable (fun v => Real.log (max b (min (Y v) L))) nu := by
  apply hlog.abs.mono' (measurable_const.max (hY.min measurable_const)).log.aestronglyMeasurable
  filter_upwards [hpos] with v hv
  simpa only [Real.norm_eq_abs] using clipped_abs_log_le hv hb hb1 hL

theorem clipped_abs_log_integral_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {b L : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    (∫v,|Real.log (max b (min (Y v) L))| ∂nu)≤∫v,|Real.log (Y v)| ∂nu :=
  integral_mono_ae (clipped_log_integrable nu hY hpos hlog hb hb1 hL).abs hlog.abs
    (hpos.mono (fun _ hv => clipped_abs_log_le hv hb hb1 hL))

theorem expected_power_clipping_error_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) (hinv : Integrable (fun v => (Y v)⁻¹) nu)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    |(∫v,(Y v)^alpha ∂nu)-(∫v,(max b (min (Y v) L))^alpha ∂nu)|≤
      alpha*((∫v,(Y v)^2 ∂nu)/L+b*(∫v,(Y v)⁻¹ ∂nu)) := by
  have hA := power_integrable nu hY hpos hY2 ha0 ha1
  have hB := clipped_power_integrable nu hY hb hb1 hL ha0 ha1
  have hInv : Integrable (fun v => b/Y v) nu := by
    simpa only [div_eq_mul_inv] using hinv.const_mul b
  have hD : Integrable (fun v => alpha*((Y v)^2/L+b/Y v)) nu := by
    have H := ((hY2.div_const L).add hInv).const_mul alpha
    exact H
  have H := integral_mono_ae (hA.sub hB).abs hD
    (hpos.mono (fun _ hv => clipped_power_error_le ha0 ha1 hv hb hb1 hL))
  change (∫v,|(Y v)^alpha-(max b (min (Y v) L))^alpha| ∂nu)≤
    ∫v,alpha*((Y v)^2/L+b/Y v) ∂nu at H
  rw [integral_const_mul,integral_add (hY2.div_const L) hInv,integral_div] at H
  have HInv : (∫v,b/Y v ∂nu)=b*(∫v,(Y v)⁻¹ ∂nu) := by
    simp only [div_eq_mul_inv,integral_const_mul]
  rw [HInv] at H
  have HA : |(∫v,(Y v)^alpha ∂nu)-(∫v,(max b (min (Y v) L))^alpha ∂nu)|≤
      ∫v,|(Y v)^alpha-(max b (min (Y v) L))^alpha| ∂nu := by
    rw [← integral_sub hA hB]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f := fun v => (Y v)^alpha-(max b (min (Y v) L))^alpha) (μ := nu)
  exact HA.trans H

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingMeasure
