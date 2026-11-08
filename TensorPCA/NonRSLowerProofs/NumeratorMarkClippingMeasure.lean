-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingScalar

/-! Probability-measure clipping and nonlinear integrability for numerator marks bounded
below by one.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.NumeratorMarkClippingMeasure
open MeasureTheory ProbabilityTheory Filter
open NumeratorMarkClippingScalar
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem mark_integrable_of_square (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hY1 : ∀ᵐv∂nu,1≤Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) : Integrable Y nu := by
  apply hY2.mono' hY.aestronglyMeasurable
  filter_upwards [hY1] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans hv)]
  nlinarith only [hv]

theorem clip_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hY1 : ∀ᵐv∂nu,1≤Y v) {L : ℝ} (hL : 1≤L) :
    Integrable (fun v => min (Y v) L) nu := by
  apply Integrable.of_bound (hY.min measurable_const).aestronglyMeasurable L
  filter_upwards [hY1] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans (le_min hv hL))]
  exact min_le_right _ _

theorem clip_tail_integrable_and_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hY1 : ∀ᵐv∂nu,1≤Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu) {L : ℝ} (hL : 1≤L) :
    Integrable (fun v => Y v-min (Y v) L) nu ∧
      0≤(∫v,Y v-min (Y v) L ∂nu) ∧
      (∫v,Y v-min (Y v) L ∂nu)≤(∫v,(Y v)^2 ∂nu)/L := by
  have hi := (mark_integrable_of_square nu hY hY1 hY2).sub (clip_integrable nu hY hY1 hL)
  refine ⟨hi,integral_nonneg (fun v => sub_nonneg.mpr (min_le_left _ _)),?_⟩
  have H := integral_mono hi (hY2.div_const L)
    (fun v => (clip_tail_le_square_div (Y v) (lt_of_lt_of_le zero_lt_one hL)).2)
  change (∫v,Y v-min (Y v) L ∂nu)≤∫v,(Y v)^2/L ∂nu at H
  rw [integral_div] at H
  exact H

theorem log_integrable_of_one_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Integrable Y nu) (hY1 : ∀ᵐv∂nu,1≤Y v) :
    Integrable (fun v => Real.log (Y v)) nu := by
  apply hY.mono' hY.aestronglyMeasurable.aemeasurable.log.aestronglyMeasurable
  filter_upwards [hY1] with v hv
  have H := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hv)
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hv)]
  linarith only [H]

theorem power_integrable_of_one_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Integrable Y nu) (hY1 : ∀ᵐv∂nu,1≤Y v) {p : ℝ} (hp1 : p≤1) :
    Integrable (fun v => (Y v)^p) nu := by
  apply hY.mono' (hY.aestronglyMeasurable.aemeasurable.pow_const p).aestronglyMeasurable
  filter_upwards [hY1] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hv) p)]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hv hp1

theorem expected_log_sub_le_expected_sub (nu : Measure V) [IsProbabilityMeasure nu]
    {Y Z : V→ℝ} (hY : Integrable Y nu) (hZ : Integrable Z nu)
    (hb : ∀ᵐv∂nu,1≤Z v ∧ Z v≤Y v) :
    0≤(∫v,Real.log (Y v) ∂nu)-(∫v,Real.log (Z v) ∂nu) ∧
      (∫v,Real.log (Y v) ∂nu)-(∫v,Real.log (Z v) ∂nu)≤∫v,Y v-Z v ∂nu := by
  have hZ1 := hb.mono (fun _ hv => hv.1)
  have hY1 := hb.mono (fun _ hv => hv.1.trans hv.2)
  have hi := (log_integrable_of_one_le nu hY hY1).sub (log_integrable_of_one_le nu hZ hZ1)
  rw [← integral_sub (log_integrable_of_one_le nu hY hY1) (log_integrable_of_one_le nu hZ hZ1)]
  refine ⟨integral_nonneg_of_ae (hb.mono (fun _ hv => sub_nonneg.mpr
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hv.1) hv.2))),?_⟩
  apply integral_mono_ae hi (hY.sub hZ)
  filter_upwards [hb] with v hv
  have H := FiniteCavityLogEmpiricalMoments.abs_log_sub_le_abs_sub (hv.1.trans hv.2) hv.1
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (lt_of_lt_of_le zero_lt_one hv.1) hv.2)),
    abs_of_nonneg (sub_nonneg.mpr hv.2)] at H
  exact H

theorem expected_power_sub_le_expected_sub (nu : Measure V) [IsProbabilityMeasure nu]
    {Y Z : V→ℝ} (hY : Integrable Y nu) (hZ : Integrable Z nu)
    (hb : ∀ᵐv∂nu,1≤Z v ∧ Z v≤Y v) {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) :
    0≤(∫v,(Y v)^p ∂nu)-(∫v,(Z v)^p ∂nu) ∧
      (∫v,(Y v)^p ∂nu)-(∫v,(Z v)^p ∂nu)≤p*(∫v,Y v-Z v ∂nu) := by
  have hZ1 := hb.mono (fun _ hv => hv.1)
  have hY1 := hb.mono (fun _ hv => hv.1.trans hv.2)
  have hi := (power_integrable_of_one_le nu hY hY1 hp1).sub (power_integrable_of_one_le nu hZ hZ1 hp1)
  rw [← integral_sub (power_integrable_of_one_le nu hY hY1 hp1) (power_integrable_of_one_le nu hZ hZ1 hp1)]
  refine ⟨integral_nonneg_of_ae (hb.mono (fun _ hv => sub_nonneg.mpr
    (Real.rpow_le_rpow (zero_le_one.trans hv.1) hv.2 hp0))),?_⟩
  have H := integral_mono_ae hi ((hY.sub hZ).const_mul p) (hb.mono (fun v hv => by
    have H := abs_rpow_sub_le hp0 hp1 hv.1 (hv.1.trans hv.2)
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (zero_le_one.trans hv.1) hv.2 hp0)),
      abs_of_nonneg (sub_nonneg.mpr hv.2)] at H
    exact H))
  change (∫v,(Y v)^p-(Z v)^p ∂nu)≤∫v,p*(Y v-Z v) ∂nu at H
  rw [integral_const_mul] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.NumeratorMarkClippingMeasure
