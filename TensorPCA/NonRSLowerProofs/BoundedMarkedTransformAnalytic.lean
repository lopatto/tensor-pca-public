-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedIntegralAnalytic
public import Mathlib.Analysis.Analytic.Uniqueness

/-! Strict positivity and analytic power/logarithm compositions of the bounded mark
integral throughout its positive-base ball.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedTransformAnalytic
open MeasureTheory ProbabilityTheory Filter Set
open BoundedMarkedPowerTransform BoundedMarkedIntegralAnalytic
open scoped Topology NNReal ENNReal
noncomputable section
variable {V : Type*} [MeasurableSpace V]

private theorem base_bounds {a t z : ℝ} (hz : 0≤z ∧ z≤a) :
    1-|t| *a≤1-t*z ∧ 1-t*z≤1+|t| *a := by
  have H : |t*z|≤|t| *a := by rw [abs_mul,abs_of_nonneg hz.1]; exact mul_le_mul_of_nonneg_left hz.2 (abs_nonneg t)
  have HS := abs_le.mp H
  constructor <;> linarith only [HS.1,HS.2]

theorem markTransform_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha t : ℝ} (ha : 0≤a) (h0 : 0≤alpha)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (ht : |t| *a<1) :
    Integrable (fun v => (1-t*Z v)^alpha) nu := by
  have hm : Measurable (fun v => (1-t*Z v)^alpha) :=
    (measurable_const.sub (hZ.const_mul t)).pow_const alpha
  apply Integrable.of_bound hm.aestronglyMeasurable ((1+|t| *a)^alpha)
  filter_upwards [hb] with v hv
  have H := base_bounds (t := t) hv
  have hbase : 0≤1-t*Z v := by linarith only [H.1,ht]
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hbase alpha)]
  exact Real.rpow_le_rpow hbase H.2 h0

theorem markTransform_pos (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha t : ℝ} (ha : 0≤a) (h0 : 0≤alpha)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (ht : |t| *a<1) :
    0<markTransform nu Z alpha t := by
  have hbase : 0<1-|t| *a := sub_pos.mpr ht
  have H := integral_mono_ae (integrable_const ((1-|t| *a)^alpha))
    (markTransform_integrable nu hZ ha h0 hb ht)
    (hb.mono (fun v hv => Real.rpow_le_rpow hbase.le (base_bounds (t := t) hv).1 h0))
  have H' : (1-|t| *a)^alpha≤markTransform nu Z alpha t := by
    simpa only [integral_const,probReal_univ,one_smul,markTransform] using H
  exact (Real.rpow_pos_of_pos hbase alpha).trans_le H'

theorem power_markTransform_analyticOnNhd (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha : ℝ} (ha : 0≤a) (h0 : 0≤alpha) (h1 : alpha≤1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1) (q : ℝ) :
    AnalyticOnNhd ℝ (fun t : ℝ => (markTransform nu Z alpha t)^q) (Metric.eball 0 R) := by
  have HS := markTransform_hasFPowerSeriesOnBall nu hZ ha h0 h1 hb R hR hAR
  intro t ht
  have HA := HS.analyticAt_of_mem ht
  have htR : |t|<(R : ℝ) := by
    rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
    exact ht
  have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
  have hp := markTransform_pos nu hZ ha h0 hb hta
  have HL : AnalyticAt ℝ (fun s => Real.log (markTransform nu Z alpha s)*q) t :=
    (HA.log hp).mul analyticAt_const
  have H := HL.rexp'
  apply H.congr
  filter_upwards [HA.continuousAt.eventually (lt_mem_nhds hp)] with s hs
  exact (Real.rpow_def_of_pos hs q).symm

theorem log_markTransform_analyticOnNhd (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha : ℝ} (ha : 0≤a) (h0 : 0≤alpha) (h1 : alpha≤1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1) :
    AnalyticOnNhd ℝ (fun t : ℝ => Real.log (markTransform nu Z alpha t)/alpha) (Metric.eball 0 R) := by
  have HS := markTransform_hasFPowerSeriesOnBall nu hZ ha h0 h1 hb R hR hAR
  intro t ht
  have htR : |t|<(R : ℝ) := by
    rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
    exact ht
  have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
  exact ((HS.analyticAt_of_mem ht).log (markTransform_pos nu hZ ha h0 hb hta)).div_const

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedTransformAnalytic
