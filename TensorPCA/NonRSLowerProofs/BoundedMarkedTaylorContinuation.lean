-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedTransformAnalytic

/-! Analytic continuation of the canonical scalar Taylor series from a
coefficient bound. Both analyticity across the ball and the coefficient
bound are required; smooth jets alone are not used as a value identity. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedTaylorContinuation
open Filter Set
open scoped Topology NNReal ENNReal
noncomputable section

theorem hasFPowerSeriesOnBall_of_coefficient_bound {f : ℝ→ℝ} {a : ℝ} (ha : 0≤a)
    (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)≤1)
    (hF : AnalyticOnNhd ℝ f (Metric.eball 0 R))
    (hcoeff : ∀n : ℕ,|iteratedDeriv n f 0/(n.factorial : ℝ)|≤a^n) :
    HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n f 0/(n.factorial : ℝ))) 0 R := by
  let p := FormalMultilinearSeries.ofScalars ℝ (fun n => iteratedDeriv n f 0/(n.factorial : ℝ))
  have hr : (R : ℝ≥0∞)≤p.radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    dsimp only [p]
    rw [FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs]
    calc
      _ ≤ a^n*(R : ℝ)^n := mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg R.coe_nonneg n)
      _ = (a*(R : ℝ))^n := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg ha R.coe_nonneg) hAR
  have hR' : (0 : ℝ≥0∞)<R := by exact_mod_cast hR
  have H := (p.hasFPowerSeriesOnBall (hR'.trans_le hr)).mono hR' hr
  have hzero : (0 : ℝ)∈Metric.eball 0 (R : ℝ≥0∞) := by simpa using hR'
  have HF : HasFPowerSeriesAt f p 0 := (hF 0 hzero).hasFPowerSeriesAt
  have heq : f =ᶠ[𝓝 0] p.sum := by
    filter_upwards [HF.eventually_hasSum] with t ht
    change f t=∑'n : ℕ,p n (fun _ => t)
    simpa only [zero_add] using ht.tsum_eq.symm
  have hconnected : IsPreconnected (Metric.eball (0 : ℝ) (R : ℝ≥0∞)) := by
    rw [Metric.eball_coe]
    exact (convex_ball (0 : ℝ) (R : ℝ)).isPreconnected
  have HE := hF.eqOn_of_preconnected_of_eventuallyEq H.analyticOnNhd hconnected hzero heq
  exact H.congr HE.symm

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedTaylorContinuation
