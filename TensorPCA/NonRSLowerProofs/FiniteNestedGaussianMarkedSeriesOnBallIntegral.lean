-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesIntegral

/-! Coefficientwise integration on a fixed ball. Each induction step uses the child
expansion at the same specified radius, without extending it beyond the supplied
ball.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesOnBallIntegral
open MeasureTheory ProbabilityTheory Filter Set
open FiniteNestedGaussianMarkedSeriesIntegral
open scoped Topology NNReal ENNReal
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem integral_series_on_ball (nu : Measure V) [IsProbabilityMeasure nu]
    {c : ℕ→V→ℝ} (hc : ∀n,Measurable (c n)) {a : ℝ} (ha : 0≤a)
    (hb : ∀n v,|c n v|≤a^n) {f : ℝ→V→ℝ}
    (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1)
    (hs : ∀v,HasFPowerSeriesOnBall (fun t => f t v)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => c n v)) 0 R) :
    HasFPowerSeriesOnBall (fun t => ∫v,f t v ∂nu) (integralSeries nu c) 0 R := by
  refine ⟨?_,by exact_mod_cast hR,?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    rw [integralSeries,FormalMultilinearSeries.ofScalars_norm,Real.norm_eq_abs]
    calc
      _ ≤ a^n*(R : ℝ)^n := mul_le_mul_of_nonneg_right (coefficient_integral_abs_le nu hc hb n) (pow_nonneg R.coe_nonneg n)
      _ = (a*(R : ℝ))^n := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg ha R.coe_nonneg) hAR.le
  · intro t ht
    have htR : |t|<(R : ℝ) := by
      rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
      exact ht
    have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
    have hg : Summable (fun n : ℕ => (|t| *a)^n) :=
      summable_geometric_of_lt_one (mul_nonneg (abs_nonneg _) ha) hta
    have H := hasSum_integral_of_dominated_convergence (μ := nu)
      (F := fun n v => c n v*t^n) (f := f t) (fun n _ => (|t| *a)^n)
      (fun n => ((hc n).mul_const (t^n)).aestronglyMeasurable)
      (fun n => ae_of_all _ (fun v => by
        rw [norm_mul,norm_pow,Real.norm_eq_abs,Real.norm_eq_abs]
        calc
          _ ≤ a^n*|t|^n := mul_le_mul_of_nonneg_right (hb n v) (pow_nonneg (abs_nonneg _) n)
          _ = _ := by rw [← mul_pow,mul_comm]))
      (ae_of_all _ (fun _ => hg)) (integrable_const _)
      (ae_of_all _ (fun v => by
        simpa only [FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,zero_add] using (hs v).hasSum ht))
    convert H using 1
    · funext n
      rw [integralSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,integral_mul_const]
    · simp only [zero_add]

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesOnBallIntegral
