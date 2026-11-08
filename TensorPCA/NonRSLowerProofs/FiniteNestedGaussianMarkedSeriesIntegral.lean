-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedIntegralAnalytic

/-! Coefficientwise integration of a uniformly geometric scalar power series in the
nested Gaussian marking induction. The hypothesis is a pointwise HasSum statement;
formal coefficient identities or smooth derivatives alone do not suffice.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesIntegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
noncomputable section
variable {V : Type*} [MeasurableSpace V]

def integralSeries (nu : Measure V) (c : ℕ→V→ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => ∫v,c n v ∂nu)

theorem coefficient_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {c : ℕ→V→ℝ} (hc : ∀n,Measurable (c n)) {a : ℝ}
    (hb : ∀n v,|c n v|≤a^n) (n : ℕ) : Integrable (c n) nu :=
  Integrable.of_bound (hc n).aestronglyMeasurable (a^n)
    (ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs] using hb n v))

theorem coefficient_integral_abs_le (nu : Measure V) [IsProbabilityMeasure nu]
    {c : ℕ→V→ℝ} (hc : ∀n,Measurable (c n)) {a : ℝ}
    (hb : ∀n v,|c n v|≤a^n) (n : ℕ) : |∫v,c n v ∂nu|≤a^n := by
  have H := integral_mono (coefficient_integrable nu hc hb n).abs (integrable_const (a^n)) (hb n)
  have HI : |∫v,c n v ∂nu|≤∫v,|c n v| ∂nu := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := c n) (μ := nu)
  exact HI.trans (by simpa only [integral_const,probReal_univ,one_smul] using H)

theorem integral_hasSum (nu : Measure V) [IsProbabilityMeasure nu]
    {c : ℕ→V→ℝ} (hc : ∀n,Measurable (c n)) {a : ℝ} (ha : 0≤a)
    (hb : ∀n v,|c n v|≤a^n) {f : ℝ→V→ℝ}
    (hs : ∀t,|t| *a<1→∀v,HasSum (fun n : ℕ => c n v*t^n) (f t v))
    {t : ℝ} (ht : |t| *a<1) :
    HasSum (fun n : ℕ => (integralSeries nu c) n (fun _ => t)) (∫v,f t v ∂nu) := by
  have hg : Summable (fun n : ℕ => (|t| *a)^n) :=
    summable_geometric_of_lt_one (mul_nonneg (abs_nonneg _) ha) ht
  have H := hasSum_integral_of_dominated_convergence (μ := nu)
    (F := fun n v => c n v*t^n) (f := f t) (fun n _ => (|t| *a)^n)
    (fun n => ((hc n).mul_const (t^n)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun v => by
      rw [norm_mul,norm_pow,Real.norm_eq_abs,Real.norm_eq_abs]
      calc
        _ ≤ a^n*|t|^n := mul_le_mul_of_nonneg_right (hb n v) (pow_nonneg (abs_nonneg _) n)
        _ = _ := by rw [← mul_pow,mul_comm]))
    (ae_of_all _ (fun _ => hg)) (integrable_const _)
    (ae_of_all _ (hs t ht))
  convert H using 1
  funext n
  rw [integralSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,integral_mul_const]

theorem integral_hasFPowerSeriesOnBall (nu : Measure V) [IsProbabilityMeasure nu]
    {c : ℕ→V→ℝ} (hc : ∀n,Measurable (c n)) {a : ℝ} (ha : 0≤a)
    (hb : ∀n v,|c n v|≤a^n) {f : ℝ→V→ℝ}
    (hs : ∀t,|t| *a<1→∀v,HasSum (fun n : ℕ => c n v*t^n) (f t v))
    (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1) :
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
    simpa only [zero_add] using integral_hasSum nu hc ha hb hs hta

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedSeriesIntegral
