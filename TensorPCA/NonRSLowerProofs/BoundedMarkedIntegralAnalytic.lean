-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialSeries
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedIIDMarkedMoments

/-! A power series for the bounded mark integral, obtained by dominated summation of the
standard binomial series. This supplies analytic regularity on a ball larger than
the evaluation interval when a<1.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedIntegralAnalytic
open MeasureTheory ProbabilityTheory Filter Set
open BoundedMarkedPowerTransform FiniteDiscountedIIDMarkedMoments
open BoundedMarkedBinomialCoefficients BoundedMarkedBinomialSeries
open scoped BigOperators Topology NNReal ENNReal
noncomputable section
variable {V : Type*} [MeasurableSpace V]

def markIntegralSeries (nu : Measure V) (Z : V→ℝ) (alpha : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n =>
    (((-1 : ℝ)^n*(descPochhammer ℝ n).eval alpha)/(n.factorial : ℝ))*(∫v,(Z v)^n ∂nu))

theorem markIntegralSeries_norm_le (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha : ℝ} (ha : 0≤a) (h0 : 0≤alpha) (h1 : alpha≤1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (n : ℕ) :
    ‖markIntegralSeries nu Z alpha n‖≤a^n := by
  rw [markIntegralSeries,FormalMultilinearSeries.ofScalars_norm,norm_mul,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_nonneg (bounded_mark_moment_mem nu hZ ha hb n).1]
  calc
    _ ≤ 1*a^n := mul_le_mul (signed_falling_coefficient_abs_le_one h0 h1 n)
      (bounded_mark_moment_mem nu hZ ha hb n).2
      (bounded_mark_moment_mem nu hZ ha hb n).1 zero_le_one
    _ = _ := one_mul _

theorem markTransform_hasSum (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha t : ℝ} (ha : 0≤a) (h0 : 0≤alpha) (h1 : alpha≤1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (ht : |t| *a<1) :
    HasSum (fun n : ℕ => markIntegralSeries nu Z alpha n (fun _ => t))
      (markTransform nu Z alpha t) := by
  let c : ℕ→ℝ := fun n => ((-1 : ℝ)^n*(descPochhammer ℝ n).eval alpha)/(n.factorial : ℝ)
  have hg : Summable (fun n : ℕ => (|t| *a)^n) :=
    summable_geometric_of_lt_one (mul_nonneg (abs_nonneg t) ha) ht
  have H := hasSum_integral_of_dominated_convergence
    (μ := nu) (F := fun n v => c n*(t*Z v)^n) (f := fun v => (1-t*Z v)^alpha)
    (fun (n : ℕ) (_ : V) => (|t| *a)^n)
    (fun n => ((hZ.const_mul t).pow_const n).const_mul (c n) |>.aestronglyMeasurable)
    (fun n => hb.mono (fun v hv => by
      rw [norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs,abs_mul,abs_of_nonneg hv.1]
      calc
        _ ≤ 1*(|t| *a)^n := mul_le_mul (signed_falling_coefficient_abs_le_one h0 h1 n)
          (pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) hv.1)
            (mul_le_mul_of_nonneg_left hv.2 (abs_nonneg t)) n)
          (pow_nonneg (mul_nonneg (abs_nonneg t) hv.1) n) zero_le_one
        _ = _ := one_mul _))
    (Eventually.of_forall (fun _ => hg)) (integrable_const _)
    (hb.mono (fun v hv => signed_binomial_hasSum alpha (by
      rw [abs_mul,abs_of_nonneg hv.1]
      exact (mul_le_mul_of_nonneg_left hv.2 (abs_nonneg t)).trans_lt ht)))
  convert H using 1
  · funext n
    rw [markIntegralSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]
    simp only [mul_pow]
    rw [← integral_const_mul,← integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by dsimp only [c]; ring)
  · rfl

theorem markTransform_hasFPowerSeriesOnBall (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {a alpha : ℝ} (ha : 0≤a) (h0 : 0≤alpha) (h1 : alpha≤1)
    (hb : ∀ᵐv∂nu,0≤Z v ∧ Z v≤a) (R : ℝ≥0) (hR : 0<R) (hAR : a*(R : ℝ)<1) :
    HasFPowerSeriesOnBall (markTransform nu Z alpha) (markIntegralSeries nu Z alpha) 0 R := by
  refine ⟨?_,by exact_mod_cast hR,?_⟩
  · apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    calc
      ‖markIntegralSeries nu Z alpha n‖*(R : ℝ)^n ≤ a^n*(R : ℝ)^n :=
        mul_le_mul_of_nonneg_right (markIntegralSeries_norm_le nu hZ ha h0 h1 hb n)
          (pow_nonneg R.coe_nonneg n)
      _ = (a*(R : ℝ))^n := (mul_pow _ _ _).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg ha R.coe_nonneg) hAR.le
  · intro t ht
    have htR : |t|<(R : ℝ) := by
      rw [Metric.eball_coe,Metric.mem_ball,Real.dist_eq,sub_zero] at ht
      exact ht
    have hta : |t| *a<1 := (mul_le_mul_of_nonneg_right htR.le ha).trans_lt (by simpa only [mul_comm] using hAR)
    simpa only [zero_add] using markTransform_hasSum nu hZ ha h0 h1 hb hta

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedIntegralAnalytic
