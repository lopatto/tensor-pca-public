-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingMeasure
public import Mathlib.Analysis.Convex.Integral

/-! A mass-uniform positive lower bound for compensation power means. Both the original
and clipped means are bounded below by exp(-E|log Y|). This uses Jensen and
integrability, without a lower margin on the mass.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingJensen
open MeasureTheory ProbabilityTheory Set
open CompensationMarkClippingScalar CompensationMarkClippingMeasure
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem power_mean_lower (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hpos : ∀ᵐv∂nu,0<Y v)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {alpha : ℝ} (ha0 : 0≤alpha) (ha1 : alpha≤1)
    (hpow : Integrable (fun v => (Y v)^alpha) nu) :
    Real.exp (-(∫v,|Real.log (Y v)| ∂nu))≤∫v,(Y v)^alpha ∂nu := by
  have heq : (fun v => Real.exp (alpha*Real.log (Y v)))=ᵐ[nu]fun v => (Y v)^alpha := by
    filter_upwards [hpos] with v hv
    rw [Real.rpow_def_of_pos hv,mul_comm]
  have hExp : Integrable (fun v => Real.exp (alpha*Real.log (Y v))) nu :=
    hpow.congr heq.symm
  have hJ : Real.exp (∫v,alpha*Real.log (Y v) ∂nu)≤
      ∫v,Real.exp (alpha*Real.log (Y v)) ∂nu :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all nu (fun _ => mem_univ _)) (hlog.const_mul alpha) hExp
  have hbound : -(∫v,|Real.log (Y v)| ∂nu)≤∫v,alpha*Real.log (Y v) ∂nu := by
    rw [← integral_neg]
    apply integral_mono hlog.abs.neg (hlog.const_mul alpha)
    intro v
    have H : |alpha*Real.log (Y v)|≤|Real.log (Y v)| := by
      rw [abs_mul,abs_of_nonneg ha0]
      exact mul_le_of_le_one_left (abs_nonneg _) ha1
    exact (neg_le_neg H).trans (neg_abs_le _)
  calc
    _ ≤ Real.exp (∫v,alpha*Real.log (Y v) ∂nu) := Real.exp_le_exp.mpr hbound
    _ ≤ _ := hJ.trans_eq (integral_congr_ae heq)

theorem common_power_mean_lower (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) (hpos : ∀ᵐv∂nu,0<Y v)
    (hY2 : Integrable (fun v => (Y v)^2) nu)
    (hlog : Integrable (fun v => Real.log (Y v)) nu)
    {b L alpha : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    let m := Real.exp (-(∫v,|Real.log (Y v)| ∂nu))
    0<m ∧ m≤1 ∧ m≤(∫v,(Y v)^alpha ∂nu) ∧
      m≤(∫v,(max b (min (Y v) L))^alpha ∂nu) := by
  dsimp only
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg (fun _ => abs_nonneg _))),
    power_mean_lower nu hpos hlog ha0 ha1 (power_integrable nu hY hpos hY2 ha0 ha1),?_⟩
  have hclip := power_mean_lower nu (ae_of_all nu (fun _ => clipped_pos hb))
    (clipped_log_integrable nu hY hpos hlog hb hb1 hL) ha0 ha1
    (clipped_power_integrable nu hY hb hb1 hL ha0 ha1)
  exact (Real.exp_le_exp.mpr (neg_le_neg (clipped_abs_log_integral_le nu hY hpos hlog hb hb1 hL))).trans hclip

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingJensen
