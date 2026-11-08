-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingMeasure
public import TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform

/-! A bounded deficit for clipped positive marks, providing the quantities used by the
bounded marked-value estimates. Physical hierarchy moment matching is treated
separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingNormalization
open MeasureTheory ProbabilityTheory
open CompensationMarkClippingScalar BoundedMarkedPowerTransform GGFiniteEmpiricalNormalizer
open scoped BigOperators
noncomputable section
variable {V : Type*} [MeasurableSpace V]

theorem deficit_bounds {b L y : ℝ} (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    0≤1-max b (min y L)/L ∧ 1-max b (min y L)/L≤1-b/L ∧
      0≤1-b/L ∧ 1-b/L<1 := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hc := clipped_le_upper (y := y) hb1 hL
  have hbL := div_le_div_of_nonneg_right (le_max_left b (min y L)) hL0.le
  have hcL := (div_le_one hL0).mpr hc
  have hp := div_pos hb hL0
  have hbL1 := (div_le_one hL0).mpr (hb1.trans hL)
  exact ⟨by linarith only [hcL],by linarith only [hbL],by linarith only [hbL1],by linarith only [hp]⟩

theorem deficit_ae_bounds (nu : Measure V) {Y : V→ℝ} {b L : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) :
    ∀ᵐv∂nu,0≤1-max b (min (Y v) L)/L ∧ 1-max b (min (Y v) L)/L≤1-b/L :=
  ae_of_all _ (fun _ => ⟨(deficit_bounds hb hb1 hL).1,(deficit_bounds hb hb1 hL).2.1⟩)

theorem clipped_power_mean_pos (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) {b L alpha : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0≤alpha) (ha1 : alpha≤1) :
    0<∫v,(max b (min (Y v) L))^alpha ∂nu := by
  have H := integral_mono (integrable_const (b^alpha))
    (CompensationMarkClippingMeasure.clipped_power_integrable nu hY hb hb1 hL ha0 ha1)
    (fun v => Real.rpow_le_rpow hb.le (le_max_left b (min (Y v) L)) ha0)
  simp only [integral_const,probReal_univ,one_smul] at H
  exact (Real.rpow_pos_of_pos hb alpha).trans_le H

theorem markTransform_deficit_eq (nu : Measure V) {Y : V→ℝ} {b L alpha : ℝ}
    (hb : 0<b) (hL : 0<L) :
    markTransform nu (fun v => 1-max b (min (Y v) L)/L) alpha 1=
      (∫v,(max b (min (Y v) L))^alpha ∂nu)/(L^alpha) := by
  unfold markTransform
  have he (v : V) : (1-1*(1-max b (min (Y v) L)/L))^alpha=
      (max b (min (Y v) L))^alpha/(L^alpha) := by
    rw [show 1-1*(1-max b (min (Y v) L)/L)=max b (min (Y v) L)/L by ring]
    exact Real.div_rpow (clipped_pos hb).le hL.le alpha
  simp_rw [he]
  rw [integral_div]

theorem normalized_log_eq_deficit (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) {b L alpha : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) :
    Real.log (∫v,(max b (min (Y v) L))^alpha ∂nu)/alpha=Real.log L+
      Real.log (markTransform nu (fun v => 1-max b (min (Y v) L)/L) alpha 1)/alpha := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hp := clipped_power_mean_pos nu hY hb hb1 hL ha0.le ha1
  rw [markTransform_deficit_eq nu hb hL0,Real.log_div (ne_of_gt hp) (ne_of_gt (Real.rpow_pos_of_pos hL0 alpha)),
    Real.log_rpow hL0 alpha]
  field_simp
  <;> ring

theorem parent_power_eq_deficit (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Measurable Y) {b L alpha : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hL : 1≤L) (ha0 : 0<alpha) (ha1 : alpha≤1) (p : ℝ) :
    (∫v,(max b (min (Y v) L))^alpha ∂nu)^(p/alpha)=L^p*
      (markTransform nu (fun v => 1-max b (min (Y v) L)/L) alpha 1)^(p/alpha) := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hp := clipped_power_mean_pos nu hY hb hb1 hL ha0.le ha1
  rw [markTransform_deficit_eq nu hb hL0,Real.div_rpow hp.le (Real.rpow_nonneg hL0.le _),
    ← Real.rpow_mul hL0.le,show alpha*(p/alpha)=p by field_simp]
  field_simp

theorem empirical_deficit_eq {K : ℕ} (hK : 0<K) (Y : V→ℝ) (s : Fin K→V) (L : ℝ) :
    empiricalMean K (fun v => 1-Y v/L) s=1-empiricalMean K Y s/L := by
  unfold empiricalMean
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [← Finset.sum_div,sub_div,div_self (by exact_mod_cast hK.ne' : (K : ℝ)≠0)]
  ring

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingNormalization
