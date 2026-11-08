-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperatureKernel
public import TensorPCA.NonRSLowerProofs.FiniteCSTruncationProofs
public import TensorPCA.LandscapeVariationalUpperProofs
/-! Uniform comparison of the extended finite-temperature CS minimum with the zero-
temperature variational infimum. Singular baseline entropy is compared additively in
ENNReal, avoiding subtraction of infinite quantities.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperature
open Set Filter MeasureTheory
open FiniteCS
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem shifted_reciprocal_integral_le (k : ℕ) {beta m delta : ℝ}
    (hbeta : 0 < beta) (nu : Trial) (hfinite : rawFunctional k beta m nu ≠ ∞)
    (hd : 0 < delta) :
    (∫ t in (0 : ℝ)..1, 1/(profile beta nu t+delta)) ≤
      (entropy beta nu).toReal+Real.log ((beta+delta)/delta)/beta := by
  let f : ℝ → ℝ := fun t ↦ 1/(profile beta nu t+delta)
  let g : ℝ → ℝ := fun t ↦ 1/(beta*(1-t)+delta)
  have hp := profile_add_admissible hbeta.le nu hd
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hp.1 (fun t ht ↦ (hp.2.2.2 t ht).ne')
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (add_pos_of_nonneg_of_pos (mul_nonneg hbeta.le (sub_nonneg.mpr ht.2)) hd).ne'
  have hfi : IntegrableOn f (Ico (0 : ℝ) 1) := hfc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hgi : IntegrableOn g (Ico (0 : ℝ) 1) := hgc.integrableOn_Icc.mono_set Ico_subset_Icc_self
  have hfn : 0 ≤ᵐ[volume.restrict (Ico (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact (one_div_pos.mpr (hp.2.2.2 t ⟨ht.1, ht.2.le⟩)).le
  have hgn : 0 ≤ᵐ[volume.restrict (Ico (0 : ℝ) 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact (one_div_pos.mpr (add_pos (mul_pos hbeta (sub_pos.mpr ht.2)) hd)).le
  have hpoint : ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1),
      ENNReal.ofReal (f t) ≤ entropyExcess beta nu t+ENNReal.ofReal (g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    have hpt := profile_pos_of_rawFunctional_ne_top k hbeta m nu hfinite ht
    have hpb := (profile_bounds hbeta.le nu ⟨ht.1, ht.2.le⟩).2
    have hEx := entropyExcess_real_nonneg hbeta nu ht hpt
    have hBase : 0 ≤ g t := (one_div_pos.mpr
      (add_pos (mul_pos hbeta (sub_pos.mpr ht.2)) hd)).le
    rw [entropyExcess_eq_ofReal hbeta nu ht hpt,
      ← ENNReal.ofReal_add hEx hBase]
    apply ENNReal.ofReal_le_ofReal
    simpa only [f, g, one_div] using reciprocal_shift_le hpt hpb hd
  have H := lintegral_mono_ae hpoint
  rw [lintegral_add_left (entropyExcess_measurable beta nu)] at H
  change (∫⁻ t in Ico (0 : ℝ) 1, ENNReal.ofReal (f t)) ≤
    entropy beta nu+(∫⁻ t in Ico (0 : ℝ) 1, ENNReal.ofReal (g t)) at H
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hfn,
    ← ofReal_integral_eq_lintegral_ofReal hgi hgn] at H
  have hEntropy : entropy beta nu ≠ ∞ := (ENNReal.add_ne_top.mp hfinite).2
  have HR := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hEntropy, ENNReal.ofReal_ne_top⟩) H
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hfn),
    ENNReal.toReal_add hEntropy ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hgn)] at HR
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one] at HR
  simpa only [f, g, baseline_integral hbeta hd] using HR

private theorem energy_toReal_eq_integral (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 ≤ beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) :
    (energy k beta m nu).toReal =
      (∫ t in (0 : ℝ)..1, deriv (deriv (Scalar.xiSlice k m)) t*profile beta nu t)+
        deriv (Scalar.xiSlice k m) 0*profile beta nu 0 := by
  have H := integral_mono (slice_covariance_integrable k m nu)
    (integrable_const (Scalar.xiSlice k m 1)) (slice_covariance_le_one k hm)
  simp only [integral_const, probReal_univ, one_smul] at H
  have hn := mul_nonneg hbeta (sub_nonneg.mpr H)
  rw [energy_eq_ofReal k hk hbeta hm nu, ENNReal.toReal_ofReal hn]
  exact (energy_real_integral_eq k hk beta m nu).symm

theorem shifted_parisiFunctional_eq (k : ℕ) (hk : 1 ≤ k) {beta m delta : ℝ}
    (hbeta : 0 ≤ beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) (hd : 0 < delta) :
    Scalar.parisiFunctional (Scalar.xiSlice k m) 0 (fun t ↦ profile beta nu t+delta) =
      (energy k beta m nu).toReal+delta*deriv (Scalar.xiSlice k m) 1+
        (∫ t in (0 : ℝ)..1, 1/(profile beta nu t+delta)) := by
  let xi := Scalar.xiSlice k m
  let p := profile beta nu
  let w := deriv (deriv xi)
  have hw : Continuous w := continuous_secondDeriv_slice k m
  have hp : Continuous p := profile_continuous beta nu
  have hpos := profile_add_admissible hbeta nu hd
  have hwp : IntervalIntegrable (fun t ↦ w t*p t) volume 0 1 :=
    (hw.mul hp).intervalIntegrable 0 1
  have hwi : IntervalIntegrable w volume 0 1 := hw.intervalIntegrable 0 1
  have hinv : IntervalIntegrable (fun t ↦ 1/(p t+delta)) volume 0 1 :=
    (continuousOn_const.div hpos.1
      (fun t ht ↦ (hpos.2.2.2 t ht).ne')).intervalIntegrable_of_Icc zero_le_one
  have hFTC : (∫ t in (0 : ℝ)..1, w t) = deriv xi 1-deriv xi 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hwi
    intro t ht
    exact (VariationalProofs.hasDerivAt_deriv_xiSlice hk m t).differentiableAt.hasDerivAt
  have hIntegral : (∫ t in (0 : ℝ)..1, w t*(p t+delta)+1/(p t+delta)) =
      (∫ t in (0 : ℝ)..1, w t*p t)+delta*(∫ t in (0 : ℝ)..1, w t)+
        (∫ t in (0 : ℝ)..1, 1/(p t+delta)) := by
    have heq : (fun t ↦ w t*(p t+delta)+1/(p t+delta)) =
        fun t ↦ (w t*p t+delta*w t)+1/(p t+delta) := by funext t; ring
    rw [heq, intervalIntegral.integral_add (hwp.add (hwi.const_mul delta)) hinv,
      intervalIntegral.integral_add hwp (hwi.const_mul delta), intervalIntegral.integral_const_mul]
  change (∫ t in (0 : ℝ)..1, w t*(p t+delta)+1/(p t+delta))+
    (0^2+deriv xi 0)*(p 0+delta) = _
  rw [hIntegral, hFTC, energy_toReal_eq_integral k hk hbeta hm nu]
  change _ = ((∫ t in (0 : ℝ)..1, w t*p t)+deriv xi 0*p 0)+
    delta*deriv xi 1+(∫ t in (0 : ℝ)..1, 1/(p t+delta))
  ring

theorem variational_le_rawFunctional (k : ℕ) (hk : 3 ≤ k) {beta m delta : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial)
    (hfinite : rawFunctional k beta m nu ≠ ∞) (hd : 0 < delta) :
    2*Scalar.variationalValue (Scalar.xiSlice k m) 0 ≤
      (rawFunctional k beta m nu).toReal+delta*deriv (Scalar.xiSlice k m) 1+
        Real.log ((beta+delta)/delta)/beta := by
  have hG := LandscapeVariationalUpperProofs.xiSlice_variationalValue_le_half_functional
    k hk hm (profile_add_admissible hbeta.le nu hd)
  rw [shifted_parisiFunctional_eq k (by omega) hbeta.le hm nu hd] at hG
  have hEntropy := shifted_reciprocal_integral_le k hbeta nu hfinite hd
  have hparts := ENNReal.add_ne_top.mp hfinite
  have hraw : (rawFunctional k beta m nu).toReal =
      (energy k beta m nu).toReal+(entropy beta nu).toReal :=
    ENNReal.toReal_add hparts.1 hparts.2
  rw [hraw]
  nlinarith

theorem variational_le_rawValue (k : ℕ) (hk : 3 ≤ k) {beta m delta : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (hd : 0 < delta) :
    2*Scalar.variationalValue (Scalar.xiSlice k m) 0 ≤
      (rawValue k beta m).toReal+delta*deriv (Scalar.xiSlice k m) 1+
        Real.log ((beta+delta)/delta)/beta := by
  obtain ⟨nu, heq, hfinite, hmin⟩ := exists_finite_minimizer k beta m
  have H := variational_le_rawFunctional k hk hbeta hm nu hfinite hd
  rwa [heq] at H

theorem variational_le_rawValue_uniform_error (k : ℕ) (hk : 3 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) :
    2*Scalar.variationalValue (Scalar.xiSlice k m) 0 ≤
      (rawValue k beta m).toReal+
        (deriv (Scalar.xiSlice k m) 1+Real.log (1+beta^2))/beta := by
  have H := variational_le_rawValue k hk hbeta hm (one_div_pos.mpr hbeta)
  have hratio : (beta+1/beta)/(1/beta) = 1+beta^2 := by field_simp [hbeta.ne'] <;> ring
  rw [hratio] at H
  calc
    _ ≤ (rawValue k beta m).toReal+(1/beta)*deriv (Scalar.xiSlice k m) 1+
        Real.log (1+beta^2)/beta := H
    _ = _ := by ring


end
end TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperature
