-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSDefinitions
public import TensorPCA.PureVariationalProofs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! Uniform positive-floor comparison for finite-temperature CS profiles. The finite-
temperature terminal value is retained until the explicit positive shift is added.
No optimizer compactness or limiting minimizer is used.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperature
open Set MeasureTheory Filter
open FiniteCS
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem reciprocal_shift_le {p b delta : ℝ} (hp : 0 < p) (hpb : p ≤ b)
    (hd : 0 < delta) :
    1/(p+delta) ≤ (1/p-1/b)+1/(b+delta) := by
  have hb : 0 < b := hp.trans_le hpb
  have hp' : 0 < p+delta := add_pos hp hd
  have hb' : 0 < b+delta := add_pos hb hd
  have hden : p*(p+delta) ≤ b*(b+delta) :=
    mul_le_mul hpb (add_le_add hpb le_rfl) hp'.le hb.le
  have H := div_le_div_of_nonneg_left hd.le (mul_pos hp hp') hden
  have heqP : delta/(p*(p+delta)) = 1/p-1/(p+delta) := by
    field_simp [hp.ne', hp'.ne'] <;> ring
  have heqB : delta/(b*(b+delta)) = 1/b-1/(b+delta) := by
    field_simp [hb.ne', hb'.ne'] <;> ring
  rw [heqP, heqB] at H
  linarith

theorem baseline_integral {beta delta : ℝ} (hbeta : 0 < beta) (hd : 0 < delta) :
    (∫ t in (0 : ℝ)..1, 1/(beta*(1-t)+delta)) =
      Real.log ((beta+delta)/delta)/beta := by
  have hfun : (fun t : ℝ ↦ 1/(beta*(1-t)+delta)) =
      fun t ↦ 1/PureVariationalProofs.affineProfile delta beta t := by
    funext t
    unfold PureVariationalProofs.affineProfile
    congr 1
    ring
  rw [hfun, PureVariationalProofs.integral_inv_affineProfile hd hbeta]
  rw [add_comm delta beta]

theorem profile_add_admissible {beta delta : ℝ} (hbeta : 0 ≤ beta)
    (nu : Trial) (hd : 0 < delta) :
    Scalar.AdmissibleProfile (fun t ↦ profile beta nu t+delta) := by
  have hc : Continuous (profile beta nu) := by
    change Continuous (fun t ↦ beta*hatCDF (nu : Measure Overlap) t)
    exact continuous_const.mul (hatCDF_continuous _)
  refine ⟨(hc.add continuous_const).continuousOn, ?_, ?_, ?_⟩
  · intro t ht u hu htu
    exact add_le_add (scaled_hatCDF_antitone (nu : Measure Overlap) hbeta htu) le_rfl
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro t ht u hu alpha gamma halpha hgamma hsum
    have H := (scaled_hatCDF_concave (nu : Measure Overlap) hbeta).2
      (mem_univ t) (mem_univ u) halpha hgamma hsum
    change alpha*profile beta nu t+gamma*profile beta nu u ≤
      profile beta nu (alpha*t+gamma*u) at H
    change alpha*(profile beta nu t+delta)+gamma*(profile beta nu u+delta) ≤
      profile beta nu (alpha*t+gamma*u)+delta
    have hdSum : alpha*delta+gamma*delta = delta := by rw [← add_mul, hsum, one_mul]
    nlinarith
  · intro t ht
    exact add_pos_of_nonneg_of_pos (scaled_hatCDF_bounds (nu : Measure Overlap) hbeta ht).1 hd

theorem baseline_inverse_beta {beta : ℝ} (hbeta : 0 < beta) :
    (∫ t in (0 : ℝ)..1, 1/(beta*(1-t)+1/beta)) = Real.log (1+beta^2)/beta := by
  rw [baseline_integral hbeta (one_div_pos.mpr hbeta)]
  congr 2
  field_simp [hbeta.ne'] <;> ring

theorem tendsto_log_one_add_sq_div_atTop :
    Tendsto (fun beta : ℝ ↦ Real.log (1+beta^2)/beta) atTop (𝓝 (0 : ℝ)) := by
  have hlog : Tendsto (fun beta : ℝ ↦ Real.log (1+beta)/beta) atTop (𝓝 (0 : ℝ)) := by
    have H := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    apply H.congr'
    filter_upwards with beta
    simp only [pow_one, one_mul, Function.comp_def, id_eq]
    congr 1
    ring
  have hup : Tendsto (fun beta : ℝ ↦ 2*(Real.log (1+beta)/beta)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hlog.const_mul 2
  apply squeeze_zero' _ _ hup
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hb
    exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg beta])) hb.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with beta hb
    have hmono : Real.log (1+beta^2) ≤ 2*Real.log (1+beta) := by
      have H := Real.log_le_log (by positivity : (0 : ℝ) < 1+beta^2)
        (by nlinarith : 1+beta^2 ≤ (1+beta)^2)
      simpa only [Real.log_pow, Nat.cast_ofNat] using H
    have H := div_le_div_of_nonneg_right hmono hb.le
    simpa only [mul_div_assoc] using H

theorem tendsto_uniform_error (c : ℝ) :
    Tendsto (fun beta : ℝ ↦ (c+Real.log (1+beta^2))/beta) atTop (𝓝 (0 : ℝ)) := by
  have hconst : Tendsto (fun beta : ℝ ↦ c/beta) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have H := hconst.add tendsto_log_one_add_sq_div_atTop
  simpa only [zero_add, ← add_div] using H


end
end TensorPCA.NonRSLowerProofs.FiniteCSZeroTemperature
