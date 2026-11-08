-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSTruncationProofs
public import TensorPCA.NonRSLowerProofs.FiniteCSCutoffTransport

/-! Exact transport between the complete extended finite-temperature CS cost
and the ordinary cutoff functional. Positivity, finiteness, and real-valued
equalities are proved, so minimization can be reflected in either direction. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
open RetainedCountProofs.CrisantiSommers

theorem profile_cutoff_tail (beta : ℝ) (nu : Trial) {q t : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) (ht : q ≤ t) :
    profile beta nu t = beta*(1-t) := by
  rw [profile_eq_scaled_xHat_realLaw, xHat_tail (realLaw nu) (realLaw_hasCutoff nu hq hnu) ht]

theorem profile_cutoff_pos {beta : ℝ} (hbeta : 0 < beta) (nu : Trial) {q t : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) (ht : t < 1) :
    0 < profile beta nu t := by
  rw [profile_eq_scaled_xHat_realLaw]
  exact mul_pos hbeta (xHat_pos (realLaw nu) (realLaw_hasCutoff nu hq hnu) ht)

theorem entropyExcess_cutoff_tail (beta : ℝ) (nu : Trial) {q t : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) (ht : q ≤ t) :
    entropyExcess beta nu t = 0 := by
  rw [entropyExcess, profile_cutoff_tail beta nu hq hnu ht, tsub_self]

theorem entropy_cutoff_real_nonneg {beta : ℝ} (hbeta : 0 < beta) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    0 ≤ beta⁻¹*((∫ t in (0 : ℝ)..q, (xHat (realLaw nu) t)⁻¹)+Real.log (1-q)) := by
  let f : ℝ → ℝ := fun t => (profile beta nu t)⁻¹-(beta*(1-t))⁻¹
  have hcut := realLaw_hasCutoff nu hq hnu
  have hX : IntegrableOn (fun t => (xHat (realLaw nu) t)⁻¹) (Icc (0 : ℝ) q) := by
    apply ContinuousOn.integrableOn_Icc
    apply (xHat_continuous (realLaw nu) hcut).continuousOn.inv₀
    intro t ht
    exact (xHat_pos (realLaw nu) hcut (ht.2.trans_lt hq.2)).ne'
  have hBase : IntegrableOn (fun t : ℝ => (1-t)⁻¹) (Icc (0 : ℝ) q) := by
    apply ContinuousOn.integrableOn_Icc
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro t ht
    exact (sub_pos.mpr (ht.2.trans_lt hq.2)).ne'
  have heq : f = fun t => beta⁻¹*((xHat (realLaw nu) t)⁻¹-(1-t)⁻¹) := by
    funext t
    dsimp [f]
    rw [profile_eq_scaled_xHat_realLaw, mul_inv, mul_inv]
    ring
  have hi : IntegrableOn f (Icc (0 : ℝ) q) := by rw [heq]; exact (hX.sub hBase).const_mul _
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) q)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact entropyExcess_real_nonneg hbeta nu ⟨ht.1, ht.2.trans_lt hq.2⟩
      (profile_cutoff_pos hbeta nu hq hnu (ht.2.trans_lt hq.2))
  have H := integral_nonneg_of_ae hn
  rw [heq, integral_const_mul, integral_sub hX hBase,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.1,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.1,
    integral_inverse_one_sub (by norm_num : (0 : ℝ)<1) hq.2] at H
  simpa only [sub_zero, Real.log_one, zero_sub, sub_neg_eq_add] using H

theorem entropy_cutoff_eq_ofReal {beta : ℝ} (hbeta : 0 < beta) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    entropy beta nu = ENNReal.ofReal
      (beta⁻¹*((∫ t in (0 : ℝ)..q, (xHat (realLaw nu) t)⁻¹)+Real.log (1-q))) := by
  let f : ℝ → ℝ := fun t => (profile beta nu t)⁻¹-(beta*(1-t))⁻¹
  have hcut := realLaw_hasCutoff nu hq hnu
  have hf : ContinuousOn f (Icc (0 : ℝ) q) := by
    apply ContinuousOn.sub
    · exact (profile_continuous beta nu).continuousOn.inv₀ (fun t ht =>
        (profile_cutoff_pos hbeta nu hq hnu (ht.2.trans_lt hq.2)).ne')
    · apply (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn.inv₀
      intro t ht
      exact (mul_pos hbeta (sub_pos.mpr (ht.2.trans_lt hq.2))).ne'
  have hi : IntegrableOn f (Icc (0 : ℝ) q) := hf.integrableOn_Icc
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) q)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact entropyExcess_real_nonneg hbeta nu ⟨ht.1, ht.2.trans_lt hq.2⟩
      (profile_cutoff_pos hbeta nu hq hnu (ht.2.trans_lt hq.2))
  have hsub : Icc (0 : ℝ) q ⊆ Ico (0 : ℝ) 1 :=
    fun t ht => ⟨ht.1, ht.2.trans_lt hq.2⟩
  have hext : entropy beta nu = ∫⁻ t in Icc (0 : ℝ) q, ENNReal.ofReal (f t) := by
    unfold entropy
    have HH : (fun t => entropyExcess beta nu t) =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
        (Icc (0 : ℝ) q).indicator (fun t => ENNReal.ofReal (f t)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      by_cases htq : t ≤ q
      · rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) q from ⟨ht.1, htq⟩)]
        exact entropyExcess_eq_ofReal hbeta nu ht (profile_cutoff_pos hbeta nu hq hnu ht.2)
      · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) q from fun h => htq h.2),
          entropyExcess_cutoff_tail beta nu hq hnu (le_of_not_ge htq)]
    rw [lintegral_congr_ae HH, setLIntegral_indicator measurableSet_Icc,
      inter_eq_left.mpr hsub]
  rw [hext, ← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  have hX : IntegrableOn (fun t => (xHat (realLaw nu) t)⁻¹) (Icc (0 : ℝ) q) := by
    apply ContinuousOn.integrableOn_Icc
    apply (xHat_continuous (realLaw nu) hcut).continuousOn.inv₀
    intro t ht
    exact (xHat_pos (realLaw nu) hcut (ht.2.trans_lt hq.2)).ne'
  have hBase : IntegrableOn (fun t : ℝ => (1-t)⁻¹) (Icc (0 : ℝ) q) := by
    apply ContinuousOn.integrableOn_Icc
    apply (continuous_const.sub continuous_id).continuousOn.inv₀
    intro t ht
    exact (sub_pos.mpr (ht.2.trans_lt hq.2)).ne'
  have heq : f = fun t => beta⁻¹*((xHat (realLaw nu) t)⁻¹-(1-t)⁻¹) := by
    funext t
    dsimp [f]
    rw [profile_eq_scaled_xHat_realLaw, mul_inv, mul_inv]
    ring
  rw [heq, integral_const_mul, integral_sub hX hBase,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.1,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hq.1,
    integral_inverse_one_sub (by norm_num : (0 : ℝ)<1) hq.2]
  simp only [sub_zero, Real.log_one, zero_sub, sub_neg_eq_add]

theorem slice_covariance_integral_realLaw (k : ℕ) (m : ℝ) (nu : Trial) :
    (∫ q : Overlap, Scalar.xiSlice k m (q : ℝ) ∂(nu : Measure Overlap)) =
      ∫ q : ℝ, Scalar.xiSlice k m q ∂realLaw nu := by
  unfold realLaw
  rw [integral_map measurable_subtype_coe.aemeasurable (by unfold Scalar.xiSlice; fun_prop)]

theorem slice_energy_real_nonneg (k : ℕ) {beta m : ℝ} (hbeta : 0 ≤ beta)
    (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) :
    0 ≤ beta*(Scalar.xiSlice k m 1-
      (∫ q : Overlap, Scalar.xiSlice k m (q : ℝ) ∂(nu : Measure Overlap))) := by
  have H := integral_mono (slice_covariance_integrable k m nu)
    (integrable_const (Scalar.xiSlice k m 1)) (slice_covariance_le_one k hm)
  simp only [integral_const, probReal_univ, one_smul] at H
  exact mul_nonneg hbeta (sub_nonneg.mpr H)

theorem cutoff_raw_real_eq (k : ℕ) {beta : ℝ} (hbeta : beta ≠ 0) (m : ℝ)
    (nu : Trial) (q : ℝ) :
    beta*(Scalar.xiSlice k m 1-
      (∫ s : Overlap, Scalar.xiSlice k m (s : ℝ) ∂(nu : Measure Overlap)))+
      beta⁻¹*((∫ t in (0 : ℝ)..q, (xHat (realLaw nu) t)⁻¹)+Real.log (1-q)) =
      2*functional beta (Scalar.xiSlice k m) (realLaw nu) q/beta := by
  rw [slice_covariance_integral_realLaw]
  unfold functional
  field_simp [hbeta]
  ring

theorem scaled_cutoff_functional_nonneg (k : ℕ) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    0 ≤ 2*functional beta (Scalar.xiSlice k m) (realLaw nu) q/beta := by
  rw [← cutoff_raw_real_eq k hbeta.ne' m nu q]
  exact add_nonneg (slice_energy_real_nonneg k hbeta.le hm nu)
    (entropy_cutoff_real_nonneg hbeta nu hq hnu)

theorem rawFunctional_cutoff_eq_ofReal (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    rawFunctional k beta m nu =
      ENNReal.ofReal (2*functional beta (Scalar.xiSlice k m) (realLaw nu) q/beta) := by
  rw [rawFunctional, energy_eq_ofReal k hk hbeta.le hm,
    entropy_cutoff_eq_ofReal hbeta nu hq hnu,
    ← ENNReal.ofReal_add (slice_energy_real_nonneg k hbeta.le hm nu)
      (entropy_cutoff_real_nonneg hbeta nu hq hnu), cutoff_raw_real_eq k hbeta.ne']

theorem rawFunctional_cutoff_toReal (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    (rawFunctional k beta m nu).toReal =
      2*functional beta (Scalar.xiSlice k m) (realLaw nu) q/beta := by
  rw [rawFunctional_cutoff_eq_ofReal k hk hbeta hm nu hq hnu,
    ENNReal.toReal_ofReal (scaled_cutoff_functional_nonneg k hbeta hm nu hq hnu)]

theorem rawFunctional_cutoff_ne_top (k : ℕ) (hk : 1 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm : m ∈ Icc (-1 : ℝ) 1) (nu : Trial) {q : ℝ}
    (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ (s : Overlap) ∂(nu : Measure Overlap), (s : ℝ) ≤ q) :
    rawFunctional k beta m nu ≠ ∞ := by
  rw [rawFunctional_cutoff_eq_ofReal k hk hbeta hm nu hq hnu]
  exact ENNReal.ofReal_ne_top


end
end TensorPCA.NonRSLowerProofs.FiniteCS
