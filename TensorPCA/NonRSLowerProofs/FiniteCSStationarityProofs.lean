-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSPositiveMassProofs
public import Mathlib.Analysis.Calculus.DerivativeTest

/-! Finite-temperature endpoint stationarity. The Gaussian precision in this
module is D=1/xHat(q0)=beta/profile(q0); covariance parameters carry beta².
This differs from zero-temperature rescaled precision 1/(beta*xHat(q0)). -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
open RetainedCountProofs.CrisantiSommers
noncomputable section

theorem xHat_of_ordered_two_atom (nu : Trial) {q0 q1 x : ℝ}
    (hq : q0 ≤ q1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) (t : ℝ) :
    xHat (realLaw nu) t = (1 - max t q1) + x * max (q1 - max t q0) 0 := by
  have H := profile_of_ordered_two_atom 1 nu hq hx hlaw t
  simpa only [profile_eq_scaled_xHat_realLaw, one_mul] using H

theorem xHat_two_atom_below (nu : Trial) {q0 q1 x t : ℝ}
    (hq : q0 ≤ q1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) (ht : t ≤ q0) :
    xHat (realLaw nu) t = (1 - q1) + x * (q1 - q0) := by
  rw [xHat_of_ordered_two_atom nu hq hx hlaw,
    max_eq_right (ht.trans hq), max_eq_right ht, max_eq_left (sub_nonneg.mpr hq)]

theorem xHat_two_atom_between (nu : Trial) {q0 q1 x t : ℝ}
    (hq : q0 ≤ q1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) (ht : t ∈ Icc q0 q1) :
    xHat (realLaw nu) t = (1 - q1) + x * (q1 - t) := by
  rw [xHat_of_ordered_two_atom nu hq hx hlaw,
    max_eq_right ht.2, max_eq_left ht.1, max_eq_left (sub_nonneg.mpr ht.2)]

theorem integral_inverseSquare_xHat_to_first_atom (nu : Trial) {q0 q1 x : ℝ}
    (hq0 : 0 ≤ q0) (hq : q0 ≤ q1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) :
    (∫ t in (0 : ℝ)..q0, 1 / (xHat (realLaw nu) t) ^ 2) =
      q0 / (xHat (realLaw nu) q0) ^ 2 := by
  have hconst (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) q0) :
      xHat (realLaw nu) t = xHat (realLaw nu) q0 := by
    rw [xHat_two_atom_below nu hq hx hlaw ((uIcc_of_le hq0 ▸ ht).2),
      xHat_two_atom_below nu hq hx hlaw le_rfl]
  calc
    _ = ∫ _t in (0 : ℝ)..q0, 1 / (xHat (realLaw nu) q0) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      change 1 / (xHat (realLaw nu) t) ^ 2 = 1 / (xHat (realLaw nu) q0) ^ 2
      rw [hconst t ht]
    _ = _ := by simp [div_eq_mul_inv]

theorem property_at_first_atom_of_ae (nu : Trial) {q0 q1 x : ℝ} (hx : 0 < x)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂realLaw nu, P r) : P q0 := by
  rw [hlaw, ae_add_measure_iff] at hP
  have hfirst := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hx).ne').mp hP.1
  simpa only [ae_dirac_eq, Filter.eventually_pure] using hfirst

theorem property_at_second_atom_of_ae (nu : Trial) {q0 q1 x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) (hcollapse : q0 = q1 ↔ x = 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1)
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂realLaw nu, P r) : P q1 := by
  by_cases hx1 : x = 1
  · rw [← hcollapse.mpr hx1]
    exact property_at_first_atom_of_ae nu hx.1 hlaw hP
  · rw [hlaw, ae_add_measure_iff] at hP
    have hpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hx1)
    have hsecond := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.mpr hpos).ne').mp hP.2
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hsecond

private theorem secondDeriv_nonpos_of_localMax {f : ℝ → ℝ} {q : ℝ}
    (hmax : IsLocalMax f q) (hc : ContinuousAt f q) : deriv (deriv f) q ≤ 0 := by
  by_contra hnot
  have hpos : 0 < deriv (deriv f) q := lt_of_not_ge hnot
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 q] (fun _ => f q) := by
    filter_upwards [hmin, hmax] with t htmin htmax
    exact le_antisymm htmax htmin
  have hh := heq.deriv.deriv_eq
  simp at hh
  exact hpos.ne' hh

theorem first_atom_stationarity_and_replicon (k : ℕ) (hk : 1 ≤ k) (beta m : ℝ)
    (nu : Trial) (zeta : Admissible) (hzlaw : zeta.law = realLaw nu)
    (hzmin : zeta.IsMinimizer beta (Scalar.xiSlice k m)) {q0 q1 x : ℝ}
    (hq0 : q0 ∈ Ioo (0 : ℝ) 1) (hq : q0 ≤ q1) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) :
    beta ^ 2 * deriv (Scalar.xiSlice k m) q0 = q0 / (xHat (realLaw nu) q0) ^ 2 ∧
      beta ^ 2 * deriv (deriv (Scalar.xiSlice k m)) q0 ≤ 1 / (xHat (realLaw nu) q0) ^ 2 := by
  let xi := Scalar.xiSlice k m
  let f := firstVariation beta xi (realLaw nu)
  have hxi : ContinuousOn xi (Ico (0 : ℝ) 1) := by
    intro t _
    exact (VariationalProofs.hasDerivAt_xiSlice k m t).continuousAt.continuousWithinAt
  obtain ⟨M, hmax, heq⟩ := (zeta.minimizer_iff_support_on_maximum beta xi hxi).mp hzmin
  rw [hzlaw] at hmax heq
  have h0M := property_at_first_atom_of_ae nu hx.1 hlaw heq
  have hlocal : IsLocalMax f q0 := by
    filter_upwards [Ioo_mem_nhds hq0.1 hq0.2] with t ht
    change firstVariation beta xi (realLaw nu) t ≤ firstVariation beta xi (realLaw nu) q0
    rw [h0M]
    exact hmax t ⟨ht.1.le, ht.2⟩
  have hcut : HasCutoff (realLaw nu) zeta.cutoff := by rw [← hzlaw]; exact zeta.hasCutoff
  have hd := firstVariation_hasDerivAt beta xi (realLaw nu) hcut hq0.2
    (VariationalProofs.hasDerivAt_xiSlice k m q0).differentiableAt.hasDerivAt
  have hz := hlocal.deriv_eq_zero
  change deriv (firstVariation beta xi (realLaw nu)) q0 = 0 at hz
  rw [hd.deriv, integral_inverseSquare_xHat_to_first_atom nu hq0.1.le hq ⟨hx.1.le, hx.2⟩ hlaw] at hz
  have hdiff : DifferentiableOn ℝ xi (Iio 1) := by
    intro t _
    exact (VariationalProofs.hasDerivAt_xiSlice k m t).differentiableAt.differentiableWithinAt
  have hd2 := firstVariation_deriv_hasDerivAt beta xi (realLaw nu) hcut hq0.2 hdiff
    (VariationalProofs.hasDerivAt_deriv_xiSlice hk m q0).differentiableAt.hasDerivAt
  have hle := secondDeriv_nonpos_of_localMax hlocal hd.continuousAt
  change deriv (deriv (firstVariation beta xi (realLaw nu))) q0 ≤ 0 at hle
  rw [hd2.deriv] at hle
  exact ⟨sub_eq_zero.mp hz, sub_nonpos.mp hle⟩

theorem mass_mul_integral_inverseSquare_between_atoms (nu : Trial) {q0 q1 x : ℝ}
    (hq : q0 ≤ q1) (hq1 : q1 < 1) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) :
    x * (∫ t in q0..q1, 1 / (xHat (realLaw nu) t) ^ 2) =
      (1 - q1)⁻¹ - (xHat (realLaw nu) q0)⁻¹ := by
  let A : ℝ → ℝ := fun t => (1 - q1) + x * (q1 - t)
  have hA (t : ℝ) (ht : t ∈ uIcc q0 q1) : 0 < A t := by
    rw [uIcc_of_le hq] at ht
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hq1) (mul_nonneg hx.1.le (sub_nonneg.mpr ht.2))
  have heq (t : ℝ) (ht : t ∈ uIcc q0 q1) : xHat (realLaw nu) t = A t :=
    xHat_two_atom_between nu hq ⟨hx.1.le, hx.2⟩ hlaw ((uIcc_of_le hq) ▸ ht)
  have hhat : Continuous (xHat (realLaw nu)) := by
    have he : xHat (realLaw nu) = hatCDF (nu : Measure Overlap) := funext (xHat_realLaw nu)
    rw [he]
    exact hatCDF_continuous _
  have hInt : IntervalIntegrable (fun t => x / (xHat (realLaw nu) t) ^ 2) volume q0 q1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (hhat.continuousOn.pow 2)
    intro t ht
    change (xHat (realLaw nu) t) ^ 2 ≠ 0
    rw [heq t ht]
    exact pow_ne_zero 2 (hA t ht).ne'
  have hd (t : ℝ) (ht : t ∈ uIcc q0 q1) :
      HasDerivAt (fun t => (A t)⁻¹) (x / (xHat (realLaw nu) t) ^ 2) t := by
    have hdA : HasDerivAt A (-x) t := by
      convert (((hasDerivAt_id t).const_sub q1).const_mul x).const_add (1 - q1) using 1 <;>
        (try funext u) <;> (try dsimp [A]) <;> ring
    rw [heq t ht]
    convert hdA.inv (hA t ht).ne' using 1 <;> ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hInt
  have hA0 : A q0 = xHat (realLaw nu) q0 :=
    (xHat_two_atom_between nu hq ⟨hx.1.le, hx.2⟩ hlaw ⟨le_rfl, hq⟩).symm
  have hA1 : A q1 = 1 - q1 := by dsimp [A]; ring
  rw [hA0, hA1] at hh
  simp_rw [div_eq_mul_inv] at hh ⊢
  rw [intervalIntegral.integral_const_mul] at hh
  simpa only [one_mul] using hh

private theorem inverseSquare_intervalIntegrable_of_cutoff (mu : Measure ℝ)
    [IsProbabilityMeasure mu] {q a b : ℝ} (hq : HasCutoff mu q) (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable (fun t => 1 / (xHat mu t) ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div ((xHat_continuous mu hq).continuousOn.pow 2)
  intro t ht
  change (xHat mu t) ^ 2 ≠ 0
  exact pow_ne_zero 2 (xHat_pos mu hq (ht.2.trans_lt (max_lt ha hb))).ne'

theorem thermal_precision_difference (k : ℕ) (hk : 1 ≤ k) (beta m : ℝ)
    (nu : Trial) (zeta : Admissible) (hzlaw : zeta.law = realLaw nu)
    (hzmin : zeta.IsMinimizer beta (Scalar.xiSlice k m)) {q0 q1 x : ℝ}
    (hq0 : q0 ∈ Ioo (0 : ℝ) 1) (hq1 : q1 ∈ Ioo (0 : ℝ) 1) (hq : q0 ≤ q1)
    (hx : x ∈ Ioc (0 : ℝ) 1) (hcollapse : q0 = q1 ↔ x = 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) :
    x * (beta ^ 2 * (deriv (Scalar.xiSlice k m) q1 - deriv (Scalar.xiSlice k m) q0)) =
      (1 - q1)⁻¹ - (xHat (realLaw nu) q0)⁻¹ := by
  let xi := Scalar.xiSlice k m
  let f := firstVariation beta xi (realLaw nu)
  have hxi : ContinuousOn xi (Ico (0 : ℝ) 1) := by
    intro t _
    exact (VariationalProofs.hasDerivAt_xiSlice k m t).continuousAt.continuousWithinAt
  obtain ⟨M, hmax, heq⟩ := (zeta.minimizer_iff_support_on_maximum beta xi hxi).mp hzmin
  rw [hzlaw] at hmax heq
  have h1M := property_at_second_atom_of_ae nu hx hcollapse hlaw heq
  have hlocal : IsLocalMax f q1 := by
    filter_upwards [Ioo_mem_nhds hq1.1 hq1.2] with t ht
    change firstVariation beta xi (realLaw nu) t ≤ firstVariation beta xi (realLaw nu) q1
    rw [h1M]
    exact hmax t ⟨ht.1.le, ht.2⟩
  have hcut : HasCutoff (realLaw nu) zeta.cutoff := by rw [← hzlaw]; exact zeta.hasCutoff
  have hd := firstVariation_hasDerivAt beta xi (realLaw nu) hcut hq1.2
    (VariationalProofs.hasDerivAt_xiSlice k m q1).differentiableAt.hasDerivAt
  have hz := hlocal.deriv_eq_zero
  change deriv (firstVariation beta xi (realLaw nu)) q1 = 0 at hz
  rw [hd.deriv] at hz
  have hsecond : beta ^ 2 * deriv xi q1 = ∫ t in (0 : ℝ)..q1, 1 / (xHat (realLaw nu) t) ^ 2 :=
    sub_eq_zero.mp hz
  have hfirst := (first_atom_stationarity_and_replicon k hk beta m nu zeta hzlaw hzmin hq0 hq hx hlaw).1
  rw [← integral_inverseSquare_xHat_to_first_atom nu hq0.1.le hq ⟨hx.1.le, hx.2⟩ hlaw] at hfirst
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (inverseSquare_intervalIntegrable_of_cutoff (realLaw nu) (a := (0 : ℝ)) (b := q0) hcut (by norm_num) hq0.2)
    (inverseSquare_intervalIntegrable_of_cutoff (realLaw nu) (a := q0) (b := q1) hcut hq0.2 hq1.2)
  have hdiff : beta ^ 2 * (deriv xi q1 - deriv xi q0) =
      ∫ t in q0..q1, 1 / (xHat (realLaw nu) t) ^ 2 := by
    rw [mul_sub, hsecond, hfirst]
    linarith [hsplit]
  rw [hdiff]
  exact mass_mul_integral_inverseSquare_between_atoms nu hq hq1.2 hx hlaw

/-- Finite-temperature optimal parameters, satisfying both thermal precision identities
and the replicon inequality.
-/
theorem exists_thermal_stationary_minimizer (k : ℕ) (hk : 3 ≤ k) {beta m : ℝ}
    (hbeta : 0 < beta) (hm0 : 0 < |m|) (hm1 : |m| < 1) :
    ∃ (nu : Trial) (q0 q1 x : ℝ), 0 < q0 ∧ q0 ≤ q1 ∧ q1 < 1 ∧
      x ∈ Ioc (0 : ℝ) 1 ∧ (q0 = q1 ↔ x = 1) ∧
      realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
        ENNReal.ofReal (1 - x) • Measure.dirac q1 ∧
      rawFunctional k beta m nu = rawValue k beta m ∧
      (∀ tau : Trial, rawFunctional k beta m nu ≤ rawFunctional k beta m tau) ∧
      beta ^ 2 * deriv (Scalar.xiSlice k m) q0 = q0 * ((xHat (realLaw nu) q0)⁻¹) ^ 2 ∧
      beta ^ 2 * deriv (deriv (Scalar.xiSlice k m)) q0 ≤ ((xHat (realLaw nu) q0)⁻¹) ^ 2 ∧
      x * (beta ^ 2 * (deriv (Scalar.xiSlice k m) q1 - deriv (Scalar.xiSlice k m) q0)) =
        (1 - q1)⁻¹ - (xHat (realLaw nu) q0)⁻¹ := by
  obtain ⟨nu, q0, q1, x, hq0, hq, hq1, hx, hcollapse, hlaw, heq, hmin⟩ :=
    exists_positive_mass_two_atom_minimizer k hk hbeta hm0 hm1
  have hrealcut : ∀ᵐ r ∂realLaw nu, r ≤ q1 := by
    rw [hlaw, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simpa only [ae_dirac_eq, Filter.eventually_pure] using hq
    · apply Measure.ae_smul_measure
      simp
  have hcut : ∀ᵐ r : Overlap ∂(nu : Measure Overlap), (r : ℝ) ≤ q1 :=
    (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mp hrealcut
  have hm : m ∈ Icc (-1 : ℝ) 1 := abs_le.mp hm1.le
  obtain ⟨zeta, hzlaw, hzmin⟩ := exists_legacy_minimizer_of_raw_minimizer k (by omega) hbeta hm nu
    ⟨hq0.le.trans hq, hq1⟩ hcut hmin
  have hq0int : q0 ∈ Ioo (0 : ℝ) 1 := ⟨hq0, hq.trans_lt hq1⟩
  have hq1int : q1 ∈ Ioo (0 : ℝ) 1 := ⟨hq0.trans_le hq, hq1⟩
  obtain ⟨hstationary, hreplicon⟩ := first_atom_stationarity_and_replicon k (by omega) beta m
    nu zeta hzlaw hzmin hq0int hq hx hlaw
  have hprecision := thermal_precision_difference k (by omega) beta m nu zeta hzlaw hzmin
    hq0int hq1int hq hx hcollapse hlaw
  refine ⟨nu, q0, q1, x, hq0, hq, hq1, hx, hcollapse, hlaw, heq, hmin, ?_, ?_, hprecision⟩
  · simpa only [div_eq_mul_inv, inv_pow] using hstationary
  · simpa only [one_div, inv_pow] using hreplicon

end
end TensorPCA.NonRSLowerProofs.FiniteCS
