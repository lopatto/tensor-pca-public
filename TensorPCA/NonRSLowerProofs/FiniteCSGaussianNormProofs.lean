-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSStationarityProofs

/-! Exact Gaussian norm stationarity from finite-temperature two-atom geometry.
All precisions are thermal: P=1/(1-q1), D=1/xHat(q0). -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set MeasureTheory
open scoped Topology ENNReal
open RetainedCountProofs.CrisantiSommers
noncomputable section

theorem thermal_precisions_pos_and_order (nu : Trial) {q0 q1 x : ℝ}
    (hq : q0 ≤ q1) (hq1 : q1 < 1) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1) :
    0 < (xHat (realLaw nu) q0)⁻¹ ∧
      (xHat (realLaw nu) q0)⁻¹ ≤ (1 - q1)⁻¹ ∧ 0 < (1 - q1)⁻¹ := by
  have hhat := xHat_two_atom_below nu hq ⟨hx.1.le, hx.2⟩ hlaw le_rfl
  have hge : 1 - q1 ≤ xHat (realLaw nu) q0 := by
    rw [hhat]
    exact le_add_of_nonneg_right (mul_nonneg hx.1.le (sub_nonneg.mpr hq))
  have hs : 0 < 1 - q1 := sub_pos.mpr hq1
  exact ⟨inv_pos.mpr (hs.trans_le hge), inv_anti₀ hs hge, inv_pos.mpr hs⟩

theorem gaussian_norm_stationarity (nu : Trial) {q0 q1 x a v : ℝ}
    (hq : q0 ≤ q1) (hq1 : q1 < 1) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hlaw : realLaw nu = ENNReal.ofReal x • Measure.dirac q0 +
      ENNReal.ofReal (1 - x) • Measure.dirac q1)
    (ha : a = q0 * ((xHat (realLaw nu) q0)⁻¹) ^ 2)
    (hv : x * v = (1 - q1)⁻¹ - (xHat (realLaw nu) q0)⁻¹) :
    a / ((xHat (realLaw nu) q0)⁻¹) ^ 2 +
      (1 / (1 - q1)⁻¹ + v / ((1 - q1)⁻¹ * (xHat (realLaw nu) q0)⁻¹)) = 1 := by
  have hhat := xHat_two_atom_below nu hq ⟨hx.1.le, hx.2⟩ hlaw le_rfl
  have hs : 0 < 1 - q1 := sub_pos.mpr hq1
  have hH : 0 < xHat (realLaw nu) q0 := by
    rw [hhat]
    exact add_pos_of_pos_of_nonneg hs (mul_nonneg hx.1.le (sub_nonneg.mpr hq))
  have hmul : x * v * (1 - q1) * xHat (realLaw nu) q0 = xHat (realLaw nu) q0 - (1 - q1) := by
    rw [hv]
    field_simp [hs.ne', hH.ne']
  have hprod : x * (v * ((1 - q1) * xHat (realLaw nu) q0)) = x * (q1 - q0) := by
    calc
      _ = xHat (realLaw nu) q0 - (1 - q1) := by nlinarith [hmul]
      _ = _ := by rw [hhat]; ring
  have hvnorm : v / ((1 - q1)⁻¹ * (xHat (realLaw nu) q0)⁻¹) = q1 - q0 := by
    have hh := mul_left_cancel₀ hx.1.ne' hprod
    simpa only [div_eq_mul_inv, mul_inv, inv_inv] using hh
  have hanorm : a / ((xHat (realLaw nu) q0)⁻¹) ^ 2 = q0 := by
    rw [ha]
    field_simp [hH.ne']
  rw [hanorm, hvnorm]
  simp only [one_div, inv_inv]
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteCS
