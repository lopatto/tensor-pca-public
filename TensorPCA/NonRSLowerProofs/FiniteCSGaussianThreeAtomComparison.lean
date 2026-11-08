-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomPrecision
public import Mathlib.Analysis.Convex.Deriv

/-! The exact difference between the Gaussian three-atom cost at a stationary
precision and the ordinary CS cost of the constructed, different atom law. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomComparison
open Set FiniteCSGaussianThreeAtomPrecision
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem convex_bregman_nonneg {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f)
    {r q y : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hd : HasDerivAt f y q) :
    0 ≤ f r-f q-y*(r-q) := by
  rcases lt_trichotomy q r with hlt | heq | hgt
  · have h := hf.le_slope_of_hasDerivAt hq hr hlt hd
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · subst r
    simp
  · have h := hf.slope_le_of_hasDerivAt hr hq hgt hd
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith

theorem gaussian_sub_cs_eq_weighted_bregman (f : ℝ → ℝ)
    {x z y0 y1 y2 y3 q0 q1 q2 r0 r1 r2 B : ℝ}
    (hx : 0 < x) (hz : 0 < z) (h01 : y0 ≤ y1) (h12 : y1 ≤ y2) (h23 : y2 ≤ y3)
    (hB : x*(y1-y0)+z*(y2-y1)+(y3-y2) < B)
    (hr0 : r0 = y0/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))^2)
    (hmoment : x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 = y3-B+1) :
    (threeAtomCost x z y0 (y1-y0) (y2-y1) (y3-y2) B-
      (x*((q1*y1-f q1)-(q0*y0-f q0))+
        z*((q2*y2-f q2)-(q1*y1-f q1))+((y3-f 1)-(q2*y2-f q2))))-
      (f 1-(x*f r0+(z-x)*f r1+(1-z)*f r2)+
        r0*(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))+
        Real.log ((B-(z*(y2-y1)+(y3-y2)))/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2))))/x+
        Real.log ((B-(y3-y2))/(B-(z*(y2-y1)+(y3-y2))))/z-Real.log (B-(y3-y2))) =
      x*(f r0-f q0-y0*(r0-q0))+
        (z-x)*(f r1-f q1-y1*(r1-q1))+(1-z)*(f r2-f q2-y2*(r2-q2)) := by
  have hD0 : 0 < B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)) := sub_pos.mpr hB
  have hD2 : 0 < B-(y3-y2) := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr h01), mul_nonneg hz.le (sub_nonneg.mpr h12)]
  have hBp : 0 < B := by linarith
  have hcontact : y0/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2))) =
      r0*(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2))) := by
    rw [hr0]
    field_simp <;> ring
  rw [threeAtomCost_eq hx hz (sub_nonneg.mpr h01) (sub_nonneg.mpr h12) (sub_nonneg.mpr h23) hB,
    Real.log_div hBp.ne' hD2.ne', hcontact]
  linear_combination hmoment

theorem gaussian_cs_comparison (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ici 0) f)
    {x z y0 y1 y2 y3 q0 q1 q2 r0 r1 r2 B : ℝ}
    (hx : 0 < x) (hxz : x ≤ z) (hz1 : z ≤ 1)
    (h01 : y0 ≤ y1) (h12 : y1 ≤ y2) (h23 : y2 ≤ y3)
    (hq0 : 0 ≤ q0) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hr0pos : 0 ≤ r0) (hr1pos : 0 ≤ r1) (hr2pos : 0 ≤ r2)
    (hd0 : HasDerivAt f y0 q0) (hd1 : HasDerivAt f y1 q1) (hd2 : HasDerivAt f y2 q2)
    (hB : x*(y1-y0)+z*(y2-y1)+(y3-y2) < B)
    (hr0 : r0 = y0/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))^2)
    (hmoment : x*r0*y0+(z-x)*r1*y1+(1-z)*r2*y2 = y3-B+1) :
    f 1-(x*f r0+(z-x)*f r1+(1-z)*f r2)+
        r0*(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2)))+
        Real.log ((B-(z*(y2-y1)+(y3-y2)))/(B-(x*(y1-y0)+z*(y2-y1)+(y3-y2))))/x+
        Real.log ((B-(y3-y2))/(B-(z*(y2-y1)+(y3-y2))))/z-Real.log (B-(y3-y2)) ≤
      threeAtomCost x z y0 (y1-y0) (y2-y1) (y3-y2) B-
        (x*((q1*y1-f q1)-(q0*y0-f q0))+
          z*((q2*y2-f q2)-(q1*y1-f q1))+((y3-f 1)-(q2*y2-f q2))) := by
  have h := gaussian_sub_cs_eq_weighted_bregman f (q0 := q0) (q1 := q1) (q2 := q2) hx (hx.trans_le hxz)
    h01 h12 h23 hB hr0 hmoment
  have h0 := mul_nonneg hx.le (convex_bregman_nonneg hf hr0pos hq0 hd0)
  have h1 := mul_nonneg (sub_nonneg.mpr hxz) (convex_bregman_nonneg hf hr1pos hq1 hd1)
  have h2 := mul_nonneg (sub_nonneg.mpr hz1) (convex_bregman_nonneg hf hr2pos hq2 hd2)
  linarith

end
end TensorPCA.NonRSLowerProofs.FiniteCSGaussianThreeAtomComparison
