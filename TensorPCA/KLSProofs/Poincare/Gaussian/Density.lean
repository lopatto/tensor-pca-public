-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/Gaussian/Density.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Density helpers for one-dimensional Gaussian Poincaré

Density helpers for `lem:poincare-gaussian-one-dimensional`, with explicit analytic
assumptions.

The parameter `v : NNReal` is the variance. This module treats `v ≠ 0`, when `gaussianReal m v`
has density `gaussianPDFReal m v` with respect to Lebesgue measure. At `v = 0`, the Gaussian law
is `Measure.dirac m`, whereas `gaussianPDFReal m 0` is the zero function; the Dirac case must be
handled separately. No Poincaré test-domain definitions are imported here.

Historical API references in the upstream source use Mathlib v4.33.0, commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. This port is checked with the toolchain
and Mathlib revision pinned in this repository:

* [Gaussian density, probability law, and moments](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean).
* [Gaussian first-moment integrability](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean).
* [Improper fundamental theorem of calculus](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean).
* [Integrability under a density](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean).

The existing probability instance, density nonnegativity, density integral, Gaussian moments,
and `integral_gaussianReal_eq_integral_smul` are reused directly rather than restated.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

/-- [Local helper] The derivative of the positive-variance Gaussian density, with variance
`v` rather than standard deviation as the parameter.

Source: differentiate Mathlib's
[`gaussianPDFReal_def`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L49-L54)
using the real exponential chain rule. This is a local calculus obligation. -/
theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) x := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hsq : HasDerivAt (fun y : ℝ ↦ -(y - m) ^ 2 / (2 * (v : ℝ))) (-((x - m) / (v : ℝ))) x := by
    have h1 : HasDerivAt (fun y : ℝ ↦ y - m) 1 x := (hasDerivAt_id x).sub_const m
    have h2 : HasDerivAt (fun y : ℝ ↦ (y - m) ^ 2) (2 * (x - m)) x := by
      have h := (hasDerivAt_pow 2 (x - m)).comp x h1
      rw [show ((2 : ℕ) : ℝ) * (x - m) ^ (2 - 1) * 1 = 2 * (x - m) by norm_num] at h
      exact h
    have h3 := h2.neg.div_const (2 * (v : ℝ))
    rw [show -(2 * (x - m)) / (2 * (v : ℝ)) = -((x - m) / (v : ℝ)) by
        rw [neg_div, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]] at h3
    exact h3
  have hexp := (hsq.exp).const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have hval :
    -((x - m) / (v : ℝ)) * gaussianPDFReal m v x =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        (Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) * -((x - m) / (v : ℝ))) := by
    simp only [gaussianPDFReal_def]
    ring
  rw [hval, gaussianPDFReal_def]
  exact hexp

/-- [Local helper] The positive-variance Gaussian density vanishes at positive infinity.

Source: the explicit
[`gaussianPDFReal_def`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L49-L54)
and `Real.tendsto_exp_atBot`. The limit concerns the density, not a Poincaré test function. -/
theorem tendsto_gaussianPDFReal_atTop (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atTop (𝓝 0) := by
  have hvpos : (0 : ℝ) < 2 * (v : ℝ) := by
    have : 0 < v := pos_iff_ne_zero.mpr hv
    have : (0 : ℝ) < v := NNReal.coe_pos.mpr this
    linarith
  have hsub : Tendsto (fun x : ℝ ↦ x - m) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-m) tendsto_id).congr fun x ↦
      (sub_eq_add_neg x m).symm
  have harg : Tendsto (fun x : ℝ ↦ -(x - m) ^ 2 / (2 * (v : ℝ))) atTop atBot :=
    Tendsto.atBot_div_const hvpos
      (tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).comp hsub))
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have h0 := hexp.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  rw [mul_zero] at h0
  simpa only [gaussianPDFReal_def] using h0

/-- [Local helper] The positive-variance Gaussian density vanishes at negative infinity.

Source: the explicit
[`gaussianPDFReal_def`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L49-L54)
and `Real.tendsto_exp_atBot`, with the squared centered variable tending to positive infinity. -/
theorem tendsto_gaussianPDFReal_atBot (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atBot (𝓝 0) := by
  have hvpos : (0 : ℝ) < 2 * (v : ℝ) := by
    have : 0 < v := pos_iff_ne_zero.mpr hv
    have : (0 : ℝ) < v := NNReal.coe_pos.mpr this
    linarith
  have hsub : Tendsto (fun x : ℝ ↦ m - x) atBot atTop :=
    (tendsto_atTop_add_const_left atBot m tendsto_neg_atBot_atTop).congr fun x ↦
      (sub_eq_add_neg m x).symm
  have hsq : Tendsto (fun x : ℝ ↦ (x - m) ^ 2) atBot atTop :=
    (((tendsto_pow_atTop two_ne_zero).comp hsub).congr fun x ↦ by
      rw [Function.comp_apply, ← neg_sub x m, neg_sq])
  have harg : Tendsto (fun x : ℝ ↦ -(x - m) ^ 2 / (2 * (v : ℝ))) atBot atBot :=
    Tendsto.atBot_div_const hvpos (tendsto_neg_atTop_atBot.comp hsq)
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ)))) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have h0 := hexp.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  rw [mul_zero] at h0
  simpa only [gaussianPDFReal_def] using h0

/-- [Mathlib bridge] The centered first moment times the density is Lebesgue integrable.
`Integrable` includes absolute integrability, so it supplies the integrability needed by both
one-sided density FTC identities.

Source: Mathlib's `integrable_mul_exp_neg_mul_sq`, translated and scaled using the explicit
Gaussian density. The same fact could alternatively be recovered from
[`memLp_id_gaussianReal`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Probability/Distributions/Gaussian/Real.lean#L578-L587)
and the density integrability bridge. No moment assumption is imposed on an external measure or
test function. -/
theorem integrable_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun x : ℝ ↦ (x - m) * gaussianPDFReal m v x) volume := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hb : (0 : ℝ) < (2 * (v : ℝ))⁻¹ := by positivity
  have h := (integrable_mul_exp_neg_mul_sq hb).comp_sub_right m
  have h2 := h.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  refine h2.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  have harg : -(2 * (v : ℝ))⁻¹ * (x - m) ^ 2 = -(x - m) ^ 2 / (2 * (v : ℝ)) := by ring
  simp only [gaussianPDFReal_def, harg]
  ring

/-- [Local helper] The centered first-moment weight on a right half-line equals variance times
the density. The identity holds for every endpoint `t`; downstream nonnegative Tonelli arguments
specialize it to `m ≤ t`.

Source: the density derivative and limit above, combined with Mathlib's
[`integral_Ioi_of_hasDerivAt_of_tendsto'`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L805-L819).
This is a local tail identity for the anchored Poincaré argument. -/
theorem integral_Ioi_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℝ) :
    (∫ x in Set.Ioi t, (x - m) * gaussianPDFReal m v x) = (v : ℝ) * gaussianPDFReal m v t := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hderiv :
    ∀ x ∈ Set.Ici t,
      HasDerivAt (fun y ↦ -(v : ℝ) * gaussianPDFReal m v y) ((x - m) * gaussianPDFReal m v x)
        x := by
    intro x _
    have h := (hasDerivAt_gaussianPDFReal m hv x).const_mul (-(v : ℝ))
    have hcancel : (v : ℝ) * ((x - m) / (v : ℝ)) = x - m := by field_simp
    have hval :
      -(v : ℝ) * (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) =
        (x - m) * gaussianPDFReal m v x := by
      calc
        -(v : ℝ) * (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) =
            ((v : ℝ) * ((x - m) / (v : ℝ))) * gaussianPDFReal m v x := by
          ring
        _ = (x - m) * gaussianPDFReal m v x := by rw [hcancel]
    rwa [hval] at h
  have hint : IntegrableOn (fun x ↦ (x - m) * gaussianPDFReal m v x) (Set.Ioi t) :=
    (integrable_centered_gaussianPDFReal m hv).integrableOn
  have hlim : Tendsto (fun y ↦ -(v : ℝ) * gaussianPDFReal m v y) atTop (𝓝 0) := by
    have h := (tendsto_gaussianPDFReal_atTop m hv).const_mul (-(v : ℝ))
    rwa [mul_zero] at h
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  rw [hFTC]
  ring

/-- [Local helper] The reflected centered first-moment weight on a left half-line equals
variance times the density. The identity holds for every endpoint `t`; downstream nonnegative
Tonelli arguments specialize it to `t ≤ m`.

Source: the density derivative and limit above, Mathlib's
[`integral_Iic_of_hasDerivAt_of_tendsto'`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L1001-L1014),
and `integral_Iic_eq_integral_Iio` for Lebesgue-null singleton endpoints. -/
theorem integral_Iio_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℝ) :
    (∫ x in Set.Iio t, (m - x) * gaussianPDFReal m v x) = (v : ℝ) * gaussianPDFReal m v t := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hderiv :
    ∀ x ∈ Set.Iic t,
      HasDerivAt (fun y ↦ (v : ℝ) * gaussianPDFReal m v y) ((m - x) * gaussianPDFReal m v x)
        x := by
    intro x _
    have h := (hasDerivAt_gaussianPDFReal m hv x).const_mul (v : ℝ)
    have hcancel : (v : ℝ) * ((x - m) / (v : ℝ)) = x - m := by field_simp
    have hval :
      (v : ℝ) * (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) =
        (m - x) * gaussianPDFReal m v x := by
      calc
        (v : ℝ) * (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) =
            -(((v : ℝ) * ((x - m) / (v : ℝ))) * gaussianPDFReal m v x) := by
          ring
        _ = (m - x) * gaussianPDFReal m v x := by rw [hcancel]; ring
    rwa [hval] at h
  have hint : Integrable (fun x ↦ (m - x) * gaussianPDFReal m v x) volume := by
    have h := (integrable_centered_gaussianPDFReal m hv).neg
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.neg_apply]
    ring
  have hlim : Tendsto (fun y ↦ (v : ℝ) * gaussianPDFReal m v y) atBot (𝓝 0) := by
    have h := (tendsto_gaussianPDFReal_atBot m hv).const_mul (v : ℝ)
    rwa [mul_zero] at h
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto' hderiv hint.integrableOn hlim
  rw [← integral_Iic_eq_integral_Iio, hFTC]
  ring

/-- [Mathlib bridge] Integrability under the positive-variance Gaussian law is exactly
Lebesgue integrability after multiplication by its real density. No separate measurability
assumption on `f` is needed: it is already part of either `Integrable` proposition.

Source: `gaussianReal_of_var_ne_zero`, `measurable_gaussianPDF`, `gaussianPDF_lt_top`,
`toReal_gaussianPDF`, and Mathlib's
[`integrable_withDensity_iff_integrable_smul'`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L807-L813).
An equality of real integrals alone would not establish this integrability equivalence. -/
theorem integrable_gaussianReal_iff (m : ℝ) {v : NNReal} (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔ Integrable (fun x ↦ gaussianPDFReal m v x * f x) volume := by
  rw [gaussianReal_of_var_ne_zero m hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF m v)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp_rw [smul_eq_mul, toReal_gaussianPDF]

end TensorPCA.KLSProofs.Poincare.SmoothTest
