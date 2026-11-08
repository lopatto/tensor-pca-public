-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Probability/Gaussian/CharacteristicFunction.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Probability.Gaussian.Kernel
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic function and standard-law identification of radial Gaussians

The centered law with density proportional to `exp (-s * ‖x‖²)`, `s > 0`, has
characteristic function `exp (-‖t‖² / (4s))` and is the scalar image of Mathlib's
standard Gaussian by `(sqrt (2s))⁻¹`. These identities include dimension zero
and retain variance `1/(2s)`. They support the Gaussian channel in BKL
arXiv:2610.05474v1, Section 2, independently of convolution or Poincaré bounds.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace TensorPCA.KLSProofs.Probability.Gaussian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The characteristic function of the Gaussian law at inverse variance parameter `s`. -/
theorem charFun_law {s : ℝ} (hs : 0 < s) (t : V) :
    charFun (law (V := V) s) t = Complex.exp (-(‖t‖ ^ 2 / (4 * s) : ℝ)) := by
  rw [charFun_apply, law,
    integral_withDensity_eq_integral_toReal_smul
      ((normalizedKernel_measurable s).ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (normalizedKernel_pos hs _).le]
  have hform (x : V) : normalizedKernel s x •
      Complex.exp ((inner ℝ x t : ℂ) * Complex.I) =
      ((mass (V := V) s)⁻¹ : ℂ) •
        Complex.exp (-(s : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * (inner ℝ t x : ℂ)) := by
    simp only [normalizedKernel, kernel, real_inner_comm, Complex.exp_add]
    change ((Real.exp (-s * ‖x‖ ^ 2) / mass (V := V) s : ℝ) : ℂ) *
      Complex.exp ((inner ℝ t x : ℂ) * Complex.I) =
      ((mass (V := V) s)⁻¹ : ℂ) *
        (Complex.exp (-(s : ℂ) * (‖x‖ : ℂ) ^ 2) *
          Complex.exp (Complex.I * (inner ℝ t x : ℂ)))
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
  simp_rw [hform]
  rw [integral_smul]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := V) (show 0 < (s : ℂ).re from hs) Complex.I t]
  have hmass : (mass (V := V) s : ℂ) =
      ((Real.pi : ℂ) / s) ^ (((Module.finrank ℝ V : ℂ) / 2)) := by
    unfold mass
    norm_cast
    simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / s)
      ((Module.finrank ℝ V : ℝ) / 2))
  rw [← hmass]
  have hm : (mass (V := V) s : ℂ) ≠ 0 := by
    exact_mod_cast (mass_pos (V := V) hs).ne'
  simp only [smul_eq_mul, Complex.I_sq, neg_one_mul]
  have hexp : -(‖t‖ : ℂ) ^ 2 / (4 * (s : ℂ)) =
      -(‖t‖ ^ 2 / (4 * s) : ℝ) := by
    push_cast
    ring
  rw [hexp, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]


/-- The Gaussian law is the indicated scalar image of the standard Gaussian. -/
theorem law_eq_scaled_stdGaussian {s : ℝ} (hs : 0 < s) :
    law (V := V) s =
      (stdGaussian V).map (fun x : V => (Real.sqrt (2 * s))⁻¹ • x) := by
  have : IsProbabilityMeasure (law (V := V) s) :=
    law_probability hs
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_law hs, charFun_map_smul, charFun_stdGaussian]
  have hss : 0 < 2 * s := by positivity
  have hr : 0 ≤ (Real.sqrt (2 * s))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr2 : ((Real.sqrt (2 * s))⁻¹) ^ 2 = (2 * s)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hss.le]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  congr 1
  norm_cast
  rw [mul_pow, hr2]
  field_simp
  ring


end TensorPCA.KLSProofs.Probability.Gaussian
