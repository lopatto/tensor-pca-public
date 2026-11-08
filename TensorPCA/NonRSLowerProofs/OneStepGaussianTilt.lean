-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianMomentProofs
public import Mathlib.MeasureTheory.Measure.Tilted

/-! Exact finite Gaussian normalization in the one-step spherical lower
endpoint. The norm-square exponential is tilted under Mathlib stdGaussian;
no sphere pressure limit or literature formula is assumed. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTilt
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def tiltExponent (B v m : ℝ) (y g : E) : ℝ :=
  m/(2*B)*‖y+Real.sqrt v • g‖^2

theorem tiltExponent_eq_quadratic {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (y g : E) :
    tiltExponent B v m y g = m*‖y‖^2/(2*B)+
      (inner ℝ ((m*Real.sqrt v/B) • y) g-
        ((B-m*v)/B-1)/2*‖g‖^2) := by
  unfold tiltExponent
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    Real.sq_sqrt hv,inner_smul_right,real_inner_smul_left]
  field_simp [hB.ne']
  ring

theorem tiltExponent_exp_integrable {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    Integrable (fun g => Real.exp (tiltExponent B v m y g)) (stdGaussian E) := by
  have H := (GaussianMomentProofs.integrable_exp_quadratic (div_pos hD hB)
    ((m*Real.sqrt v/B) • y)).const_mul (Real.exp (m*‖y‖^2/(2*B)))
  refine H.congr (Eventually.of_forall fun g => ?_)
  dsimp only
  rw [tiltExponent_eq_quadratic hB hv,Real.exp_add]

/-- Exact normalization, directly in the canonical Gaussian integral form. -/
theorem integral_exp_tiltExponent {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    (∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian E) =
      Real.exp (m*‖y‖^2/(2*B)) *
        ((B-m*v)/B)^(-((Module.finrank ℝ E : ℝ)/2)) *
          Real.exp (‖(m*Real.sqrt v/B) • y‖^2/(2*((B-m*v)/B))) := by
  simp_rw [tiltExponent_eq_quadratic hB hv,Real.exp_add]
  rw [integral_const_mul,GaussianMomentProofs.integral_exp_quadratic (div_pos hD hB)]
  ring

/-- The exact finite Gaussian endpoint normalization in logarithmic form. -/
theorem log_integral_exp_tiltExponent {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    Real.log (∫ g, Real.exp (tiltExponent B v m y g) ∂stdGaussian E) =
      ((Module.finrank ℝ E : ℝ)/2)*Real.log (B/(B-m*v))+
        m*‖y‖^2/(2*(B-m*v)) := by
  have hz : 0 < (B-m*v)/B := div_pos hD hB
  rw [integral_exp_tiltExponent hB hv hD]
  rw [Real.log_mul (mul_ne_zero (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne')
    (Real.exp_pos _).ne',Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz,Real.log_exp]
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,mul_pow,Real.sq_sqrt hv,
    Real.log_div hD.ne' hB.ne',Real.log_div hB.ne' hD.ne']
  field_simp [hB.ne',hD.ne']
  ring

/-- The tilted law is a probability measure for every admissible finite Gaussian
endpoint parameter, including zero fresh variance.
-/
theorem tilted_probability {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    IsProbabilityMeasure ((stdGaussian E).tilted (tiltExponent B v m y)) :=
  isProbabilityMeasure_tilted (tiltExponent_exp_integrable hB hv hD y)

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTilt
