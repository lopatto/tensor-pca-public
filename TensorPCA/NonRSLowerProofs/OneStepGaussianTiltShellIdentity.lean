-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltFractional
public import TensorPCA.NonRSLowerProofs.OneStepGaussianShellChernoff

/-! The conditional spin-shell factor is exactly the Gaussian reference
shell integral appearing in the polar comparison. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltShellIdentity
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTiltLaw OneStepGaussianTiltFractional OneStepGaussianShellChernoff
open GaussianDensityProofs
open scoped RealInnerProductSpace Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A literal Cameron--Martin identity for the finite reference shell. -/
theorem gaussian_reference_shell_identity {B : ℝ} (hB : 0 < B) (w : E)
    {S : Set E} (hS : MeasurableSet S) :
    Real.exp (‖w‖^2/(2*B)) *
      (∫ g : E, S.indicator (fun _ => (1 : ℝ))
        ((1/B) • w+(Real.sqrt B)⁻¹ • g) ∂stdGaussian E) =
          ∫ x in S, Real.exp (inner ℝ w x) ∂scaledGaussian B := by
  let b := (Real.sqrt B)⁻¹
  let q : E → ℝ := fun x => inner ℝ (b • w) x
  have hb : b*b = 1/B := by
    dsimp [b]
    rw [← pow_two,inv_pow,Real.sq_sqrt hB.le,one_div]
  have hZ : (∫ x, Real.exp (q x) ∂stdGaussian E) = Real.exp (‖w‖^2/(2*B)) := by
    simp only [q,real_inner_smul_left]
    rw [integral_exp_inner_stdGaussian]
    congr 1
    rw [pow_two,hb]
    ring
  have hT : (stdGaussian E).tilted q = (stdGaussian E).map (fun g => b • w+g) := by
    simpa only [q,sub_self,zero_div,zero_mul,sub_zero,inv_one,one_smul,Real.sqrt_one] using
      tilted_quadratic_eq_affine_gaussian (by norm_num : (0 : ℝ) < 1) (b • w)
  have H := integral_tilted q (fun x : E => S.indicator (fun _ => (1 : ℝ)) (b • x))
    (μ := stdGaussian E)
  have hTest : Measurable (fun x : E => S.indicator (fun _ => (1 : ℝ)) (b • x)) :=
    (measurable_const.indicator hS).comp (by fun_prop)
  rw [hT,integral_map (by fun_prop : Measurable (fun g : E => b • w+g)).aemeasurable
    hTest.aestronglyMeasurable] at H
  have hAffine (g : E) : b • (b • w+g) = (1/B) • w+b • g := by
    rw [smul_add,smul_smul,hb]
  simp_rw [hAffine] at H
  rw [hZ] at H
  calc
    _ = Real.exp (‖w‖^2/(2*B))*
        (∫ x, (Real.exp (q x)/Real.exp (‖w‖^2/(2*B))) •
          S.indicator (fun _ => (1 : ℝ)) (b • x) ∂stdGaussian E) := by
      exact congrArg (fun r : ℝ => Real.exp (‖w‖^2/(2*B))*r) H
    _ = ∫ x, Real.exp (q x)*S.indicator (fun _ => (1 : ℝ)) (b • x)
        ∂stdGaussian E := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul]
      field_simp [(Real.exp_pos (‖w‖^2/(2*B))).ne']
    _ = _ := by
      rw [← integral_indicator hS,scaledGaussian,integral_map
        (by fun_prop : Measurable (fun x : E => (Real.sqrt B)⁻¹ • x)).aemeasurable
        ((by fun_prop : Measurable (fun x : E => Real.exp (inner ℝ w x))).indicator hS).aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : b • x ∈ S
      · rw [indicator_of_mem hx,indicator_of_mem hx]
        simp only [q,real_inner_smul_left,inner_smul_right,mul_one]
      · rw [indicator_of_notMem hx,indicator_of_notMem hx,mul_zero]

theorem conditional_shell_factor_eq_reference_integral {B : ℝ} (hB : 0 < B)
    (v : ℝ) (y g : E) {S : Set E} (hS : MeasurableSet S) :
    Real.exp (‖y+Real.sqrt v • g‖^2/(2*B))*conditionalShellProbability B v y S g =
      ∫ x in S, Real.exp (inner ℝ (y+Real.sqrt v • g) x) ∂scaledGaussian B :=
  gaussian_reference_shell_identity hB (y+Real.sqrt v • g) hS

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltShellIdentity
