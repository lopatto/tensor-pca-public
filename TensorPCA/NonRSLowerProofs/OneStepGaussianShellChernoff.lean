-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianMomentProofs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! A probability upper bound for a thin spherical shell under the rescaled standard
Gaussian. The signed Chernoff parameter covers every B>0.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianShellChernoff
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Literal centered Gaussian with coordinate variance B inverse. -/
def scaledGaussian (B : ℝ) : Measure E :=
  (stdGaussian E).map (fun g ↦ (Real.sqrt B)⁻¹ • g)

instance scaledGaussian_probability (B : ℝ) :
    IsProbabilityMeasure (scaledGaussian (E := E) B) := by
  unfold scaledGaussian
  exact (Measure.isProbabilityMeasure_map_iff
    (by fun_prop : Measurable (fun g : E ↦ (Real.sqrt B)⁻¹ • g)).aemeasurable).mpr inferInstance

theorem scaled_norm_sq {B : ℝ} (hB : 0 < B) (g : E) :
    ‖(Real.sqrt B)⁻¹ • g‖^2 = ‖g‖^2/B := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hB.le]
  ring

theorem standard_shell_parameter_integrable {B : ℝ} (hB : 0 < B) :
    Integrable (fun g : E ↦ Real.exp ((B-1)/(2*B)*‖g‖^2)) (stdGaussian E) := by
  apply GaussianMomentProofs.integrable_exp_norm_sq
  apply (div_lt_iff₀ (by positivity : 0 < 2*B)).mpr
  linarith

theorem standard_shell_parameter_integral {B : ℝ} (hB : 0 < B) :
    (∫ g : E, Real.exp ((B-1)/(2*B)*‖g‖^2) ∂stdGaussian E) =
      Real.exp ((Module.finrank ℝ E : ℝ)*Real.log B/2) := by
  have ht : (B-1)/(2*B) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*B)).mpr
    linarith
  have heq : 1-2*((B-1)/(2*B)) = B⁻¹ := by field_simp [hB.ne']; ring
  rw [GaussianMomentProofs.integral_exp_norm_sq ht, heq,
    Real.rpow_def_of_pos (inv_pos.mpr hB), Real.log_inv]
  congr 1
  ring

private theorem shell_parameter_comp {B : ℝ} (hB : 0 < B) :
    (fun x : E ↦ Real.exp ((B-1)/2*‖x‖^2)) ∘ (fun g ↦ (Real.sqrt B)⁻¹ • g) =
      fun g ↦ Real.exp ((B-1)/(2*B)*‖g‖^2) := by
  funext g
  change Real.exp ((B-1)/2*‖(Real.sqrt B)⁻¹ • g‖^2) = _
  rw [scaled_norm_sq hB]
  congr 1
  field_simp [hB.ne']

theorem scaled_shell_parameter_integrable {B : ℝ} (hB : 0 < B) :
    Integrable (fun x : E ↦ Real.exp ((B-1)/2*‖x‖^2)) (scaledGaussian B) := by
  unfold scaledGaussian
  apply (integrable_map_measure
    (by fun_prop : Measurable (fun x : E ↦ Real.exp ((B-1)/2*‖x‖^2))).aestronglyMeasurable
    (by fun_prop : Measurable (fun g : E ↦ (Real.sqrt B)⁻¹ • g)).aemeasurable).mpr
  rw [shell_parameter_comp hB]
  exact standard_shell_parameter_integrable hB

theorem scaled_shell_parameter_integral {B : ℝ} (hB : 0 < B) :
    (∫ x : E, Real.exp ((B-1)/2*‖x‖^2) ∂scaledGaussian B) =
      Real.exp ((Module.finrank ℝ E : ℝ)*Real.log B/2) := by
  unfold scaledGaussian
  rw [integral_map
    (by fun_prop : Measurable (fun g : E ↦ (Real.sqrt B)⁻¹ • g)).aemeasurable
    (by fun_prop : Measurable (fun x : E ↦ Real.exp ((B-1)/2*‖x‖^2))).aestronglyMeasurable]
  change (∫ g : E, ((fun x ↦ Real.exp ((B-1)/2*‖x‖^2)) ∘
    (fun g ↦ (Real.sqrt B)⁻¹ • g)) g ∂stdGaussian E) = _
  rw [shell_parameter_comp hB]
  exact standard_shell_parameter_integral hB

/-- No lower large-deviation estimate is used. The exact quadratic MGF and
the signed exponential Markov bound suffice, including B<1 and dimension zero. -/
theorem shell_probability_upper {B eps : ℝ} (hB : 0 < B) (heps : 0 ≤ eps) :
    (scaledGaussian (E := E) B).real
      {x | |‖x‖^2-(Module.finrank ℝ E : ℝ)| ≤ eps*(Module.finrank ℝ E : ℝ)} ≤
      Real.exp ((Module.finrank ℝ E : ℝ)*
        (-(B-1-Real.log B)/2+|B-1| *eps/2)) := by
  let d : ℝ := Module.finrank ℝ E
  let L := (B-1)*d/2-|B-1| *eps*d/2
  let S : Set E := {x | |‖x‖^2-d| ≤ eps*d}
  let F : E → ℝ := fun x ↦ Real.exp ((B-1)/2*‖x‖^2)
  have hInt : Integrable F (scaledGaussian B) := scaled_shell_parameter_integrable hB
  have hsub : S ⊆ {x | Real.exp L ≤ F x} := by
    intro x hx
    change |‖x‖^2-d| ≤ eps*d at hx
    have habs : |(B-1)*(‖x‖^2-d)| ≤ |B-1| *(eps*d) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have hlo := (abs_le.mp habs).1
    apply Real.exp_le_exp.mpr
    dsimp [F, L]
    nlinarith
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (scaledGaussian (E := E) B) fun x ↦ (Real.exp_pos _).le) hInt (Real.exp L)
  have hmass := measureReal_mono (μ := scaledGaussian (E := E) B) hsub
  have hweighted := mul_le_mul_of_nonneg_left hmass (Real.exp_pos L).le
  have hbound : (scaledGaussian (E := E) B).real S ≤
      Real.exp ((Module.finrank ℝ E : ℝ)*Real.log B/2)/Real.exp L := by
    apply (le_div_iff₀ (Real.exp_pos L)).mpr
    rw [mul_comm]
    apply hweighted.trans
    simpa only [F, scaled_shell_parameter_integral hB] using hMarkov
  change (scaledGaussian (E := E) B).real S ≤ _
  apply hbound.trans_eq
  rw [← Real.exp_sub]
  congr 1
  dsimp [L, d]
  ring


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianShellChernoff
