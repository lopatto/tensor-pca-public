-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz

/-! Order and constant translation for the literal Gaussian log-step.
Quadratic comparison terminals use explicit exponential-integrability and
nonzero-normalizer inputs; no quadratic function is asserted Lipschitz. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepOrder
open MeasureTheory ProbabilityTheory Set Filter OneStepGaussianStepLipschitz
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussianNormalizer_add_const {N : ℕ} (T : Model.Vector N →L[ℝ] E)
    (mass : ℝ) (F : E → ℝ) (C : ℝ) (x : E) :
    gaussianNormalizer T mass (fun y => F y+C) x=
      Real.exp (mass*C)*gaussianNormalizer T mass F x := by
  unfold gaussianNormalizer
  simp_rw [mul_add,Real.exp_add]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall (fun _ => mul_comm _ _)

theorem gaussianLogStep_add_const {N : ℕ} (T : Model.Vector N →L[ℝ] E)
    {mass : ℝ} (hm : mass≠0) (F : E → ℝ) (C : ℝ) (x : E)
    (hZ : gaussianNormalizer T mass F x≠0) :
    gaussianLogStep T mass (fun y => F y+C) x=gaussianLogStep T mass F x+C := by
  simp only [gaussianLogStep,if_neg hm]
  rw [gaussianNormalizer_add_const,Real.log_mul (Real.exp_ne_zero _) hZ,Real.log_exp]
  field_simp [hm]
  ring

theorem gaussianLogStep_mono {N : ℕ} (T : Model.Vector N →L[ℝ] E)
    {mass : ℝ} (hm : 0<mass) {F G : E → ℝ} (x : E)
    (hF : Integrable (fun g : Model.Vector N => Real.exp (mass*F (x+T g))) (stdGaussian (Model.Vector N)))
    (hG : Integrable (fun g : Model.Vector N => Real.exp (mass*G (x+T g))) (stdGaussian (Model.Vector N)))
    (hFG : ∀ y,F y≤G y) : gaussianLogStep T mass F x≤gaussianLogStep T mass G x := by
  simp only [gaussianLogStep,if_neg hm.ne']
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (integral_exp_pos hF)
  exact integral_mono hF hG (fun g => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG _) hm.le))

/-- The dominating quadratic moment also proves the spherical exponential
moment exists; no integrability of the smaller terminal is assumed. -/
theorem gaussianLogStep_mono_add_const {N : ℕ} (T : Model.Vector N →L[ℝ] E)
    {mass : ℝ} (hm : 0<mass) {F G : E → ℝ} (hFm : Measurable F)
    (C : ℝ) (x : E)
    (hG : Integrable (fun g : Model.Vector N => Real.exp (mass*G (x+T g))) (stdGaussian (Model.Vector N)))
    (hFG : ∀ y,F y≤G y+C) :
    Integrable (fun g : Model.Vector N => Real.exp (mass*F (x+T g))) (stdGaussian (Model.Vector N)) ∧
      gaussianLogStep T mass F x≤gaussianLogStep T mass G x+C := by
  have hBound (g : Model.Vector N) : Real.exp (mass*F (x+T g))≤
      Real.exp (mass*C)*Real.exp (mass*G (x+T g)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hFG (x+T g)) hm.le]
  have hI : Integrable (fun g : Model.Vector N => Real.exp (mass*F (x+T g))) (stdGaussian (Model.Vector N)) := by
    apply (hG.const_mul (Real.exp (mass*C))).mono'
      ((Real.continuous_exp.measurable.comp ((hFm.comp (by fun_prop)).const_mul mass)).aestronglyMeasurable)
    filter_upwards [] with g
    dsimp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hBound g
  refine ⟨hI,?_⟩
  have hGC : Integrable (fun g : Model.Vector N => Real.exp (mass*(G (x+T g)+C)))
      (stdGaussian (Model.Vector N)) := by
    convert hG.const_mul (Real.exp (mass*C)) using 1
    funext g
    rw [mul_add,Real.exp_add]
    ring
  have H := gaussianLogStep_mono T hm x hI hGC hFG
  rw [gaussianLogStep_add_const T hm.ne' G C x (integral_exp_pos hG).ne'] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepOrder
