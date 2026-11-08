-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz

/-! Order and constant stability of the literal Gaussian log step. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitzOrder
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem gaussianLogStep_add_const {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    (mass c : ℝ) (x : E) :
    gaussianLogStep T mass (fun y ↦ F y+c) x=gaussianLogStep T mass F x+c := by
  by_cases hm : mass=0
  · simp only [gaussianLogStep,if_pos hm]
    rw [integral_add (shifted_integrable hF T x) (integrable_const c),integral_const]
    simp
  have hZ : gaussianNormalizer T mass (fun y ↦ F y+c) x=
      Real.exp (mass*c)*gaussianNormalizer T mass F x := by
    unfold gaussianNormalizer
    rw [← integral_const_mul]
    congr 1
    funext g
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gaussianLogStep,if_neg hm]
  rw [hZ,Real.log_mul (Real.exp_pos _).ne' (gaussianNormalizer_pos hF T mass x).ne',Real.log_exp]
  field_simp
  ring

theorem gaussianLogStep_mono {N : ℕ} {L K : ℝ≥0} {F G : E → ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N →L[ℝ] E) {mass : ℝ} (hmass : 0≤mass)
    (hFG : ∀y,F y≤G y) (x : E) :
    gaussianLogStep T mass F x≤gaussianLogStep T mass G x := by
  by_cases hm : mass=0
  · simp only [gaussianLogStep,if_pos hm]
    exact integral_mono (shifted_integrable hF T x) (shifted_integrable hG T x) (fun g ↦ hFG _)
  have hmpos : 0<mass := lt_of_le_of_ne hmass (Ne.symm hm)
  have hZ : gaussianNormalizer T mass F x≤gaussianNormalizer T mass G x := by
    apply integral_mono (shifted_exp_integrable hF T mass x) (shifted_exp_integrable hG T mass x)
    intro g
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG _) hmass)
  simp only [gaussianLogStep,if_neg hm]
  exact div_le_div_of_nonneg_right (Real.log_le_log (gaussianNormalizer_pos hF T mass x) hZ) hmpos.le

theorem gaussianLogStep_sub_le {N : ℕ} {L K : ℝ≥0} {F G : E → ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N →L[ℝ] E) {mass : ℝ} (hmass : 0≤mass)
    {c : ℝ} (hFG : ∀y,F y-G y≤c) (x : E) :
    gaussianLogStep T mass F x-gaussianLogStep T mass G x≤c := by
  have hGc : LipschitzWith K (fun y ↦ G y+c) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_add_right] using hG.dist_le_mul y z
  have H := gaussianLogStep_mono hF hGc T hmass (fun y ↦ by have H := hFG y; linarith) x
  rw [gaussianLogStep_add_const hG T mass c x] at H
  linarith

theorem gaussianLogStep_abs_sub_le {N : ℕ} {L K : ℝ≥0} {F G : E → ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (T : Model.Vector N →L[ℝ] E) {mass : ℝ} (hmass : 0≤mass)
    {c : ℝ} (hFG : ∀y,|F y-G y|≤c) (x : E) :
    |gaussianLogStep T mass F x-gaussianLogStep T mass G x|≤c := by
  rw [abs_le]
  constructor
  · have H := gaussianLogStep_sub_le hG hF T hmass (fun y ↦ by have H := (abs_le.mp (hFG y)).1; linarith) x
    linarith
  · exact gaussianLogStep_sub_le hF hG T hmass (fun y ↦ (abs_le.mp (hFG y)).2) x

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitzOrder
