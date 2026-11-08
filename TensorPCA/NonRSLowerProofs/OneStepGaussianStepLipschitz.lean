-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- Adapted finite log-step comparison from pmaronow/arbitrary-rsb-palomar
-- @5162e2d15b440ce46fd322f20eb429468d601948,
-- vendor/spin-glass-foundations/Targets/CascadeDerivPi.lean (Apache-2.0).
-- The terminal space and continuous linear Gaussian shift are generalized;
-- the measure is Mathlib's actual stdGaussian on Model.Vector N.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltStepDerivative

/-! Terminal-independent finite Gaussian log-step Lipschitz preservation.
All growth, integrability and positive-normalizer claims follow from the
single Lipschitz hypothesis; every real mass, including zero, is covered. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTiltStepDerivative
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

def gaussianNormalizer {N : ℕ} (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  ∫ g : Model.Vector N, Real.exp (mass*F (x+T g)) ∂stdGaussian (Model.Vector N)

def gaussianLogStep {N : ℕ} (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  if mass = 0 then ∫ g : Model.Vector N, F (x+T g) ∂stdGaussian (Model.Vector N)
  else Real.log (gaussianNormalizer T mass F x)/mass

theorem shifted_deviation {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (x : E) (g : Model.Vector N) :
    |F (x+T g)-F x| ≤ (L : ℝ)*‖T‖*‖g‖ := by
  have h := hF.dist_le_mul (x+T g) x
  have hh : |F (x+T g)-F x| ≤ (L : ℝ)*‖T g‖ := by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, add_sub_cancel_left] using h
  exact hh.trans ((mul_le_mul_of_nonneg_left (T.le_opNorm g) L.coe_nonneg).trans_eq (by ring))

theorem shifted_linear_growth {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (x : E) (g : Model.Vector N) :
    |F (x+T g)| ≤ |F x|+(L : ℝ)*‖T‖*‖g‖ := by
  have h := shifted_deviation hF T x g
  have hh := abs_add_le (F (x+T g)-F x) (F x)
  rw [sub_add_cancel] at hh
  linarith

theorem shifted_integrable {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (x : E) :
    Integrable (fun g : Model.Vector N ↦ F (x+T g)) (stdGaussian (Model.Vector N)) := by
  apply integrable_of_linear_growth (hF.continuous.measurable.comp (by fun_prop))
  exact shifted_linear_growth hF T x

theorem shifted_exp_integrable {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) :
    Integrable (fun g : Model.Vector N ↦ Real.exp (mass*F (x+T g))) (stdGaussian (Model.Vector N)) := by
  apply integrable_exp_of_linear_growth (hF.continuous.measurable.comp (by fun_prop))
    (shifted_linear_growth hF T x) mass

theorem gaussianNormalizer_pos {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x : E) : 0 < gaussianNormalizer T mass F x :=
  integral_exp_pos (shifted_exp_integrable hF T mass x)

theorem gaussianNormalizer_comparison {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x y : E) :
    gaussianNormalizer T mass F x ≤
      Real.exp (|mass| *(L : ℝ)*dist x y)*gaussianNormalizer T mass F y := by
  unfold gaussianNormalizer
  rw [← integral_const_mul]
  apply integral_mono (shifted_exp_integrable hF T mass x)
    ((shifted_exp_integrable hF T mass y).const_mul _)
  intro g
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hxy : |F (x+T g)-F (y+T g)| ≤ (L : ℝ)*dist x y := by
    simpa only [Real.dist_eq, dist_add_right] using hF.dist_le_mul (x+T g) (y+T g)
  have h := (le_abs_self (mass*(F (x+T g)-F (y+T g)))).trans
    ((abs_mul _ _).trans_le (mul_le_mul_of_nonneg_left hxy (abs_nonneg mass)))
  nlinarith

theorem gaussianLogStep_dist_le {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) (x y : E) :
    |gaussianLogStep T mass F x-gaussianLogStep T mass F y| ≤ (L : ℝ)*dist x y := by
  by_cases hm : mass = 0
  · simp only [gaussianLogStep, if_pos hm]
    rw [← integral_sub (shifted_integrable hF T x) (shifted_integrable hF T y)]
    have hh : ∀ᵐ g : Model.Vector N ∂stdGaussian (Model.Vector N),
        ‖F (x+T g)-F (y+T g)‖ ≤ (L : ℝ)*dist x y := by
      apply Eventually.of_forall
      intro g
      simpa only [Real.norm_eq_abs, Real.dist_eq, dist_add_right] using
        hF.dist_le_mul (x+T g) (y+T g)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hh
  · simp only [gaussianLogStep, if_neg hm]
    have hx := gaussianNormalizer_pos hF T mass x
    have hy := gaussianNormalizer_pos hF T mass y
    have h1 := Real.log_le_log hx (gaussianNormalizer_comparison hF T mass x y)
    have h2 := Real.log_le_log hy (gaussianNormalizer_comparison hF T mass y x)
    rw [Real.log_mul (Real.exp_pos _).ne' hy.ne', Real.log_exp] at h1
    rw [Real.log_mul (Real.exp_pos _).ne' hx.ne', Real.log_exp, dist_comm y x] at h2
    rw [← sub_div, abs_div, div_le_iff₀ (abs_pos.mpr hm), abs_le]
    constructor <;> nlinarith

theorem gaussianLogStep_lipschitz {N : ℕ} {L : ℝ≥0} {F : E → ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector N →L[ℝ] E) (mass : ℝ) : LipschitzWith L (gaussianLogStep T mass F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq] using gaussianLogStep_dist_le hF T mass x y

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz
