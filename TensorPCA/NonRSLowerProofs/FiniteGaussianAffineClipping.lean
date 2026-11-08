-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianAffineBarrier
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLinearLogSteps

/-! A bounded positive-mark clamp of an affine Gaussian terminal has a tower error
controlled by total variance, uniformly in depth.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianAffineClipping
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz OneStepGaussianAffineBarrier
open FiniteGaussianAffineBarrier FiniteGaussianLogStepsCompression FiniteGaussianLinearLogSteps
open scoped RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def logClamp (b cap z : ℝ) : ℝ := max (Real.log b) (min z (Real.log cap))

theorem logClamp_eq_log_mark {b cap : ℝ} (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap) (z : ℝ) :
    logClamp b cap z=Real.log (max b (min (Real.exp z) cap)) := by
  have hLogbc := Real.log_le_log hb hbc
  by_cases hHigh : cap≤Real.exp z
  · have hz : Real.log cap≤z := by simpa only [Real.log_exp] using Real.log_le_log hcap hHigh
    simp only [logClamp,min_eq_right hz,max_eq_right hLogbc,min_eq_right hHigh,max_eq_right hbc]
  · have hzcap : Real.exp z≤cap := le_of_not_ge hHigh
    by_cases hLow : Real.exp z≤b
    · have hz : z≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hLow
      simp only [logClamp,min_eq_left (hz.trans hLogbc),max_eq_left hz,min_eq_left hzcap,max_eq_left hLow]
    · have hzb : b≤Real.exp z := le_of_not_ge hLow
      have hz0 : Real.log b≤z := by simpa only [Real.log_exp] using Real.log_le_log hb hzb
      have hz1 : z≤Real.log cap := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos z) hzcap
      simp only [logClamp,min_eq_left hz1,max_eq_right hz0,min_eq_left hzcap,max_eq_right hzb,Real.log_exp]

theorem logClamp_error_le {b cap : ℝ} (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap) (z : ℝ) :
    |z-logClamp b cap z|≤cap⁻¹*Real.exp z+b*Real.exp (-z) := by
  have hLogbc := Real.log_le_log hb hbc
  by_cases hLow : z≤Real.log b
  · rw [logClamp,min_eq_left (hLow.trans hLogbc),max_eq_left hLow,
      abs_of_nonpos (sub_nonpos.mpr hLow)]
    have H : Real.log b-z≤b*Real.exp (-z) := by
      calc
        _ ≤ Real.exp (Real.log b-z) := by linarith [Real.add_one_le_exp (Real.log b-z)]
        _ = _ := by rw [Real.exp_sub,Real.exp_log hb,Real.exp_neg]; simp only [div_eq_mul_inv]
    have HP : 0≤cap⁻¹*Real.exp z := mul_nonneg (inv_nonneg.mpr hcap.le) (Real.exp_pos _).le
    linarith
  · have hLo : Real.log b≤z := le_of_not_ge hLow
    by_cases hHigh : Real.log cap≤z
    · rw [logClamp,min_eq_right hHigh,max_eq_right hLogbc,abs_of_nonneg (sub_nonneg.mpr hHigh)]
      have H : z-Real.log cap≤cap⁻¹*Real.exp z := by
        calc
          _ ≤ Real.exp (z-Real.log cap) := by linarith [Real.add_one_le_exp (z-Real.log cap)]
          _ = _ := by rw [Real.exp_sub,Real.exp_log hcap]; simp only [div_eq_mul_inv,mul_comm]
      have HP : 0≤b*Real.exp (-z) := mul_nonneg hb.le (Real.exp_pos _).le
      linarith
    · have hHi : z≤Real.log cap := le_of_not_ge hHigh
      rw [logClamp,min_eq_left hHi,max_eq_right hLo,sub_self,abs_zero]
      positivity

theorem linear_logClamp_lipschitz {N : ℕ} (lambda : Model.Vector N) (b cap : ℝ) :
    LipschitzWith ‖lambda‖₊ (fun x : Model.Vector N => logClamp b cap (inner ℝ lambda x)) := by
  have hF : LipschitzWith ‖lambda‖₊ (fun x : Model.Vector N => inner ℝ lambda x) := by
    simpa only [zero_add] using affine_lipschitz lambda 0
  exact (hF.min_const (Real.log cap)).const_max (Real.log b)

theorem affine_tower_logClamp_error {N : ℕ} (lambda : Model.Vector N) (steps : List (ℝ×ℝ))
    (hDelta : ∀p∈steps,0≤p.2) (hMass : ∀p∈steps,|p.1|≤1) {b cap Y : ℝ}
    (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap) (hY : (steps.map Prod.snd).sum≤Y) :
    |gaussianLogSteps (isotropicSteps N steps) (fun h => inner ℝ lambda h) 0-
      gaussianLogSteps (isotropicSteps N steps) (fun h => logClamp b cap (inner ℝ lambda h)) 0|≤
      (b+cap⁻¹)*Real.exp (3/2*‖lambda‖^2*Y) := by
  have hF : LipschitzWith ‖lambda‖₊ (fun h : Model.Vector N => inner ℝ lambda h) := by
    simpa only [zero_add] using affine_lipschitz lambda 0
  have hErr (h : Model.Vector N) : |inner ℝ lambda h-logClamp b cap (inner ℝ lambda h)|≤
      affineBarrier lambda cap⁻¹ b h := by
    simpa only [affineBarrier,inner_neg_left] using logClamp_error_le hb hcap hbc (inner ℝ lambda h)
  have H := gaussianLogSteps_affineBarrier_at_zero hF (linear_logClamp_lipschitz lambda b cap)
    steps hDelta hMass lambda (le_refl ‖lambda‖) (inv_nonneg.mpr hcap.le) hb.le hErr hY
  simpa only [coe_nnnorm,add_comm] using H

theorem affine_tower_positive_mark_clamp_error {N : ℕ} (lambda : Model.Vector N) (steps : List (ℝ×ℝ))
    (hDelta : ∀p∈steps,0≤p.2) (hMass : ∀p∈steps,|p.1|≤1) {b cap Y : ℝ}
    (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap) (hY : (steps.map Prod.snd).sum≤Y) :
    |gaussianLogSteps (isotropicSteps N steps) (fun h => inner ℝ lambda h) 0-
      gaussianLogSteps (isotropicSteps N steps)
        (fun h => Real.log (max b (min (Real.exp (inner ℝ lambda h)) cap))) 0|≤
      (b+cap⁻¹)*Real.exp (3/2*‖lambda‖^2*Y) := by
  simpa only [logClamp_eq_log_mark hb hcap hbc] using
    affine_tower_logClamp_error lambda steps hDelta hMass hb hcap hbc hY

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianAffineClipping
