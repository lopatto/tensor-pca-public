-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepWeightedStability
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLaw

/-! Linear exponential moments under a Lipschitz Gaussian tilt. The Cameron-Martin shift
gives a depth-independent bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLinearMGF
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz OneStepGaussianStepTiltMoment
open OneStepGaussianStepWeightedStability OneStepGaussianTiltLaw
open GaussianDensityProofs
open scoped RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem linear_tilt_eq_gaussian_shift {N : ℕ} (w : Model.Vector N) :
    (stdGaussian (Model.Vector N)).tilted (fun g => inner ℝ w g)=
      (stdGaussian (Model.Vector N)).map (fun g => w+g) := by
  simpa only [sub_self,zero_div,zero_mul,sub_zero,inv_one,Real.sqrt_one,one_smul] using
    tilted_quadratic_eq_affine_gaussian (E := Model.Vector N) (z := 1) (by norm_num) w

theorem cameronMartin_exp_integrable {N : ℕ} {L : ℝ≥0} {K : E→ℝ}
    (hK : LipschitzWith L K) (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) (w : Model.Vector N) :
    Integrable (fun g : Model.Vector N =>
      Real.exp (inner ℝ w g)*Real.exp (mass*K (x+T g))) (stdGaussian (Model.Vector N)) := by
  have hM : Measurable (fun g : Model.Vector N => Real.exp (mass*K (x+T g))) :=
    (Real.continuous_exp.comp ((hK.continuous.comp (continuous_const.add T.continuous)).const_mul mass)).measurable
  have hShift : Integrable (fun g : Model.Vector N => Real.exp (mass*K (x+T g)))
      ((stdGaussian (Model.Vector N)).map (fun g => w+g)) := by
    apply (integrable_map_measure hM.aestronglyMeasurable (by fun_prop)).mpr
    convert shifted_exp_integrable hK T mass (x+T w) using 1
    funext g
    simp only [Function.comp_def,map_add,add_assoc]
  rw [← linear_tilt_eq_gaussian_shift w] at hShift
  have hE : Integrable (fun g : Model.Vector N => Real.exp (inner ℝ w g)) (stdGaussian (Model.Vector N)) := by
    simpa only [sub_self,zero_div,zero_mul,sub_zero] using
      GaussianMomentProofs.integrable_exp_quadratic (z := 1) (by norm_num) w
  exact (integrable_tilted_iff hE _).mp hShift

theorem cameronMartin_exp_integral {N : ℕ} {L : ℝ≥0} {K : E→ℝ}
    (hK : LipschitzWith L K) (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) (w : Model.Vector N) :
    (∫g : Model.Vector N,Real.exp (inner ℝ w g)*Real.exp (mass*K (x+T g))
      ∂stdGaussian (Model.Vector N))=
      Real.exp (‖w‖^2/2)*gaussianNormalizer T mass K (x+T w) := by
  have hM : Measurable (fun g : Model.Vector N => Real.exp (mass*K (x+T g))) :=
    (Real.continuous_exp.comp ((hK.continuous.comp (continuous_const.add T.continuous)).const_mul mass)).measurable
  have H : (∫g : Model.Vector N,Real.exp (mass*K (x+T g))
      ∂(stdGaussian (Model.Vector N)).tilted (fun g => inner ℝ w g))=
      gaussianNormalizer T mass K (x+T w) := by
    rw [linear_tilt_eq_gaussian_shift w,integral_map (by fun_prop) hM.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro g
    simp only [map_add,add_assoc]
  rw [integral_tilted] at H
  simp only [smul_eq_mul] at H
  have hMGF : (∫g : Model.Vector N,Real.exp (inner ℝ w g)∂stdGaussian (Model.Vector N))=
      Real.exp (‖w‖^2/2) := by simpa using integral_exp_inner_stdGaussian w 1
  rw [hMGF] at H
  have hfun : (fun g : Model.Vector N =>
      Real.exp (inner ℝ w g)/Real.exp (‖w‖^2/2)*Real.exp (mass*K (x+T g)))=
      (fun g => (Real.exp (inner ℝ w g)*Real.exp (mass*K (x+T g)))/Real.exp (‖w‖^2/2)) := by
    funext g
    ring
  rw [hfun,integral_div] at H
  exact (div_eq_iff (Real.exp_pos _).ne').mp H |>.trans (by ring)

theorem tilted_linear_exp_integrable {N : ℕ} {L : ℝ≥0} {K : E→ℝ}
    (hK : LipschitzWith L K) (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) (w : Model.Vector N) :
    Integrable (fun g : Model.Vector N => Real.exp (inner ℝ w g)) (gaussianTilt T mass K x) := by
  apply (integrable_tilted_iff (shifted_exp_integrable hK T mass x) _).mpr
  simpa only [smul_eq_mul,mul_comm] using cameronMartin_exp_integrable hK T mass x w

theorem tilted_linear_mgf_eq {N : ℕ} {L : ℝ≥0} {K : E→ℝ}
    (hK : LipschitzWith L K) (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) (w : Model.Vector N) :
    (∫g : Model.Vector N,Real.exp (inner ℝ w g)∂gaussianTilt T mass K x)=
      Real.exp (‖w‖^2/2)*gaussianNormalizer T mass K (x+T w)/gaussianNormalizer T mass K x := by
  unfold gaussianTilt
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have hfun : (fun g : Model.Vector N =>
      Real.exp (mass*K (x+T g))/gaussianNormalizer T mass K x*Real.exp (inner ℝ w g))=
      (fun g => (Real.exp (inner ℝ w g)*Real.exp (mass*K (x+T g)))/gaussianNormalizer T mass K x) := by
    funext g
    ring
  change (∫g : Model.Vector N,Real.exp (mass*K (x+T g))/gaussianNormalizer T mass K x*
    Real.exp (inner ℝ w g)∂stdGaussian (Model.Vector N))=_
  rw [hfun,integral_div,cameronMartin_exp_integral hK T mass x w]

theorem tilted_linear_mgf_le {N : ℕ} {L : ℝ≥0} {K : E→ℝ}
    (hK : LipschitzWith L K) (T : Model.Vector N→L[ℝ]E) (mass : ℝ) (x : E) (w : Model.Vector N) :
    (∫g : Model.Vector N,Real.exp (inner ℝ w g)∂gaussianTilt T mass K x)≤
      Real.exp (‖w‖^2/2+|mass| *(L : ℝ)*‖T w‖) := by
  rw [tilted_linear_mgf_eq hK T mass x w]
  have H := gaussianNormalizer_comparison hK T mass (x+T w) x
  have hz := gaussianNormalizer_pos hK T mass x
  have hDist : dist (x+T w) x=‖T w‖ := by simp [dist_eq_norm]
  rw [hDist] at H
  calc
    _ ≤ Real.exp (‖w‖^2/2)*(Real.exp (|mass| *(L : ℝ)*‖T w‖)*gaussianNormalizer T mass K x)/
        gaussianNormalizer T mass K x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le) hz.le
    _ = _ := by rw [mul_div_assoc,mul_div_cancel_right₀ _ hz.ne',← Real.exp_add]

theorem isotropic_tilted_linear_mgf_le {N : ℕ} {L : ℝ≥0} {K : Model.Vector N→ℝ}
    (hK : LipschitzWith L K) {Delta : ℝ} (hDelta : 0≤Delta)
    (mass : ℝ) (x lambda : Model.Vector N) :
    (∫g : Model.Vector N,Real.exp (inner ℝ lambda (Real.sqrt Delta •g))
      ∂gaussianTilt (Real.sqrt Delta •ContinuousLinearMap.id ℝ (Model.Vector N)) mass K x)≤
      Real.exp (Delta*‖lambda‖^2/2+|mass| *(L : ℝ)*Delta*‖lambda‖) := by
  let T := Real.sqrt Delta •ContinuousLinearMap.id ℝ (Model.Vector N)
  have H := tilted_linear_mgf_le hK T mass x (Real.sqrt Delta •lambda)
  have hfun : (fun g : Model.Vector N => Real.exp (inner ℝ lambda (Real.sqrt Delta •g)))=
      (fun g => Real.exp (inner ℝ (Real.sqrt Delta •lambda) g)) := by
    funext g
    simp only [inner_smul_right,real_inner_smul_left]
  rw [hfun]
  have hTw : T (Real.sqrt Delta •lambda)=Delta •lambda := by
    simp only [T,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_smul]
    rw [← sq,Real.sq_sqrt hDelta]
  have hNorm : ‖Real.sqrt Delta •lambda‖^2=Delta*‖lambda‖^2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hDelta]
  rw [hTw,hNorm,norm_smul,Real.norm_eq_abs,abs_of_nonneg hDelta] at H
  convert H using 1 <;> ring


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLinearMGF
