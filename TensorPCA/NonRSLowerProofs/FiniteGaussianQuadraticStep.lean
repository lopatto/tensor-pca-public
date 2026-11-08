-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepOrder
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepTiltMoment
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint

/-! A finite Gaussian quadratic log step and its normalized fresh Gaussian law. No
quadratic function is assumed Lipschitz.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz OneStepGaussianStepOrder OneStepGaussianStepTiltMoment
open OneStepGaussianTilt OneStepGaussianTiltLaw OneStepGaussianTiltJoint
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def quadratic {M : ℕ} (C P : ℝ) (h : Model.Vector M) : ℝ := C+‖h‖^2/(2*P)

def shift (M : ℕ) (Delta : ℝ) : Model.Vector M→L[ℝ] Model.Vector M :=
  Real.sqrt Delta • ContinuousLinearMap.id ℝ (Model.Vector M)

theorem shifted_quadratic_exponent {M : ℕ} (C P Delta mass : ℝ) (h g : Model.Vector M) :
    mass*quadratic C P (h+shift M Delta g)=mass*C+tiltExponent P Delta mass h g := by
  simp only [quadratic,shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,tiltExponent]
  ring

theorem quadratic_exp_integrable {M : ℕ} {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) (h : Model.Vector M) :
    Integrable (fun g : Model.Vector M => Real.exp (mass*quadratic C P (h+shift M Delta g)))
      (stdGaussian (Model.Vector M)) := by
  have H := (tiltExponent_exp_integrable hP hDelta hD h).const_mul (Real.exp (mass*C))
  apply H.congr
  exact .of_forall fun g => by dsimp only; rw [shifted_quadratic_exponent,Real.exp_add]

theorem quadratic_normalizer_eq {M : ℕ} (C P Delta mass : ℝ) (h : Model.Vector M) :
    gaussianNormalizer (shift M Delta) mass (quadratic C P) h=
      Real.exp (mass*C)*(∫g,Real.exp (tiltExponent P Delta mass h g)∂stdGaussian (Model.Vector M)) := by
  unfold gaussianNormalizer
  simp_rw [shifted_quadratic_exponent,Real.exp_add]
  rw [integral_const_mul]

theorem gaussianLogStep_quadratic {M : ℕ} {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hmass : mass≠0) (hD : 0< P-mass*Delta)
    (C : ℝ) (h : Model.Vector M) :
    gaussianLogStep (shift M Delta) mass (quadratic C P) h=
      C+(M : ℝ)*Real.log (P/(P-mass*Delta))/(2*mass)+‖h‖^2/(2*(P-mass*Delta)) := by
  simp only [gaussianLogStep,if_neg hmass]
  rw [quadratic_normalizer_eq,Real.log_mul (Real.exp_ne_zero _)
    (integral_exp_pos (tiltExponent_exp_integrable hP hDelta hD h)).ne',Real.log_exp,
    log_integral_exp_tiltExponent hP hDelta hD]
  simp only [Model.Vector,finrank_euclideanSpace,Fintype.card_fin]
  field_simp [hmass,hD.ne']
  ring

theorem gaussianTilt_quadratic_eq_affine {M : ℕ} {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) (h : Model.Vector M) :
    gaussianTilt (shift M Delta) mass (quadratic C P) h=
      (stdGaussian (Model.Vector M)).map (fun g => (mass*Real.sqrt Delta/(P-mass*Delta)) •h+
        Real.sqrt (P/(P-mass*Delta)) •g) := by
  have hfun : (fun g : Model.Vector M => mass*quadratic C P (h+shift M Delta g))=
      (fun _ => mass*C)+tiltExponent P Delta mass h := by
    funext g
    exact shifted_quadratic_exponent C P Delta mass h g
  have hCancel := tilted_tilted (μ := stdGaussian (Model.Vector M))
    (integrable_const (Real.exp (mass*C))) (tiltExponent P Delta mass h)
  rw [tilted_const] at hCancel
  unfold gaussianTilt
  rw [hfun,← hCancel]
  exact tilted_endpoint_eq_affine_gaussian hP hDelta hD h

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep
