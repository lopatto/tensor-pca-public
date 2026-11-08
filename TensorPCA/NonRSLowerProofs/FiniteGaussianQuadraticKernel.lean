-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianAffineKernel

/-! Tilted fresh-bank and spin kernels for the quadratic Gaussian spine.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticKernel
open MeasureTheory ProbabilityTheory
open FiniteGaussianQuadraticStep FiniteGaussianAffineKernel
open OneStepGaussianStepTiltMoment OneStepGaussianTiltLaw
open scoped RealInnerProductSpace ProbabilityTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quadratic_transition_law {M : ℕ} {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta)
    (C : ℝ) (h : Model.Vector M) :
    (gaussianTilt (shift M Delta) mass (quadratic C P) h).map
        (fun g => h+Real.sqrt Delta •g)=
      affineKernel M (P/(P-mass*Delta))
        (Real.sqrt (Delta*P/(P-mass*Delta))) h := by
  rw [gaussianTilt_quadratic_eq_affine hP hDelta hD,
    Measure.map_map (by fun_prop) (by fun_prop),affineKernel_apply]
  have hmean : 1+Real.sqrt Delta*(mass*Real.sqrt Delta/(P-mass*Delta))=
      P/(P-mass*Delta) := by
    field_simp [hD.ne']
    rw [Real.sq_sqrt hDelta]
    ring
  have hnoise : Real.sqrt Delta*Real.sqrt (P/(P-mass*Delta))=
      Real.sqrt (Delta*P/(P-mass*Delta)) := by
    rw [← Real.sqrt_mul hDelta]
    congr 1
    ring
  apply congrArg (fun f : Model.Vector M→Model.Vector M =>
    (stdGaussian (Model.Vector M)).map f)
  funext g
  dsimp only [Function.comp_apply]
  calc
    h+Real.sqrt Delta •((mass*Real.sqrt Delta/(P-mass*Delta)) •h+
        Real.sqrt (P/(P-mass*Delta)) •g)=
      (1+Real.sqrt Delta*(mass*Real.sqrt Delta/(P-mass*Delta))) •h+
        (Real.sqrt Delta*Real.sqrt (P/(P-mass*Delta))) •g := by module
    _ = _ := by rw [hmean,hnoise]

def freshKernel (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    Kernel (Model.Vector M) (Model.Vector M) where
  toFun h := gaussianTilt (shift M Delta) mass (quadratic C P) h
  measurable' := by
    have H : (fun h : Model.Vector M =>
        gaussianTilt (shift M Delta) mass (quadratic C P) h)=
        (fun h => affineKernel M (mass*Real.sqrt Delta/(P-mass*Delta))
          (Real.sqrt (P/(P-mass*Delta))) h) := by
      funext h
      rw [gaussianTilt_quadratic_eq_affine hP hDelta hD,affineKernel_apply]
    rw [H]
    exact Kernel.measurable _

theorem freshKernel_eq_affine (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    freshKernel M hP hDelta hD C=
      affineKernel M (mass*Real.sqrt Delta/(P-mass*Delta))
        (Real.sqrt (P/(P-mass*Delta))) := by
  apply Kernel.ext
  intro h
  exact (gaussianTilt_quadratic_eq_affine hP hDelta hD C h).trans
    (affineKernel_apply _ _ _ _).symm

instance freshKernel_markov (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    IsMarkovKernel (freshKernel M hP hDelta hD C) := by
  rw [freshKernel_eq_affine]
  infer_instance

def transitionKernel (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    Kernel (Model.Vector M) (Model.Vector M) where
  toFun h := (freshKernel M hP hDelta hD C h).map (fun g => h+Real.sqrt Delta •g)
  measurable' := by
    have H : (fun h : Model.Vector M =>
        (freshKernel M hP hDelta hD C h).map (fun g => h+Real.sqrt Delta •g))=
        (fun h => affineKernel M (P/(P-mass*Delta))
          (Real.sqrt (Delta*P/(P-mass*Delta))) h) := by
      funext h
      exact quadratic_transition_law hP hDelta hD C h
    rw [H]
    exact Kernel.measurable _

theorem transitionKernel_eq_affine (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    transitionKernel M hP hDelta hD C=
      affineKernel M (P/(P-mass*Delta)) (Real.sqrt (Delta*P/(P-mass*Delta))) := by
  apply Kernel.ext
  intro h
  exact quadratic_transition_law hP hDelta hD C h

instance transitionKernel_markov (M : ℕ) {P Delta mass : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (C : ℝ) :
    IsMarkovKernel (transitionKernel M hP hDelta hD C) := by
  rw [transitionKernel_eq_affine]
  infer_instance

def terminalSpinKernel (M : ℕ) {B : ℝ} (hB : 0< B) :
    Kernel (Model.Vector M) (Model.Vector M) where
  toFun h := (stdGaussian (Model.Vector M)).tilted
    (fun sigma => inner ℝ h sigma-(B-1)/2*‖sigma‖^2)
  measurable' := by
    have H : (fun h : Model.Vector M => (stdGaussian (Model.Vector M)).tilted
        (fun sigma => inner ℝ h sigma-(B-1)/2*‖sigma‖^2))=
        (fun h => affineKernel M B⁻¹ (Real.sqrt B⁻¹) h) := by
      funext h
      rw [tilted_quadratic_eq_affine_gaussian hB,affineKernel_apply]
    rw [H]
    exact Kernel.measurable _

theorem terminalSpinKernel_eq_affine (M : ℕ) {B : ℝ} (hB : 0< B) :
    terminalSpinKernel M hB=affineKernel M B⁻¹ (Real.sqrt B⁻¹) := by
  apply Kernel.ext
  intro h
  exact (tilted_quadratic_eq_affine_gaussian hB h).trans
    (affineKernel_apply _ _ _ _).symm

instance terminalSpinKernel_markov (M : ℕ) {B : ℝ} (hB : 0< B) :
    IsMarkovKernel (terminalSpinKernel M hB) := by
  rw [terminalSpinKernel_eq_affine]
  infer_instance

theorem conditional_spin_comp (M : ℕ) {P Delta mass V : ℝ}
    (hP : 0< P) (hDelta : 0≤ Delta) (hD : 0< P-mass*Delta) (hV : 0≤ V) (C : ℝ) :
    affineKernel M P⁻¹ (Real.sqrt V) ∘ₖ transitionKernel M hP hDelta hD C=
      affineKernel M (P-mass*Delta)⁻¹
        (Real.sqrt (V+Delta/((P-mass*Delta)*P))) := by
  rw [transitionKernel_eq_affine,affineKernel_comp]
  have hmean : P⁻¹*(P/(P-mass*Delta))=(P-mass*Delta)⁻¹ := by
    field_simp
  have hnoise : (P⁻¹*Real.sqrt (Delta*P/(P-mass*Delta)))^2+(Real.sqrt V)^2=
      V+Delta/((P-mass*Delta)*P) := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg (mul_nonneg hDelta hP.le) hD.le),Real.sq_sqrt hV]
    field_simp
    <;> ring
  rw [hmean,hnoise]

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticKernel
