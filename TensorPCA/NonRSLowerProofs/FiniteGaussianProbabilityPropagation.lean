-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianQuadraticStep

/-! Probability lower bounds propagate through ordered positive Gaussian log steps.
Unbounded quadratic exponential moments remain explicit.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianProbabilityPropagation
open MeasureTheory ProbabilityTheory Set
open OneStepGaussianStepLipschitz OneStepGaussianStepTiltMoment
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem probability_le_exp_smaller_mass {p D mass nextMass : ℝ}
    (hp : p∈Icc (0 : ℝ) 1) (hm : 0≤ mass) (hOrder : mass≤nextMass)
    (hBound : p≤Real.exp (nextMass*D)) : p≤Real.exp (mass*D) := by
  by_cases hD : 0≤ D
  · exact hp.2.trans (Real.one_le_exp (mul_nonneg hm hD))
  · apply hBound.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right hOrder (le_of_not_ge hD)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem gaussianLogStep_probability_lower {N : ℕ}
    (T : Model.Vector N→L[ℝ] E) {mass nextMass : ℝ}
    (hm : 0< mass) (hOrder : mass≤nextMass)
    (F H p : E→ℝ) (K : ℝ) (hp : Measurable p) (hp01 : ∀z,p z∈Icc (0 : ℝ) 1)
    (hBound : ∀z,p z≤Real.exp (nextMass*(F z-H z-K))) (z : E)
    (hF : Integrable (fun g : Model.Vector N => Real.exp (mass*F (z+T g)))
      (stdGaussian (Model.Vector N)))
    (hH : Integrable (fun g : Model.Vector N => Real.exp (mass*H (z+T g)))
      (stdGaussian (Model.Vector N))) :
    (∫g,p (z+T g)∂gaussianTilt T mass H z)≤
      Real.exp (mass*(gaussianLogStep T mass F z-gaussianLogStep T mass H z-K)) := by
  let fH := fun g : Model.Vector N => mass*H (z+T g)
  let fDiff := fun g : Model.Vector N => mass*(F (z+T g)-H (z+T g)-K)
  haveI : IsProbabilityMeasure ((stdGaussian (Model.Vector N)).tilted fH) :=
    isProbabilityMeasure_tilted hH
  have hpm : Measurable (fun g : Model.Vector N => p (z+T g)) := hp.comp (by fun_prop)
  have hpi : Integrable (fun g : Model.Vector N => p (z+T g))
      ((stdGaussian (Model.Vector N)).tilted fH) :=
    (integrable_const (1 : ℝ)).mono' hpm.aestronglyMeasurable
      (.of_forall (fun g => by rw [Real.norm_eq_abs,abs_of_nonneg (hp01 _).1]; exact (hp01 _).2))
  have hEi : Integrable (fun g : Model.Vector N => Real.exp (fDiff g))
      ((stdGaussian (Model.Vector N)).tilted fH) := by
    apply (integrable_tilted_iff hH _).mpr
    convert hF.const_mul (Real.exp (-mass*K)) using 1
    funext g
    dsimp only [fH,fDiff]
    simp only [smul_eq_mul,← Real.exp_add]
    congr 1
    ring
  have hCompare : (∫g,p (z+T g)∂gaussianTilt T mass H z)≤
      ∫g,Real.exp (fDiff g)∂(stdGaussian (Model.Vector N)).tilted fH :=
    integral_mono hpi hEi (fun g => probability_le_exp_smaller_mass
      (hp01 _) hm.le hOrder (hBound _))
  have hZF : 0< gaussianNormalizer T mass F z := integral_exp_pos hF
  have hZH : 0< gaussianNormalizer T mass H z := integral_exp_pos hH
  have hIntegral : (∫g,Real.exp (fDiff g)∂(stdGaussian (Model.Vector N)).tilted fH)=
      gaussianNormalizer T mass F z/Real.exp (mass*K)/gaussianNormalizer T mass H z := by
    rw [integral_exp_tilted]
    have heq : fH+fDiff=(fun g => mass*F (z+T g)-mass*K) := by
      funext g
      dsimp only [Pi.add_apply,fH,fDiff]
      ring
    rw [heq]
    simp_rw [Real.exp_sub]
    rw [integral_div]
    rfl
  have hExp : Real.exp (mass*(gaussianLogStep T mass F z-gaussianLogStep T mass H z-K))=
      gaussianNormalizer T mass F z/Real.exp (mass*K)/gaussianNormalizer T mass H z := by
    simp only [gaussianLogStep,if_neg hm.ne']
    have heq : mass*(Real.log (gaussianNormalizer T mass F z)/mass-
        Real.log (gaussianNormalizer T mass H z)/mass-K)=
        Real.log (gaussianNormalizer T mass F z)-mass*K-Real.log (gaussianNormalizer T mass H z) := by
      field_simp
      <;> ring
    rw [heq,Real.exp_sub,Real.exp_sub,Real.exp_log hZF,Real.exp_log hZH]
  exact hCompare.trans_eq (hIntegral.trans hExp.symm)

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianProbabilityPropagation
