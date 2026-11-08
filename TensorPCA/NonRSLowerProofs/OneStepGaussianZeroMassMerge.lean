-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianStepLipschitz
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint

/-! Consecutive zero-mass steps merge by the law of the sum of two independent standard
Gaussian vectors. All Fubini hypotheses are derived from the terminal Lipschitz
bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianZeroMassMerge
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianStepLipschitz OneStepGaussianTiltJoint
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem gaussianLogStep_zero_merge {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    (a b : ℝ) (x : E) :
    gaussianLogStep (a • T) 0 (gaussianLogStep (b • T) 0 F) x=
      gaussianLogStep (Real.sqrt (a^2+b^2) • T) 0 F x := by
  let mu := stdGaussian (Model.Vector N)
  let S := fun p : Model.Vector N×Model.Vector N ↦ a • p.1+b • p.2
  let R := fun g : Model.Vector N ↦ Real.sqrt (a^2+b^2) • g
  let f := fun z : Model.Vector N ↦ F (x+T z)
  have hf : Measurable f := hF.continuous.measurable.comp (by fun_prop)
  have hS : Measurable S := by fun_prop
  have hR : Measurable R := by fun_prop
  have hlaw : (mu.prod mu).map S=mu.map R := by
    simpa only [mu,S,R,zero_add] using sum_gaussian_law (0 : Model.Vector N) a b
  have hIR : Integrable (fun g ↦ f (R g)) mu := by
    simpa only [f,R,mu,ContinuousLinearMap.smul_apply,map_smul] using
      shifted_integrable hF (Real.sqrt (a^2+b^2) • T) x
  have hIP : Integrable (fun p ↦ f (S p)) (mu.prod mu) := by
    apply (integrable_map_measure hf.aestronglyMeasurable hS.aemeasurable).mp
    rw [hlaw]
    exact (integrable_map_measure hf.aestronglyMeasurable hR.aemeasurable).mpr hIR
  have heq : (∫ p, f (S p) ∂mu.prod mu)=∫ g, f (R g) ∂mu := by
    rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable,hlaw,
      integral_map hR.aemeasurable hf.aestronglyMeasurable]
  have H := (integral_prod (fun p ↦ f (S p)) hIP).symm.trans heq
  simpa only [gaussianLogStep,↓reduceIte,f,S,R,mu,ContinuousLinearMap.smul_apply,
    map_add,map_smul,add_assoc] using H

theorem gaussianLogStep_zero_merge_variances {N : ℕ} {L : ℝ≥0} {F : E → ℝ}
    (hF : LipschitzWith L F) (T : Model.Vector N →L[ℝ] E)
    {v w : ℝ} (hv : 0≤v) (hw : 0≤w) (x : E) :
    gaussianLogStep (Real.sqrt v • T) 0 (gaussianLogStep (Real.sqrt w • T) 0 F) x=
      gaussianLogStep (Real.sqrt (v+w) • T) 0 F x := by
  simpa only [Real.sq_sqrt hv,Real.sq_sqrt hw] using
    gaussianLogStep_zero_merge hF T (Real.sqrt v) (Real.sqrt w) x

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianZeroMassMerge
