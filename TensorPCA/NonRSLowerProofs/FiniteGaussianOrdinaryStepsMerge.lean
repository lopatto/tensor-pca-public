-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsExponentialGrowth
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint

/-! Merging ordinary Gaussian steps for exponential-growth terminals. The older
Lipschitz-only merge cannot be applied directly to numerator marks; their true
integrability here is proved from the exponential envelope.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsMerge
open MeasureTheory ProbabilityTheory
open FiniteGaussianOrdinaryStepsExponentialGrowth OneStepGaussianTiltJoint
open OneStepGaussianStepLipschitz FiniteGaussianLogStepsCompression
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

theorem ordinary_pair_merge {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖))
    (T : Model.Vector M→L[ℝ]Model.Vector M) (a b : ℝ) (z : Model.Vector M) :
    gaussianLogStep (a • T) 0 (gaussianLogStep (b • T) 0 F) z=
      gaussianLogStep (Real.sqrt (a^2+b^2) • T) 0 F z := by
  let mu := stdGaussian (Model.Vector M)
  let S := fun p : Model.Vector M×Model.Vector M => a • p.1+b • p.2
  let R := fun g : Model.Vector M => Real.sqrt (a^2+b^2) • g
  let f := fun y : Model.Vector M => F (z+T y)
  have hf : Measurable f := hF.comp (measurable_const.add T.continuous.measurable)
  have hS : Measurable S := by fun_prop
  have hR : Measurable R := by fun_prop
  have hlaw : (mu.prod mu).map S=mu.map R := by
    simpa only [mu,S,R,zero_add] using sum_gaussian_law (0 : Model.Vector M) a b
  have hIR : Integrable (fun g => f (R g)) mu := by
    simpa only [f,R,mu,ContinuousLinearMap.smul_apply,map_smul] using
      shifted_integrable hF hC hK hb (Real.sqrt (a^2+b^2) • T) z
  have hIP : Integrable (fun p => f (S p)) (mu.prod mu) := by
    apply (integrable_map_measure hf.aestronglyMeasurable hS.aemeasurable).mp
    rw [hlaw]
    exact (integrable_map_measure hf.aestronglyMeasurable hR.aemeasurable).mpr hIR
  have heq : (∫p,f (S p) ∂mu.prod mu)=∫g,f (R g) ∂mu := by
    rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable,hlaw,integral_map hR.aemeasurable hf.aestronglyMeasurable]
  have H := (integral_prod (fun p => f (S p)) hIP).symm.trans heq
  simpa only [gaussianLogStep,↓reduceIte,f,S,R,mu,ContinuousLinearMap.smul_apply,map_add,map_smul,add_assoc] using H

theorem ordinary_steps_merge {F : Model.Vector M→ℝ} (hF : Measurable F) {C K : ℝ}
    (hC : 0≤C) (hK : 0≤K) (hb : ∀z,|F z|≤C*Real.exp (K*‖z‖))
    (T : Model.Vector M→L[ℝ]Model.Vector M) (variances : List ℝ)
    (hv : ∀v∈variances,0≤v) (z : Model.Vector M) :
    gaussianLogSteps (variances.map (fun v => (0,Real.sqrt v • T))) F z=
      gaussianLogStep (Real.sqrt variances.sum • T) 0 F z := by
  induction variances generalizing z with
  | nil => simp [gaussianLogSteps,gaussianLogStep]
  | cons v variances ih =>
    have hv0 := hv v (by simp)
    have hTail : ∀w∈variances,0≤w := fun w h => hv w (by simp [h])
    have hSum : 0≤variances.sum := List.sum_nonneg hTail
    have HE : gaussianLogSteps (variances.map (fun v => (0,Real.sqrt v • T))) F=
        gaussianLogStep (Real.sqrt variances.sum • T) 0 F := funext (ih hTail)
    simp only [List.map_cons,gaussianLogSteps,List.foldr_cons]
    change gaussianLogStep (Real.sqrt v • T) 0
      (gaussianLogSteps (variances.map (fun v => (0,Real.sqrt v • T))) F) z=_
    rw [HE]
    simpa only [Real.sq_sqrt hv0,Real.sq_sqrt hSum,List.sum_cons] using
      ordinary_pair_merge hF hC hK hb T (Real.sqrt v) (Real.sqrt variances.sum) z

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsMerge
