-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
public import TensorPCA.GaussianNestedGibbsProofs

/-! Exact continuous-feature Gibbs factorization, including independent
Gaussian product integrability. This applies to the augmented physical bulk. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationFactorization
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation GaussianNestedGibbsProofs
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison FiniteCavityCompensationJointPressure
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

 theorem pointwise_feature_log_factorization (hN : 0<N)
    (a : Model.Vector N→EuclideanSpace ℝ I) (b : Model.Vector N→EuclideanSpace ℝ J)
    (ha : Continuous a) (hb : Continuous b) (ga : EuclideanSpace ℝ I) (gb : EuclideanSpace ℝ J) :
    Real.log (∫x,Real.exp (inner ℝ (a x) ga+inner ℝ (b x) gb) ∂Model.spherePrior N)=
      logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) ga+
      logPartition (gibbsMeasure (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) ga)
        (fun x ↦ innerSL ℝ (b x)) gb := by
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hLa : Measurable (fun x ↦ innerSL ℝ (a x)) := (innerSL ℝ).continuous.measurable.comp ha.measurable
  have hLb : Measurable (fun x ↦ innerSL ℝ (b x)) := (innerSL ℝ).continuous.measurable.comp hb.measurable
  have hba' : ∀ᵐx ∂Model.spherePrior N,‖innerSL ℝ (a x)‖≤Ka :=
    hba.mono (fun x hx ↦ by simpa only [innerSL_apply_norm] using hx)
  have hbb' : ∀ᵐx ∂Model.spherePrior N,‖innerSL ℝ (b x)‖≤Kb :=
    hbb.mono (fun x hx ↦ by simpa only [innerSL_apply_norm] using hx)
  have hZ := moment_one_pos (Model.spherePrior N) _ hLa hba' ga
  have hS := shiftedSpinMoment_one_pos (Model.spherePrior N) _ _ hLb hLa (hbb'.and hba') gb ga
  have hShift : shiftedSpinMoment (Model.spherePrior N) (fun _ ↦ 1)
      (fun x ↦ innerSL ℝ (b x)) (fun x ↦ innerSL ℝ (a x)) gb ga=
      ∫x,Real.exp (inner ℝ (a x) ga+inner ℝ (b x) gb) ∂Model.spherePrior N := by
    unfold shiftedSpinMoment GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun x ↦ by simp only [one_mul,innerSL_apply_apply,Real.exp_add]; ring
  change Real.log (∫x,Real.exp (inner ℝ (a x) ga+inner ℝ (b x) gb) ∂Model.spherePrior N)=
    Real.log (GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ ↦ 1) (fun x ↦ innerSL ℝ (a x)) ga)+
    Real.log (GaussianSpinInterpolation.moment (gibbsMeasure (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) ga)
      (fun _ ↦ 1) (fun x ↦ innerSL ℝ (b x)) gb)
  rw [moment_gibbs_shift_eq (Model.spherePrior N) (fun _ ↦ 1) _ _ hLa hba',
    Real.log_div hS.ne' hZ.ne',hShift]
  ring

 theorem feature_increment_joint_integrable (hN : 0<N)
    (a : Model.Vector N→EuclideanSpace ℝ I) (b : Model.Vector N→EuclideanSpace ℝ J)
    (ha : Continuous a) (hb : Continuous b) :
    Integrable (fun p : EuclideanSpace ℝ I×EuclideanSpace ℝ J ↦
      logPartition (gibbsMeasure (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) p.1)
        (fun x ↦ innerSL ℝ (b x)) p.2)
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hP := (joined_logPartition_product_integrable_and_eq (Model.spherePrior N) a b ha.measurable hb.measurable
    hKa hKb hba hbb).1
  have hB := feature_logPartition_integrable (Model.spherePrior N) a ha.measurable hKa hba
  have hBP : Integrable (fun p : EuclideanSpace ℝ I×EuclideanSpace ℝ J ↦
      logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) p.1)
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p ↦ by
    dsimp only [Pi.sub_apply]
    have H := pointwise_feature_log_factorization hN a b ha hb p.1 p.2
    linarith only [H]

 theorem expected_joined_minus_first_eq_increment (hN : 0<N)
    (a : Model.Vector N→EuclideanSpace ℝ I) (b : Model.Vector N→EuclideanSpace ℝ J)
    (ha : Continuous a) (hb : Continuous b) :
    (∫g,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (sumJoin (a x,b x))) g
      ∂stdGaussian (EuclideanSpace ℝ (I⊕J)))-
    (∫ga,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) ga∂stdGaussian (EuclideanSpace ℝ I))=
    ∫ga,(∫gb,logPartition (gibbsMeasure (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) ga)
      (fun x ↦ innerSL ℝ (b x)) gb∂stdGaussian (EuclideanSpace ℝ J))∂stdGaussian (EuclideanSpace ℝ I) := by
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hPair := joined_logPartition_product_integrable_and_eq (Model.spherePrior N) a b ha.measurable hb.measurable hKa hKb hba hbb
  have hB := feature_logPartition_integrable (Model.spherePrior N) a ha.measurable hKa hba
  have hBP : Integrable (fun p : EuclideanSpace ℝ I×EuclideanSpace ℝ J ↦
      logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) p.1)
      ((stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  have hInc := feature_increment_joint_integrable hN a b ha hb
  rw [hPair.2,←integral_prod _ hPair.1]
  have hFactor :
      (∫p : EuclideanSpace ℝ I×EuclideanSpace ℝ J,
        Real.log (∫x,Real.exp (inner ℝ (a x) p.1+inner ℝ (b x) p.2) ∂Model.spherePrior N)
        ∂(stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J)))=
      (∫p : EuclideanSpace ℝ I×EuclideanSpace ℝ J,
        logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) p.1
        ∂(stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J)))+
      (∫p : EuclideanSpace ℝ I×EuclideanSpace ℝ J,
        logPartition (gibbsMeasure (Model.spherePrior N) (fun x ↦ innerSL ℝ (a x)) p.1)
          (fun x ↦ innerSL ℝ (b x)) p.2
        ∂(stdGaussian (EuclideanSpace ℝ I)).prod (stdGaussian (EuclideanSpace ℝ J))) := by
    rw [←integral_add hBP hInc]
    apply integral_congr_ae
    exact .of_forall (fun p ↦ pointwise_feature_log_factorization hN a b ha hb p.1 p.2)
  rw [hFactor,integral_fun_fst,probReal_univ,one_smul,integral_prod _ hInc]
  ring

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationFactorization
