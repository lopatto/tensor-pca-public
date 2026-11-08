-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceRestriction

/-! The same retained-reference restriction for a finite Gaussian feature, including an
independent finite perturbation bank.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityFeatureReferenceRestriction
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityReferenceLaw FiniteCavityRetainedMass FiniteCavityRetainedPrior
open GaussianFeatureCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem feature_logPartition_ge_retained {N M : ℕ} (hN : 0<N) (hM : 0<M) {e delta : ℝ}
    (he : 0<e) (hdelta : 0<delta)
    (f : Model.Vector (N+M)→EuclideanSpace ℝ I) (hf : Measurable f) {B : ℝ}
    (hb : ∀x,‖x‖=1→‖f x‖≤B) (g : EuclideanSpace ℝ I) :
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (f (cavityReferenceMap N M z))) g≤
      logPartition (Model.spherePrior (N+M)) (fun x => innerSL ℝ (f x)) g := by
  let nu := retainedPrior N M e delta
  let L := fun z => innerSL ℝ (f (cavityReferenceMap N M z))
  letI := retainedPrior_probability hN hM he hdelta
  have hL : Measurable L := (innerSL ℝ).continuous.measurable.comp
    (hf.comp (cavityReferenceMap_measurable N M))
  have hbRet : ∀ᵐ z∂nu,‖L z‖≤B :=
    (retained_reference_norm_ae hN e delta).mono (fun z hz => by
      simpa only [L,innerSL_apply_norm] using hb (cavityReferenceMap N M z) hz)
  have hz := moment_one_pos nu L hL hbRet g
  have hbRef : ∀ᵐ z∂referenceLaw N M,‖L z‖≤B :=
    (referenceMap_norm_ae hN M).mono (fun z hz => by
      simpa only [L,innerSL_apply_norm] using hb (cavityReferenceMap N M z) hz)
  have hI : Integrable (fun z => Real.exp (inner ℝ (f (cavityReferenceMap N M z)) g))
      (referenceLaw N M) := by
    have H := weight_integrable (referenceLaw N M) (fun _ => (1 : ℝ)) L measurable_const hL
      (hbRef.mono (fun z hz => (show |(1 : ℝ)|≤1 ∧ ‖L z‖≤B from ⟨by norm_num,hz⟩))) g
    change Integrable (fun z => (1 : ℝ)*Real.exp (L z g)) (referenceLaw N M) at H
    simpa only [one_mul,L,innerSL_apply_apply] using H
  have hR := radiusBoxMass_pos hN he
  have hA := annulusMass_pos hM hdelta
  have hSub := setIntegral_le_integral (s := retainedRegion N M e delta) hI
    (.of_forall (fun _ => (Real.exp_pos _).le))
  rw [integral_restricted_reference hN hM he hdelta] at hSub
  have hExp : Measurable (fun x => Real.exp (inner ℝ (f x) g)) := by
    have H := ((ContinuousLinearMap.apply ℝ ℝ g).continuous.measurable.comp
      ((innerSL ℝ).continuous.measurable.comp hf)).exp
    change Measurable (fun x => Real.exp ((innerSL ℝ (f x)) g)) at H
    simpa only [innerSL_apply_apply] using H
  have hMap := (cavityReferenceMap_measurePreserving hN M).hasLaw.integral_comp hExp.aestronglyMeasurable
  change (∫z,Real.exp (inner ℝ (f (cavityReferenceMap N M z)) g)∂referenceLaw N M)=
    (∫x,Real.exp (inner ℝ (f x) g)∂Model.spherePrior (N+M)) at hMap
  rw [hMap] at hSub
  have hz' : 0<(∫z,Real.exp (inner ℝ (f (cavityReferenceMap N M z)) g)∂nu) := by
    simpa only [GaussianSpinInterpolation.moment,GaussianSpinInterpolation.weight,L,innerSL_apply_apply,one_mul] using hz
  have H := Real.log_le_log (mul_pos (mul_pos hR hA) hz') hSub
  rw [Real.log_mul (mul_pos hR hA).ne' hz'.ne',Real.log_mul hR.ne' hA.ne'] at H
  simpa only [logPartition,GaussianSpinInterpolation.moment,GaussianSpinInterpolation.weight,
    innerSL_apply_apply,one_mul,nu] using H

theorem expected_feature_logPartition_ge_retained {N M : ℕ} (hN : 0<N) (hM : 0<M) {e delta : ℝ}
    (he : 0<e) (hdelta : 0<delta)
    (f : Model.Vector (N+M)→EuclideanSpace ℝ I) (hf : Measurable f) {B : ℝ}
    (hB : 0≤B) (hb : ∀x,‖x‖=1→‖f x‖≤B) :
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        (∫g,logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (f (cavityReferenceMap N M z))) g∂stdGaussian (EuclideanSpace ℝ I))≤
      ∫g,logPartition (Model.spherePrior (N+M)) (fun x => innerSL ℝ (f x)) g
        ∂stdGaussian (EuclideanSpace ℝ I) := by
  letI := retainedPrior_probability hN hM he hdelta
  have hR := feature_logPartition_integrable (retainedPrior N M e delta)
    (fun z => f (cavityReferenceMap N M z)) (hf.comp (cavityReferenceMap_measurable N M)) hB
    ((retained_reference_norm_ae hN e delta).mono (fun z hz => hb _ hz))
  have hF := feature_logPartition_integrable (Model.spherePrior (N+M)) f hf hB
    ((Geometry.spherePrior_norm_ae (by omega : 0<N+M)).mono (fun x hx => hb _ hx))
  have H := integral_mono ((integrable_const
    (Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta))).add hR) hF
    (fun g => feature_logPartition_ge_retained hN hM he hdelta f hf hb g)
  change (∫g,Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
    logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (f (cavityReferenceMap N M z))) g
    ∂stdGaussian (EuclideanSpace ℝ I))≤_ at H
  rw [integral_add (integrable_const _) hR,integral_const,probReal_univ,one_smul] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityFeatureReferenceRestriction
