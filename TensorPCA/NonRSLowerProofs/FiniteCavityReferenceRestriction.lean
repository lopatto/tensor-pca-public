-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedPrior
public import TensorPCA.NonRSLowerProofs.GaussianFeatureCovarianceComparison
public import TensorPCA.GroundUpperProofs

/-! Restriction of the enlarged spherical partition to the retained reference product.
The two outside logarithmic masses are restored exactly.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceRestriction
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityReferenceLaw FiniteCavityRetainedMass FiniteCavityRetainedPrior
open GaussianFeatureCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fullReferenceFeature (N M k : ℕ) (mu beta : ℝ)
    (z : Model.Vector N×(ℝ×Model.Vector M)) : GroundState.Disorder (N+M) k :=
  beta • GroundState.sliceFeature k mu (cavityReferenceMap N M z)

theorem fullReferenceFeature_measurable (N M k : ℕ) (mu beta : ℝ) :
    Measurable (fullReferenceFeature N M k mu beta) := by
  unfold fullReferenceFeature
  exact (measurable_const : Measurable (fun _ : Model.Vector N×(ℝ×Model.Vector M) => beta)).smul
    ((GroundUpperProofs.continuous_sliceFeature (N+M) k mu).measurable.comp
    (cavityReferenceMap_measurable N M))

theorem thermal_sliceFeature_unit_bound {D k : ℕ} {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta : ℝ) {x : Model.Vector D} (hx : ‖x‖=1) :
    ‖beta • GroundState.sliceFeature k mu x‖≤|beta| *Real.sqrt (D : ℝ) := by
  have hsq := GroundUpperProofs.sliceFeature_norm_sq (k := k) hmu hx
  have hle : ‖GroundState.sliceFeature k mu x‖≤Real.sqrt (D : ℝ) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg D : (0 : ℝ)≤D)
    have hp : 0≤(D : ℝ)*mu^(2*k) :=
      mul_nonneg (Nat.cast_nonneg D) (by simpa only [pow_mul] using pow_nonneg (sq_nonneg mu) k)
    nlinarith only [hsq,hs,hp,norm_nonneg (GroundState.sliceFeature k mu x),Real.sqrt_nonneg (D : ℝ)]
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg beta)

theorem fullReferenceFeature_retained_bound {N M k : ℕ} (hN : 0<N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta e delta : ℝ) :
    ∀ᵐ z∂retainedPrior N M e delta,
      ‖fullReferenceFeature N M k mu beta z‖≤|beta| *Real.sqrt ((N+M : ℕ) : ℝ) :=
  (retained_reference_norm_ae hN e delta).mono (fun _ hz => thermal_sliceFeature_unit_bound hmu beta hz)

theorem full_logPartition_ge_retained {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu e delta : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (hdelta : 0<delta) (beta : ℝ)
    (g : GroundState.Disorder (N+M) k) :
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (fullReferenceFeature N M k mu beta z)) g≤
      logPartition (Model.spherePrior (N+M))
        (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g := by
  let nu := retainedPrior N M e delta
  let L := fun z => innerSL ℝ (fullReferenceFeature N M k mu beta z)
  letI := retainedPrior_probability hN hM he hdelta
  have hL : Measurable L := (innerSL ℝ).continuous.measurable.comp
    (fullReferenceFeature_measurable N M k mu beta)
  have hb : ∀ᵐ z∂nu,‖L z‖≤|beta| *Real.sqrt ((N+M : ℕ) : ℝ) := by
    simpa only [L,innerSL_apply_norm] using fullReferenceFeature_retained_bound (k := k) hN hmu beta e delta
  have hz := moment_one_pos nu L hL hb g
  have hbRef : ∀ᵐ z∂referenceLaw N M,‖L z‖≤|beta| *Real.sqrt ((N+M : ℕ) : ℝ) :=
    (referenceMap_norm_ae hN M).mono (fun z hz => by
      simpa only [L,innerSL_apply_norm,fullReferenceFeature] using thermal_sliceFeature_unit_bound (k := k) hmu beta hz)
  have hI : Integrable (fun z => Real.exp (inner ℝ (fullReferenceFeature N M k mu beta z) g))
      (referenceLaw N M) := by
    have H := weight_integrable (referenceLaw N M) (fun _ => (1 : ℝ)) L measurable_const hL
        (hbRef.mono (fun z hz => (show |(1 : ℝ)|≤1 ∧ ‖L z‖≤|beta| *Real.sqrt ((N+M : ℕ) : ℝ)
          from ⟨by norm_num,hz⟩))) g
    change Integrable (fun z => (1 : ℝ)*Real.exp (L z g)) (referenceLaw N M) at H
    simpa only [one_mul,L,innerSL_apply_apply] using H
  have hMassR := radiusBoxMass_pos hN he
  have hMassA := annulusMass_pos hM hdelta
  have hSub := setIntegral_le_integral (s := retainedRegion N M e delta) hI
    (.of_forall (fun _ => (Real.exp_pos _).le))
  rw [integral_restricted_reference hN hM he hdelta] at hSub
  have hExp : Measurable (fun x : Model.Vector (N+M) =>
      Real.exp (inner ℝ (beta • GroundState.sliceFeature k mu x) g)) :=
    ((GroundUpperProofs.continuous_sliceFeature (N+M) k mu).const_smul beta |>.inner continuous_const).rexp.measurable
  have hMap := (cavityReferenceMap_measurePreserving hN M).hasLaw.integral_comp hExp.aestronglyMeasurable
  change (∫z,Real.exp (inner ℝ (fullReferenceFeature N M k mu beta z) g)∂referenceLaw N M)=
    (∫x,Real.exp (inner ℝ (beta • GroundState.sliceFeature k mu x) g)∂Model.spherePrior (N+M)) at hMap
  rw [hMap] at hSub
  have hz' : 0<(∫z,Real.exp (inner ℝ (fullReferenceFeature N M k mu beta z) g)∂nu) := by
    simpa only [GaussianSpinInterpolation.moment,GaussianSpinInterpolation.weight,L,innerSL_apply_apply,one_mul] using hz
  have H := Real.log_le_log (mul_pos (mul_pos hMassR hMassA) hz') hSub
  rw [Real.log_mul (mul_pos hMassR hMassA).ne' hz'.ne',Real.log_mul hMassR.ne' hMassA.ne'] at H
  simpa only [logPartition,GaussianSpinInterpolation.moment,GaussianSpinInterpolation.weight,
    innerSL_apply_apply,one_mul,nu] using H

theorem expected_full_logPartition_ge_retained {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu e delta : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (hdelta : 0<delta) (beta : ℝ) :
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        (∫g,logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (fullReferenceFeature N M k mu beta z)) g
            ∂stdGaussian (GroundState.Disorder (N+M) k))≤
      ∫g,logPartition (Model.spherePrior (N+M))
        (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
          ∂stdGaussian (GroundState.Disorder (N+M) k) := by
  letI := retainedPrior_probability hN hM he hdelta
  have hR := feature_logPartition_integrable (retainedPrior N M e delta)
    (fullReferenceFeature N M k mu beta) (fullReferenceFeature_measurable N M k mu beta)
    (by positivity) (fullReferenceFeature_retained_bound (k := k) hN hmu beta e delta)
  have hF := feature_logPartition_integrable (Model.spherePrior (N+M))
    (fun x => beta • GroundState.sliceFeature k mu x)
    ((GroundUpperProofs.continuous_sliceFeature (N+M) k mu).const_smul beta).measurable
    (by positivity) ((Geometry.spherePrior_norm_ae (by omega : 0<N+M)).mono
      (fun _ hx => thermal_sliceFeature_unit_bound (k := k) hmu beta hx))
  have H := integral_mono ((integrable_const
    (Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta))).add hR) hF
    (fun g => full_logPartition_ge_retained hN hM hmu he hdelta beta g)
  change (∫g,Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
    logPartition (retainedPrior N M e delta)
      (fun z => innerSL ℝ (fullReferenceFeature N M k mu beta z)) g
      ∂stdGaussian (GroundState.Disorder (N+M) k))≤_ at H
  rw [integral_add (integrable_const _) hR,integral_const,probReal_univ,one_smul] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceRestriction
