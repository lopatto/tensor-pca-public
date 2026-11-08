-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
public import TensorPCA.NonRSLowerProofs.FiniteCavityFeatureReferenceRestriction
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceComparison

/-! Retained-reference pressure comparison with the same fixed finite perturbation
cutoff and amplitudes at N and N+M.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedReferenceComparison
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison
open FiniteCavityPerturbedFields FiniteCavityPerturbationReference FiniteCavityIdealField
open FiniteCavityReferenceRestriction FiniteCavityReferenceGramBounds FiniteCavityReferenceComparison
open FiniteCavityReferenceLaw FiniteCavityRetainedPrior FiniteCavityRetainedMass
open FiniteCavityFeatureReferenceRestriction FiniteCavityCompensationJointPressure
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def fullPerturbedReferenceFeature (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (z : Model.Vector N×(ℝ×Model.Vector M)) : PerturbedDisorder (N+M) k K :=
  perturbedSliceFeature (N+M) k K mu beta v a (cavityReferenceMap N M z)

def idealPerturbedReferenceFeature (N M k K : ℕ) (mu beta w : ℝ) (a : Fin K→ℝ)
    (z : Model.Vector N×(ℝ×Model.Vector M)) :
    EuclideanSpace ℝ (PerturbedCoordinate N k K⊕IdealCoordinate N M k) :=
  sumJoin (perturbedBulkFeature N M k K mu beta w a z.1,cavityFeature k mu beta z.2.2 z.1)

theorem fullPerturbedReferenceFeature_measurable (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) :
    Measurable (fullPerturbedReferenceFeature N M k K mu beta v a) :=
  (perturbedSliceFeature_continuous (N+M) k K mu beta v a).measurable.comp (cavityReferenceMap_measurable N M)

theorem idealPerturbedReferenceFeature_continuous (N M k K : ℕ) (mu beta w : ℝ) (a : Fin K→ℝ) :
    Continuous (idealPerturbedReferenceFeature N M k K mu beta w a) :=
  sumJoin.continuous.comp (((perturbedBulkFeature_continuous N M k K mu beta w a).comp continuous_fst).prodMk
    ((cavityFeature_joint_continuous N M k mu beta).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))

theorem fullPerturbedReferenceFeature_bound {N M k K : ℕ} (hN : 0<N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) (e delta : ℝ) :
    ∀ᵐ z∂retainedPrior N M e delta,
      ‖fullPerturbedReferenceFeature N M k K mu beta v a z‖≤
        |beta| *Real.sqrt ((N+M : ℕ) : ℝ)+2*|v| :=
  (retained_reference_norm_ae hN e delta).mono
    (fun z hz => perturbedSliceFeature_unit_bound hmu beta v a ha hz)

theorem idealPerturbedReferenceFeature_bound {N M k K : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta w : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2)
    (e delta : ℝ) (hdelta : 0≤delta) :
    ∀ᵐ z∂retainedPrior N M e delta,
      ‖idealPerturbedReferenceFeature N M k K mu beta w a z‖≤
        (Real.sqrt (((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M)))+2*|w|)+
          Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  apply (retainedPrior_support_ae hN e delta).mono
  intro z hz
  exact (joined_norm_le _ _).trans (add_le_add (perturbedBulkFeature_unit_bound hM hmu beta w a ha hz.1)
    (cavityFeature_norm_le k hmu beta (by positivity) z.2.2 hz.2.2.2.2 hz.1))

theorem perturbed_reference_difference_eq (N M k K : ℕ) (mu beta v w : ℝ) (a : Fin K→ℝ)
    (z z' : Model.Vector N×(ℝ×Model.Vector M)) :
    inner ℝ (fullPerturbedReferenceFeature N M k K mu beta v a z)
        (fullPerturbedReferenceFeature N M k K mu beta v a z')-
      inner ℝ (idealPerturbedReferenceFeature N M k K mu beta w a z)
        (idealPerturbedReferenceFeature N M k K mu beta w a z')=
      (inner ℝ (fullReferenceFeature N M k mu beta z) (fullReferenceFeature N M k mu beta z')-
        inner ℝ (idealReferenceFeature N M k mu beta z) (idealReferenceFeature N M k mu beta z'))+
      (inner ℝ (feature (coefficients v a) (cavityReferenceMap N M z))
          (feature (coefficients v a) (cavityReferenceMap N M z'))-
        inner ℝ (feature (coefficients w a) z.1) (feature (coefficients w a) z'.1)) := by
  dsimp only [fullPerturbedReferenceFeature,idealPerturbedReferenceFeature,perturbedSliceFeature,
    perturbedBulkFeature,fullReferenceFeature,idealReferenceFeature]
  simp only [sumJoin_inner]
  ring

theorem perturbed_reference_covariance_bounds {N M k K : ℕ} (hN : 0<N) (hM : 0<M) (hk : 3≤k)
    {mu e delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (he0 : 0≤e) (he1 : e≤1/2) (hdelta : 0≤delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta v w : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) :
    let L := (M : ℝ)*(1+delta)
    let C := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)+
      (4*|v^2-w^2|+16*(K : ℝ)*L*v^2/(N : ℝ))
    (∀ᵐ z∂retainedPrior N M e delta,
      |inner ℝ (fullPerturbedReferenceFeature N M k K mu beta v a z)
          (fullPerturbedReferenceFeature N M k K mu beta v a z)-
        inner ℝ (idealPerturbedReferenceFeature N M k K mu beta w a z)
          (idealPerturbedReferenceFeature N M k K mu beta w a z)|≤C) ∧
    (∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
      |inner ℝ (fullPerturbedReferenceFeature N M k K mu beta v a p.1)
          (fullPerturbedReferenceFeature N M k K mu beta v a p.2)-
        inner ℝ (idealPerturbedReferenceFeature N M k K mu beta w a p.1)
          (idealPerturbedReferenceFeature N M k K mu beta w a p.2)|≤C) := by
  dsimp only
  have hPure := retained_reference_ideal_covariance_bounds hN hM hk hmu he0 he1 hdelta hscale beta
  have hPert := retained_perturbation_covariance_bounds (M := M) hN a ha v w hdelta he0 he1
  constructor
  · filter_upwards [hPure.1,hPert.1] with z hz hp
    rw [perturbed_reference_difference_eq]
    exact (abs_add_le _ _).trans (add_le_add hz hp)
  · filter_upwards [hPure.2,hPert.2] with p hz hp
    rw [perturbed_reference_difference_eq]
    exact (abs_add_le _ _).trans (add_le_add hz hp)

theorem expected_full_perturbed_logPartition_ge_ideal {N M k K : ℕ}
    (hN : 0<N) (hM : 0<M) (hk : 3≤k) {mu e delta : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (he1 : e≤1/2) (hdelta : 0<delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta v w : ℝ)
    (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) :
    let L := (M : ℝ)*(1+delta)
    let C := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)+
      (4*|v^2-w^2|+16*(K : ℝ)*L*v^2/(N : ℝ))
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        (∫g,logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (idealPerturbedReferenceFeature N M k K mu beta w a z)) g
            ∂stdGaussian (EuclideanSpace ℝ (PerturbedCoordinate N k K⊕IdealCoordinate N M k)))-C≤
      ∫g,logPartition (Model.spherePrior (N+M))
        (fun x => innerSL ℝ (perturbedSliceFeature (N+M) k K mu beta v a x)) g
          ∂stdGaussian (PerturbedDisorder (N+M) k K) := by
  dsimp only
  letI := retainedPrior_probability hN hM he hdelta
  have hBounds := perturbed_reference_covariance_bounds hN hM hk hmu he.le he1 hdelta.le hscale beta v w a ha
  have HC := expected_logPartition_abs_sub_le (retainedPrior N M e delta)
    (fullPerturbedReferenceFeature N M k K mu beta v a) (idealPerturbedReferenceFeature N M k K mu beta w a)
    (fullPerturbedReferenceFeature_measurable N M k K mu beta v a)
    (idealPerturbedReferenceFeature_continuous N M k K mu beta w a).measurable
    (by positivity) (by positivity)
    (fullPerturbedReferenceFeature_bound (k := k) hN hmu beta v a ha e delta)
    (idealPerturbedReferenceFeature_bound hN hM hmu beta w a ha e delta hdelta.le) hBounds.1 hBounds.2
  have HR := expected_feature_logPartition_ge_retained hN hM he hdelta
    (perturbedSliceFeature (N+M) k K mu beta v a)
    (perturbedSliceFeature_continuous (N+M) k K mu beta v a).measurable (by positivity)
    (fun x hx => perturbedSliceFeature_unit_bound hmu beta v a ha hx)
  have H := (abs_le.mp HC).1
  dsimp only [fullPerturbedReferenceFeature] at H
  linarith only [HR,H]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedReferenceComparison
