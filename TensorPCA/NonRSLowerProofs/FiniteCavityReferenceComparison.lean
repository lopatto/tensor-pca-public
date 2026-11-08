-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceRestriction
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGramBounds

/-! Absolute comparison of the retained full and independent ideal reference fields. The
covariance error is explicit and costs once.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityReferenceComparison
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityReferenceLaw FiniteCavityRetainedMass FiniteCavityRetainedPrior
open FiniteCavityReferenceRestriction FiniteCavityReferenceGramBounds
open GaussianFeatureCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem idealReferenceFeature_retained_bound {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta e delta : ℝ) (hdelta : 0≤delta) :
    ∀ᵐ z∂retainedPrior N M e delta,
      ‖idealReferenceFeature N M k mu beta z‖≤
        Real.sqrt (((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M)))+
          Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) :=
  (retainedPrior_support_ae hN e delta).mono (fun z hz =>
    idealReferenceFeature_norm_le hM k hmu beta (by positivity) hz.1 hz.2.2.2.2)

theorem retained_reference_ideal_covariance_bounds {N M k : ℕ} (hN : 0<N) (hM : 0<M) (hk : 3≤k)
    {mu e delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (he0 : 0≤e) (he1 : e≤1/2) (hdelta : 0≤delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta : ℝ) :
    let L := (M : ℝ)*(1+delta)
    let K := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)
    (∀ᵐ z∂retainedPrior N M e delta,
      |inner ℝ (fullReferenceFeature N M k mu beta z) (fullReferenceFeature N M k mu beta z)-
        inner ℝ (idealReferenceFeature N M k mu beta z) (idealReferenceFeature N M k mu beta z)|≤K) ∧
    (∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
      |inner ℝ (fullReferenceFeature N M k mu beta p.1) (fullReferenceFeature N M k mu beta p.2)-
        inner ℝ (idealReferenceFeature N M k mu beta p.1) (idealReferenceFeature N M k mu beta p.2)|≤K) := by
  dsimp only
  have hs := retainedPrior_support_ae (M := M) hN e delta
  have H (z z' : Model.Vector N×(ℝ×Model.Vector M))
      (hz : ‖z.1‖=1 ∧ 0<z.2.1 ∧ z.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        z.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta)
      (hz' : ‖z'.1‖=1 ∧ 0<z'.2.1 ∧ z'.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
        z'.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta) :=
    reference_idealReferenceFeature_gram_error hN hM k hk hmu beta hdelta he0 he1 hscale hz.1 hz'.1
      hz.2.1.le hz'.2.1.le z.2.2 z'.2.2 hz.2.2.2 hz'.2.2.2 hz.2.2.1 hz'.2.2.1
  constructor
  · exact hs.mono (fun z hz => H z z hz hz)
  · have hS1 : ∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
        ‖p.1.1‖=1 ∧ 0<p.1.2.1 ∧ p.1.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
          p.1.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta :=
      Measure.quasiMeasurePreserving_fst.ae hs
    have hS2 : ∀ᵐ p∂(retainedPrior N M e delta).prod (retainedPrior N M e delta),
        ‖p.2.1‖=1 ∧ 0<p.2.2.1 ∧ p.2.2.1∈FiniteCavityRetainedMass.radiusBox N e ∧
          p.2.2.2∈FiniteCavityShellLinearPartition.gaussianAnnulus M delta :=
      Measure.quasiMeasurePreserving_snd.ae hs
    filter_upwards [hS1,hS2] with p hp hp'
    exact H p.1 p.2 hp hp'

theorem expected_full_logPartition_ge_ideal_reference {N M k : ℕ} (hN : 0<N) (hM : 0<M) (hk : 3≤k)
    {mu e delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (he1 : e≤1/2) (hdelta : 0<delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta : ℝ) :
    let L := (M : ℝ)*(1+delta)
    let K := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)
    Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)+
        (∫g,logPartition (retainedPrior N M e delta)
          (fun z => innerSL ℝ (idealReferenceFeature N M k mu beta z)) g
            ∂stdGaussian (EuclideanSpace ℝ (GroundState.Coordinate N k⊕FiniteCavityIdealField.IdealCoordinate N M k)))-K≤
      ∫g,logPartition (Model.spherePrior (N+M))
        (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
          ∂stdGaussian (GroundState.Disorder (N+M) k) := by
  dsimp only
  letI := retainedPrior_probability hN hM he hdelta
  have hBounds := retained_reference_ideal_covariance_bounds hN hM hk hmu he.le he1 hdelta.le hscale beta
  have HC := expected_logPartition_abs_sub_le (retainedPrior N M e delta)
    (fullReferenceFeature N M k mu beta) (idealReferenceFeature N M k mu beta)
    (fullReferenceFeature_measurable N M k mu beta) (idealReferenceFeature_measurable N M k mu beta)
    (by positivity) (by positivity)
    (fullReferenceFeature_retained_bound (k := k) hN hmu beta e delta)
    (idealReferenceFeature_retained_bound (k := k) hN hM hmu beta e delta hdelta.le)
    hBounds.1 hBounds.2
  have HR := expected_full_logPartition_ge_retained (k := k) hN hM hmu he hdelta beta
  have H := (abs_le.mp HC).1
  linarith only [HR,H]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityReferenceComparison
