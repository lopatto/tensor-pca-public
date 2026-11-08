-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceComparison
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceErrorAsymptotics
public import TensorPCA.NonRSLowerProofs.FiniteCavityIdealRetainedPressureSpherical
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison

/-! The unperturbed finite spherical ASS increment. The independent cavity and theta
banks use the same finite bulk Gibbs law. No thermodynamic limit, GG identity or
structural representation is assumed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityASSLower
open MeasureTheory ProbabilityTheory Set Filter GaussianSpinInterpolation
open FiniteCavityGaussianCompatibility FiniteCavityShellGibbsPartition FiniteCavityIdealField
open FiniteCavityNumeratorMoments FiniteCavityRetainedMass FiniteCavityReferenceComparison
open FiniteCavityReferenceErrorAsymptotics FiniteCavityIdealRetainedPressure
open FiniteCavityIdealRetainedPressureSpherical
open FiniteCavityCompensationThetaComparison
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def expectedLogSlicePartition (N k : ℕ) (mu beta : ℝ) : ℝ :=
  ∫g,logPartition (Model.spherePrior N)
    (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
      ∂stdGaussian (GroundState.Disorder N k)

def finiteCavityFunctional (N M k : ℕ) (mu beta : ℝ) : ℝ :=
  (∫gB,(∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x∂bulkGibbs N M k mu beta gB)
    ∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))∂stdGaussian (GroundState.Disorder N k))-
  (∫gB,(∫gT,logPartition (bulkGibbs N M k mu beta gB)
    (fun x => innerSL ℝ (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)) gT
    ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (GroundState.Disorder N k))

theorem finite_ass_increment_lower {N M k : ℕ} (hN : 0<N) (hM : 0<M) (hk : 3≤k)
    {mu e delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (he1 : e≤1/2) (hdelta : 0<delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta : ℝ) :
    let L := (M : ℝ)*(1+delta)
    let K := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)
    finiteCavityFunctional N M k mu beta+Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)-K≤
      expectedLogSlicePartition (N+M) k mu beta-expectedLogSlicePartition N k mu beta := by
  have HR := expected_full_logPartition_ge_ideal_reference hN hM hk hmu he he1 hdelta hscale beta
  have HI := expected_ideal_retained_ge_bulk_add_spherical_increment (k := k)
    (hN := hN) (hM := hM) (hmu := hmu) (he := he) (hdelta := hdelta) (beta := beta)
  have HC := expected_full_minus_bulk_le_theta_increment (k := k) hN hM hmu beta
  dsimp only [finiteCavityFunctional,expectedLogSlicePartition]
  dsimp only at HR
  linarith only [HR,HI,HC]

theorem eventually_ass_increment_lower (M k : ℕ) (hM : 0<M) (hk : 3≤k)
    {mu delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (hdelta : 0<delta) (beta : ℝ)
    {eps : ℝ} (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop,
      finiteCavityFunctional N M k mu beta+Real.log (annulusMass M delta)-
          (M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1-eps≤
        expectedLogSlicePartition (N+M) k mu beta-expectedLogSlicePartition N k mu beta := by
  obtain ⟨e,he,hCost⟩ := exists_radiusBox_eventually_cost_control M delta
    (beta^2*deriv (Scalar.xiSlice k mu) 1) (beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1) heps
  filter_upwards [hCost] with N hN
  have H := finite_ass_increment_lower hN.1 hM hk hmu he.1 he.2 hdelta hN.2.1 beta
  have HC := hN.2.2
  dsimp only at H
  have HC' :
      ((M : ℝ)*delta+4*((M : ℝ)*(1+delta))*e+14*((M : ℝ)*(1+delta))^2/(N : ℝ))*
          beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*((M : ℝ)*(1+delta))^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)-
        Real.log (radiusBoxMass N e)≤
      (M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1+eps := by
    convert HC using 1 <;> ring
  linarith only [H,HC']

end
end TensorPCA.NonRSLowerProofs.FiniteCavityASSLower
