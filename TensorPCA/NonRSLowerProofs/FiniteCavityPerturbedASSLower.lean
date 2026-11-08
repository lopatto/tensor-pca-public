-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressureSpherical
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationPressure
public import TensorPCA.NonRSLowerProofs.FinitePerturbationScaleAsymptotics
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceErrorAsymptotics

/-! The finite-cutoff perturbed ASS increment. One cutoff and one amplitude vector are
used at every dimension. Fixed-M increment compatibility is proved directly,
separately from any normalized pressure perturbation cost.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedASSLower
open MeasureTheory ProbabilityTheory Set Filter GaussianSpinInterpolation
open FiniteCavityPerturbedFields FiniteCavityPerturbedReferenceComparison
open FiniteCavityPerturbedIdealPressureSpherical FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteCavityIdealField FiniteCavityRetainedMass
open FiniteCavityReferenceErrorAsymptotics FinitePerturbationScaleAsymptotics
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def expectedLogPerturbedSlicePartition (N k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) : ℝ :=
  ∫g,logPartition (Model.spherePrior N)
    (fun x => innerSL ℝ (perturbedSliceFeature N k K mu beta v a x)) g
      ∂stdGaussian (PerturbedDisorder N k K)

def perturbedCavityFunctional (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) : ℝ :=
  (∫gB,(∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v a gB)
    ∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))∂stdGaussian (PerturbedDisorder N k K))-
  (∫gB,(∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
    (fun x => innerSL ℝ (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)) gT
    ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (PerturbedDisorder N k K))

theorem finite_perturbed_ass_increment_lower {N M k K : ℕ} (hN : 0<N) (hM : 0<M) (hk : 3≤k)
    {mu e delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (he1 : e≤1/2) (hdelta : 0<delta)
    (hscale : 2*((M : ℝ)*(1+delta))≤(N : ℝ)) (beta v w : ℝ)
    (a : Fin K→ℝ) (ha : ∀p,|a p|≤2) :
    let L := (M : ℝ)*(1+delta)
    let C := ((M : ℝ)*delta+4*L*e+14*L^2/(N : ℝ))*beta^2*deriv (Scalar.xiSlice k mu) 1+
      64*L^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)+
      (4*|v^2-w^2|+16*(K : ℝ)*L*v^2/(N : ℝ))
    perturbedCavityFunctional N M k K mu beta w a+
        Real.log (radiusBoxMass N e)+Real.log (annulusMass M delta)-C≤
      expectedLogPerturbedSlicePartition (N+M) k K mu beta v a-
        expectedLogPerturbedSlicePartition N k K mu beta w a := by
  have HR := expected_full_perturbed_logPartition_ge_ideal hN hM hk hmu he he1 hdelta hscale beta v w a ha
  have HI := expected_ideal_retained_ge_bulk_add_spherical_increment (k := k)
    (hN := hN) (hM := hM) (hmu := hmu) (he := he) (hdelta := hdelta) (beta := beta) (v := w) (amp := a)
  have HC := FiniteCavityPerturbedCompensationPressure.expected_full_minus_bulk_le_theta_increment
    (k := k) (K := K) hN hM hmu beta w a
  dsimp only [perturbedCavityFunctional,expectedLogPerturbedSlicePartition]
  dsimp only at HR
  linarith only [HR,HI,HC]

theorem square_rpow_natCast (N : ℕ) (gamma : ℝ) :
    ((N : ℝ)^gamma)^2=(N : ℝ)^(2*gamma) := by
  rw [mul_comm (2 : ℝ) gamma,Real.rpow_mul (Nat.cast_nonneg N)]
  exact (Real.rpow_two _).symm

theorem perturbation_reference_error_tendsto_zero (M K : ℕ) (L : ℝ) {gamma : ℝ}
    (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2) :
    Tendsto (fun N : ℕ =>
      4*|(((N+M : ℕ) : ℝ)^gamma)^2-((N : ℝ)^gamma)^2|+
        16*(K : ℝ)*L*(((N+M : ℕ) : ℝ)^gamma)^2/(N : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hA0 : 0<2*gamma := by linarith only [hgamma0]
  have hA1 : 2*gamma<1 := by linarith only [hgamma1]
  have H := ((rpow_increment_abs_tendsto_zero M hA0 hA1).const_mul 4).add
    ((rpow_shift_div_dimension_tendsto_zero M hA0 hA1).const_mul (16*(K : ℝ)*L))
  convert H using 1
  · funext N
    rw [square_rpow_natCast,square_rpow_natCast]
    ring
  · norm_num

theorem eventually_perturbed_ass_increment_lower (M k K : ℕ) (hM : 0<M) (hk : 3≤k)
    {mu delta gamma : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (hdelta : 0<delta)
    (hgamma0 : 0<gamma) (hgamma1 : gamma<1/2) (beta : ℝ) {eps : ℝ} (heps : 0<eps) :
    ∀ᶠ N : ℕ in atTop,∀a : Fin K→ℝ,(∀p,|a p|≤2) →
      perturbedCavityFunctional N M k K mu beta ((N : ℝ)^gamma) a+Real.log (annulusMass M delta)-
          (M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1-eps≤
        expectedLogPerturbedSlicePartition (N+M) k K mu beta (((N+M : ℕ) : ℝ)^gamma) a-
          expectedLogPerturbedSlicePartition N k K mu beta ((N : ℝ)^gamma) a := by
  have heps2 : 0<eps/2 := by positivity
  obtain ⟨e,he,hCost⟩ := exists_radiusBox_eventually_cost_control M delta
    (beta^2*deriv (Scalar.xiSlice k mu) 1) (beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1) heps2
  have hPert := perturbation_reference_error_tendsto_zero M K ((M : ℝ)*(1+delta)) hgamma0 hgamma1
  filter_upwards [hCost,hPert.eventually (gt_mem_nhds heps2)] with N hN hSmall
  intro a ha
  have H := finite_perturbed_ass_increment_lower hN.1 hM hk hmu he.1 he.2 hdelta hN.2.1 beta
    (((N+M : ℕ) : ℝ)^gamma) ((N : ℝ)^gamma) a ha
  have HC := hN.2.2
  dsimp only at H
  have HC' :
      ((M : ℝ)*delta+4*((M : ℝ)*(1+delta))*e+14*((M : ℝ)*(1+delta))^2/(N : ℝ))*
          beta^2*deriv (Scalar.xiSlice k mu) 1+
        64*((M : ℝ)*(1+delta))^2*beta^2*deriv (deriv (Scalar.xiSlice k mu)) 1/(N : ℝ)-
        Real.log (radiusBoxMass N e)≤
      (M : ℝ)*delta*beta^2*deriv (Scalar.xiSlice k mu) 1+eps/2 := by
    convert HC using 1 <;> ring
  linarith only [H,HC',hSmall]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedASSLower
