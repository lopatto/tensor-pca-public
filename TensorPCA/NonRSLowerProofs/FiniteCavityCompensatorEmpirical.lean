-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorEmpiricalLog
public import TensorPCA.NonRSLowerProofs.FiniteCavityThetaCovariance

/-! Uniform iid logarithmic approximation for the literal thermal compensator.
Its feature already includes sqrt(M/N); no additional cavity or beta scale is used. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorEmpirical
open MeasureTheory ProbabilityTheory Set
open FiniteCavityGaussianCompatibility FiniteCavityThetaCovariance
open FiniteCavityCompensatorGaussianMoments GGFiniteEmpiricalNormalizer
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Actual
variable {N K : ℕ} (hN : 0<N) (hK : 0<K) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
local notation "F" => limitingCompensatorFeature (N := N) M (fun p : Fin k ↦ (p : ℕ)+1)
  (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "C" => (M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1)

include hN hmu

 theorem thetaFeature_norm_sq {x : Model.Vector N} (hx : x∈Model.unitSphere N) : ‖F x‖^2=C := by
  have H := thetaFeature_inner hN M k hmu beta x x
  change ‖x‖=1 at hx
  simpa only [real_inner_self_eq_norm_sq,hx,one_pow,one_mul] using H

 theorem theta_diagonal_nonneg : 0≤C := by
  obtain ⟨x,hx⟩ := Geometry.unitSphere_nonempty hN
  rw [←thetaFeature_norm_sq hN M k hmu beta hx]
  exact sq_nonneg _

include hK

 theorem compensator_empirical_log_integrable_and_bound
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx ∂nu,x∈Model.unitSphere N) :
    Integrable (fun p : GroundState.Disorder N k×(Fin K→Model.Vector N) ↦
      Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
      Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu))
      ((stdGaussian (GroundState.Disorder N k)).prod (Measure.pi (fun _ : Fin K ↦ nu))) ∧
    (∫p : GroundState.Disorder N k×(Fin K→Model.Vector N),
      |Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
        Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)|
      ∂(stdGaussian (GroundState.Disorder N k)).prod (Measure.pi (fun _ : Fin K ↦ nu)))≤
      2*Real.exp (2*C)/Real.sqrt (K : ℝ) := by
  have hCont : Continuous F := by
    unfold limitingCompensatorFeature
    exact (continuous_const : Continuous (fun _ : Model.Vector N ↦ Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
      (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)
  have hFL : ∀ᵐx ∂nu,‖F x‖≤Real.sqrt C := hnu.mono (fun x hx ↦
    Real.le_sqrt_of_sq_le (thetaFeature_norm_sq hN M k hmu beta hx).le)
  have H := expMark_empirical_log_integrable_and_bound hK nu hCont.measurable (Real.sqrt_nonneg C) hFL
  rwa [Real.sq_sqrt (theta_diagonal_nonneg hN M k hmu beta)] at H

 theorem compensator_empirical_log_error_le
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx ∂nu,x∈Model.unitSphere N) :
    (∫p : GroundState.Disorder N k×(Fin K→Model.Vector N),
      |Real.log (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)-
        Real.log (∫x,Real.exp (inner ℝ (F x) p.1) ∂nu)|
      ∂(stdGaussian (GroundState.Disorder N k)).prod (Measure.pi (fun _ : Fin K ↦ nu)))≤
      2*Real.exp (2*C)/Real.sqrt (K : ℝ) :=
  (compensator_empirical_log_integrable_and_bound hN hK M k hmu beta nu hnu).2
end Actual

end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorEmpirical
