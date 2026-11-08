-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianCompatibility

/-! The limiting compensator has the literal thermal theta covariance.
The degree-one coefficient cancels in theta; it remains in the separate
ideal cavity field covariance. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityThetaCovariance
open MeasureTheory ProbabilityTheory Set
open FiniteCavityGaussianCompatibility NonRSSphericalGroundTrialTransportProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem thetaFeature_inner {N : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    inner ℝ (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x)
      (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) y)=
      (M : ℝ)*beta^2*(inner ℝ x y*deriv (Scalar.xiSlice k mu) (inner ℝ x y)-
        Scalar.xiSlice k mu (inner ℝ x y)) := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k mu p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hmu p)
  rw [limitingCompensatorFeature_inner M hN _ _ hc]
  have H := NonRSUpperProofs.SphericalParisiLabeledCovariance.theta_eq_positive_polynomial
    (fun p : Fin k => (p : ℕ)+1) (VariationalProofs.sliceCoefficient k mu)
    (fun _ => by omega) (inner ℝ x y)
  rw [NonRSUpperProofs.SphericalParisiLabeledCovariance.theta,
    source_xi1_eq_deriv_xiSlice,source_xi_eq_xiSlice] at H
  rw [H,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem actual_theta_field_covariance {N : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (x y : Model.Vector N) :
    cov[fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x) g,
      fun g => inner ℝ (limitingCompensatorFeature M (fun p : Fin k => (p : ℕ)+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) y) g;
      stdGaussian (GroundState.Disorder N k)]=
      (M : ℝ)*beta^2*(inner ℝ x y*deriv (Scalar.xiSlice k mu) (inner ℝ x y)-
        Scalar.xiSlice k mu (inner ℝ x y)) := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,covarianceBilin_stdGaussian]
  exact thetaFeature_inner hN M k hmu beta x y

end
end TensorPCA.NonRSLowerProofs.FiniteCavityThetaCovariance
