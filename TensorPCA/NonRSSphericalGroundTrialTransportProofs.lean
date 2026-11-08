-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSSphericalGroundPrimalDualProofs

/-! Exact covariance, derivative and trial-functional identities for the
source positive-degree tensor model specialized to the reviewed slice.
These are finite polynomial identities, without a physical limit premise. -/
@[expose] public section
namespace TensorPCA.NonRSSphericalGroundTrialTransportProofs
open Set
open NonRSUpperProofs
noncomputable section

theorem source_xi_eq_xiSlice (k : ℕ) (m : ℝ) :
    SphericalParisiLabeledCovariance.xi (fun p : Fin k => p.val + 1)
      (VariationalProofs.sliceCoefficient k m) = Scalar.xiSlice k m := by
  funext t
  exact (VariationalProofs.xiSlice_eq_sum k m t).symm

theorem source_xi1_eq_deriv_xiSlice (k : ℕ) (m : ℝ) :
    SphericalParisiLabeledCovariance.xi1 (fun p : Fin k => p.val + 1)
      (VariationalProofs.sliceCoefficient k m) = deriv (Scalar.xiSlice k m) := by
  funext t
  have H := SphericalParisiPositivePolynomialCalculus.xi_hasDerivAt
    (fun p : Fin k => p.val + 1) (VariationalProofs.sliceCoefficient k m) t
  rw [source_xi_eq_xiSlice] at H
  exact H.deriv.symm

theorem source_xi2_eq_secondDeriv_xiSlice (k : ℕ) (m : ℝ) :
    SphericalParisiPositivePolynomialCalculus.xi2 (fun p : Fin k => p.val + 1)
      (VariationalProofs.sliceCoefficient k m) = deriv (deriv (Scalar.xiSlice k m)) := by
  funext t
  have H := SphericalParisiPositivePolynomialCalculus.xi1_hasDerivAt
    (fun p : Fin k => p.val + 1) (VariationalProofs.sliceCoefficient k m) t
  rw [source_xi1_eq_deriv_xiSlice] at H
  exact H.deriv.symm

theorem continuous_secondDeriv_xiSlice (k : ℕ) (m : ℝ) :
    Continuous (deriv (deriv (Scalar.xiSlice k m))) := by
  rw [← source_xi2_eq_secondDeriv_xiSlice k m]
  exact SphericalParisiPositivePolynomialCalculus.xi2_continuous _ _

/-- The actual physical source trial equals the reviewed half-Parisi cost,
including its original degree-one boundary contribution. -/
theorem source_functional_eq_half_parisiFunctional (k : ℕ) (m : ℝ)
    {delta b s : ℝ} (hd : 0 < delta) (hb : 0 ≤ b) (hs : s ∈ Icc (0 : ℝ) 1) :
    LatitudeGroundTrial.functional
      (SphericalParisiLabeledCovariance.xi1 (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m))
      (SphericalParisiPositivePolynomialCalculus.xi2 (fun p : Fin k => p.val + 1)
        (VariationalProofs.sliceCoefficient k m))
      (delta + b * (1 - s)) b s =
      (1 / 2 : ℝ) * Scalar.parisiFunctional (Scalar.xiSlice k m) 0
        (Scalar.fourParameterProfile delta 0 b s) := by
  rw [source_xi1_eq_deriv_xiSlice, source_xi2_eq_secondDeriv_xiSlice]
  exact NonRSSphericalGroundPrimalDualProofs.functional_eq_half_parisiFunctional
    (Scalar.xiSlice k m) (continuous_secondDeriv_xiSlice k m).continuousOn hd hb hs


end
end TensorPCA.NonRSSphericalGroundTrialTransportProofs
