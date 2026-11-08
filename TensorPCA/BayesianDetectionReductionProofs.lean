-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.BayesianDetectionProofs
public import TensorPCA.CoupledTrialProofs

/-! Detection threshold reduced to the Bayesian value limit. The subcritical branch uses the proved physical coupled trial
bound; the supercritical branch uses the planted likelihood test. -/
@[expose] public section
namespace TensorPCA.BayesianDetectionReductionProofs

theorem detection_of_bayesian_values
    (hvalues : ∀ k : ℕ, 6 ≤ k → Even k → CheckedReduction.BayesianValueConvergence k) :
    Statements.Detection := by
  intro k hk heven lam hlam
  constructor
  · exact NullLikelihoodRateProofs.testingDistance_subcritical_of_trialBound
      CoupledTrialProofs.coupledTrialBound k hk heven lam hlam
  · exact BayesianDetectionProofs.testingDistance_supercritical_of_bayesian_values
      k (by omega) (hvalues k hk heven)

end TensorPCA.BayesianDetectionReductionProofs
