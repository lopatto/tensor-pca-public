-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.MaximumIntegralProofs
public import TensorPCA.CheckedReduction

/-! # Inference bounds from the Bayesian value theorem

The sole proof parameter is convergence of the spherical Bayesian free energy. Finite I-MMSE, secant comparisons, scalar derivatives, posterior bounds,
odd sign validation and envelope control are all discharged by proved modules.
These are conditional reductions, not unconditional principal exports.
-/
@[expose] public section

namespace TensorPCA.BayesianInferenceReductionProofs

universe v

theorem tensorMMSE_of_bayesian_values
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k) :
    Statements.TensorMMSE := by
  intro k hk lam hlam hne
  exact MaximumIntegralProofs.tensorMMSE_tendsto_of_values k hk (hvalues k hk) hlam hne

/-- Both reviewed expected absolute-overlap bounds, for arbitrary independent
estimator randomization in any universe, follow from actual Bayesian values. -/
theorem estimatorOptimality_of_bayesian_values
    (hvalues : ∀ k : ℕ, 3 ≤ k → CheckedReduction.BayesianValueConvergence k) :
    Statements.EstimatorOptimality.{v} := by
  apply CheckedReduction.estimatorOptimality
  · intro k hk lam _ _ A _ nu _ est hest
    exact EstimatorBounds.finiteEstimatorBounds k (by omega) lam A nu est hest
  · intro k hk lam hlam hne
    exact ValidationControlProofs.validationEnvelopeControl k hk hlam hne
      (fun mu hmu hmune ↦ tensorMMSE_of_bayesian_values hvalues k hk mu hmu hmune)


end TensorPCA.BayesianInferenceReductionProofs
