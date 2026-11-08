-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumBranchLowerProofs
public import TensorPCA.MaximumFromPureUpperProofs
public import TensorPCA.BayesianValueProofs

/-! local Lemma 5.4 and reductions parameterized by the sharp pure null upper bound. Conditional MLE results are not final exports. -/
@[expose] public section
namespace TensorPCA.MaximumConsequencesProofs
open Filter
universe u v

theorem lemma54 (k : ℕ) (hk : 3 ≤ k) {lam : ℝ} (hlam : Scalar.lambdaS k < lam) :
    Real.sqrt (k : ℝ)*(1+lam^2*(Scalar.qS k lam)^(k-1)) /
      Real.sqrt (1+lam^2*(k : ℝ)*(Scalar.qS k lam)^(k-1)) ≤
      liminf (fun n : ℕ ↦ Model.expectedMaximum (n+1) k lam) atTop :=
  MaximumBranchLowerProofs.lemma54_of_values k hk
    (BayesianValueProofs.bayesianValueConvergence k hk) hlam

theorem meanMaximumLimit_of_pure_upper
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    CheckedReduction.MeanMaximumLimit :=
  MaximumFromPureUpperProofs.meanMaximumLimit_of_pure_upper
    BayesianValueProofs.bayesianValueConvergence hUpper

theorem mleValue_of_pure_upper
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    Statements.MLEValue.{u} :=
  MaximumFromPureUpperProofs.mleValue_of_pure_upper
    BayesianValueProofs.bayesianValueConvergence hUpper

theorem mleOverlap_of_pure_upper
    (hUpper : ∀ k : ℕ, 3 ≤ k → ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, Model.expectedMaximum (n+1) k 0 ≤ Scalar.gs k+eps) :
    Statements.MLEOverlap.{u,v} :=
  MaximumFromPureUpperProofs.mleOverlap_of_pure_upper
    BayesianValueProofs.bayesianValueConvergence hUpper

end TensorPCA.MaximumConsequencesProofs
