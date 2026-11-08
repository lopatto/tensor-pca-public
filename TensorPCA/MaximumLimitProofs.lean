-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.MaximumConsequencesProofs
public import TensorPCA.PureMaximumUpperProofs
public import TensorPCA.MaximumMSEProofs
public import TensorPCA.ClassifierProofs
public import TensorPCA.EstimatorTransportProofs

/-! Maximum and estimator consequences. The Bayesian values and
sharp pure upper bound are proved prerequisites, with no intermediate proof
parameter left in these declarations. -/
@[expose] public section
namespace TensorPCA.MaximumLimitProofs
open MeasureTheory Filter
open scoped Topology
universe u v

theorem meanMaximumLimit : CheckedReduction.MeanMaximumLimit :=
  MaximumConsequencesProofs.meanMaximumLimit_of_pure_upper
    PureMaximumUpperProofs.eventually_expectedMaximum_zero_upper

theorem mleValue : Statements.MLEValue.{u} :=
  MaximumConsequencesProofs.mleValue_of_pure_upper
    PureMaximumUpperProofs.eventually_expectedMaximum_zero_upper

theorem mleOverlap : Statements.MLEOverlap.{u,v} :=
  MaximumConsequencesProofs.mleOverlap_of_pure_upper
    PureMaximumUpperProofs.eventually_expectedMaximum_zero_upper

theorem mleAttainment : Statements.MLEAttainment.{u,v} :=
  CheckedReduction.mleAttainment mleOverlap EstimatorTransportProofs.overlapIntegralTransport

theorem finiteStrengthTesting : Statements.FiniteStrengthTesting := by
  apply CheckedReduction.finiteStrengthTesting ClassifierProofs.finite_classifier
  intro k hk lam hsuper
  apply MaximumMSEProofs.maximumMeanSquare_tendsto
  exact meanMaximumLimit k hk lam ((ScalarStaticRatioProofs.lambdaC_pos k hk).trans hsuper).le

end TensorPCA.MaximumLimitProofs
