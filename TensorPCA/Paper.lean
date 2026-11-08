-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.ScalarSelectionProofs
public import TensorPCA.ScalarReduction
public import TensorPCA.FourParameterReductionProofs
public import TensorPCA.BayesianValueProofs
public import TensorPCA.BayesianDetectionReductionProofs
public import TensorPCA.BayesianInferenceReductionProofs

public import TensorPCA.MaximumLimitProofs

public import TensorPCA.RSGroundStateProofs
public import TensorPCA.LandscapeConclusionProofs
public import TensorPCA.NonRSLowerProofs.FiniteCavityPhysicalLower
public import TensorPCA.NonRSLowerProofs.PhysicalPressureLimitReduction

@[expose] public section

namespace TensorPCA.Paper

universe u v

/-- The unnumbered discontinuous-transition consequence of Theorem 1.2
in both the local revision and arXiv v2. -/
theorem discontinuousTransition : Statements.DiscontinuousTransition :=
  ScalarReduction.discontinuous ScalarSelectionProofs.selectionLaws

/-- Infimum-equality formulation of local Remark 5.11 (arXiv v2: Remark 5.10)
for interior overlaps; no unrestricted minimizer attainment is asserted. -/
theorem fourParameterReduction (k : ℕ) (hk : 3 ≤ k) (m : ℝ) (hm : |m| < 1) :
    Scalar.FourParameterReduction k m :=
  FourParameterReductionProofs.fourParameterReduction k hk hm

/-- Theorem 1.1 in both versions: the detection threshold for the spherical
Gaussian tensor experiment. -/
theorem detection : Statements.Detection :=
  BayesianDetectionReductionProofs.detection_of_bayesian_values
    (fun k hk _heven ↦ BayesianValueProofs.bayesianValueConvergence k (by omega))

/-- Local Proposition 5.9 (arXiv v2: Proposition 5.8): the posterior tensor-MMSE limit. -/
theorem tensorMMSE : Statements.TensorMMSE :=
  BayesianInferenceReductionProofs.tensorMMSE_of_bayesian_values
    BayesianValueProofs.bayesianValueConvergence

/-- Local Corollary 5.10 (arXiv v2: Corollary 5.9), in the local formulation:
both absolute-overlap bounds for measurable independently randomized unit-vector
estimators, in any auxiliary universe. -/
theorem estimatorOptimality : Statements.EstimatorOptimality.{v} :=
  BayesianInferenceReductionProofs.estimatorOptimality_of_bayesian_values
    BayesianValueProofs.bayesianValueConvergence

/-- Theorem 1.2 in both versions, value: critical strength and arbitrary physical coupling included. -/
theorem mleValue : Statements.MLEValue.{u} := MaximumLimitProofs.mleValue

/-- Theorem 1.2 in both versions, absolute overlap: zero strength and arbitrary
independent randomization included, with critical strength excluded. -/
theorem mleOverlap : Statements.MLEOverlap.{u,v} := MaximumLimitProofs.mleOverlap

/-- The unnumbered expected-absolute-overlap attainment consequence of
Theorem 1.2 and local Corollary 5.10 (arXiv v2: Corollary 5.9). -/
theorem mleAttainment : Statements.MLEAttainment.{u,v} := MaximumLimitProofs.mleAttainment

/-- The unnumbered introductory testing consequence for a fixed nonempty finite
collection of distinct supercritical strengths. -/
theorem finiteStrengthTesting : Statements.FiniteStrengthTesting := MaximumLimitProofs.finiteStrengthTesting

/-- Local Lemma 5.6 and Remark 5.11 (arXiv v2: Lemma 5.5 and Remark 5.10):
the replica-symmetric formula and equality of variational infima. -/
theorem variationalConclusions : Statements.VariationalConclusions :=
  RSGroundStateProofs.variationalConclusions

/-- Proposition 1.4 in both versions, with the local formulation of strict
local maximality, the globality threshold and zero-overlap globality throughout
the closed subcritical range. -/
theorem landscape : Statements.Landscape := LandscapeConclusionProofs.landscape

/-- Local Lemma 5.5 (arXiv v2: Lemma 5.4): expected and almost-sure constrained
limits, including signed overlaps and arbitrary physical coupling in dimension. -/
theorem constrainedLimit : Statements.ConstrainedLimit.{u} :=
  NonRSLowerProofs.PhysicalPressureLimitReduction.constrainedLimit_of_nonRSFinitePressure
    (fun k hk m _hm hm0 hsmall =>
      NonRSLowerProofs.FiniteCavityPhysicalLower.finite_pressure_lower k hk hm0
        (hsmall.trans_le
          (NonRSLowerProofs.PhysicalPressureLimitReduction.rsCutoff_le_one k hk)))






end TensorPCA.Paper
