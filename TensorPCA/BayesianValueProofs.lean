-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityValueProofs
public import TensorPCA.BayesianValueTransferProofs

/-! Finite Gaussian quantizers supply the product-prior RS limit;
ordered-index and radial transfers give the spherical Bayesian value. -/
@[expose] public section
namespace TensorPCA.BayesianValueProofs
open Filter MeasureTheory ProbabilityTheory Set FinitePriorChannelProofs
open FinitePriorScalarDomainProofs FinitePriorCavityValueProofs
open GaussianFinitePriorApproximationAlphabetProofs GaussianFinitePriorApproximationLimitProofs
open TensorOrbitAggregationProofs GaussianRSNormalizationProofs BayesianValueTransferProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unbounded Gaussian product prior has the actual unordered RS value,
by the proved finite-prior theorem and the uniform quantization bounds. -/
theorem unordered_gaussian_value (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (fun N ↦ unorderedPriorFreeEnergy N k gamma) atTop
      (𝓝 (Statistical.bayesianLimit k gamma)) := by
  apply unordered_bayesian_limit_of_finiteAlphabet_limits k hk hgamma
  intro j
  apply finite_freeEnergy_tendsto (k := k) (liftedGaussianPrior j) (Subtype.val : QuantizedAlphabet j → ℝ)
    (by omega) hgamma.le
  simpa only [scalarSecondMoment] using liftedGaussianPrior_second_moment_le_one j

/-- The reviewed spherical Bayesian value contract, with every finite-prior,
quantization, ordered-index and radial obligation discharged. -/
theorem bayesianValueConvergence (k : ℕ) (hk : 3 ≤ k) : CheckedReduction.BayesianValueConvergence k := by
  apply bayesianValueConvergence_of_productPrior_limit k hk
  intro gamma hgamma
  rw [sSup_gaussianRSPotential_eq_bayesianLimit k hk hgamma]
  have hsucc : Tendsto (fun n : ℕ ↦ n+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ ↦ Nat.le_succ n) tendsto_id
  exact (unordered_gaussian_value k hk hgamma).comp hsucc

end
end TensorPCA.BayesianValueProofs
