-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityRevealedIncrementProofs
public import TensorPCA.FinitePriorCavityPinningProofs
public import TensorPCA.FinitePriorCavityScalarEndpointProofs
public import TensorPCA.FiniteRevealFreeEnergyProofs

/-! Exact common-rate perturbed cavity increments and the last-coordinate reveal cost. All averages use the old-mask marginal and planted product
law; the common-rate identity does not identify two different reveal rates. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityAveragingProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorCavityFieldProofs FinitePriorCavityPartitionProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityConditionalIncrementProofs
open FinitePriorCavityRevealedIncrementProofs FinitePriorCavityPinningProofs FinitePriorCavityScalarEndpointProofs
open FiniteRevealProofs FiniteRevealAveragingProofs FiniteRevealFreeEnergyProofs TensorCavitySubsetProofs
open RevealPolynomialProofs BayesianPinningProofs BayesianPinningVarianceProofs
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] FiniteRevealProofs.posterior_probability

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

/-- Actual unnormalized tensor free energy at an arbitrary uniform reveal rate. -/
def revealedFreeEnergyAtRate (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (N k : ℕ) (gamma delta : ℝ) : ℝ :=
  uniformAverage Finset.univ delta (fun mask ↦ ∫ x,
    mixtureFreeEnergy (posterior (configurationPrior p N) mask x)
      (tensorSignal a N k gamma) ∂configurationPrior p N)

/-- The finite conditional increment at one full reveal mask. -/
def conditionalCavityIncrement (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (N k : ℕ) (gamma : ℝ) (A : Finset (Fin (N+1))) : ℝ :=
  ∫ X,
    let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
    let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
    ∫ y, mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
      (freshSignal a N k gamma)-
      mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p (N+1)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem revealedFreeEnergyAtRate_eq_raw_add_cost
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    {delta : ℝ} (hd : 0 < delta) :
    revealedFreeEnergyAtRate p a N k gamma delta =
      mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma)+
        uniformAverage Finset.univ delta
          (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma)) := by
  have H := uniformAverage_const (Finset.univ : Finset (Fin N)) hd
    (mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma))
  rw [uniformAverage_eq_sum Finset.univ hd] at H
  unfold revealedFreeEnergyAtRate
  rw [uniformAverage_eq_sum Finset.univ hd,uniformAverage_eq_sum Finset.univ hd]
  unfold revealFreeEnergyCost
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,H]
  ring

theorem bernoulli_cavity_increment_identity
    (p : Measure S) [IsProbabilityMeasure p] {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) (theta : ℝ) :
    average Finset.univ (fun A ↦ ∫ X, mixtureFreeEnergy (posterior (configurationPrior p (N+1)) A X)
        (tensorSignal a (N+1) k gamma) ∂configurationPrior p (N+1)) theta-
      average Finset.univ (fun A ↦ ∫ x, mixtureFreeEnergy (posterior (configurationPrior p N) A x)
        (tensorSignal a N k gamma) ∂configurationPrior p N) theta =
      average Finset.univ (conditionalCavityIncrement p a N k gamma) theta := by
  rw [← average_oldPart N (fun A ↦ ∫ x, mixtureFreeEnergy (posterior (configurationPrior p N) A x)
    (tensorSignal a N k gamma) ∂configurationPrior p N) theta,← BayesianPinningVarianceProofs.average_sub]
  congr 1
  funext A
  exact revealed_cavity_increment_integral p hN hk hgamma a A

theorem uniform_cavity_increment_identity
    (p : Measure S) [IsProbabilityMeasure p] {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) {delta : ℝ} (hd : 0 < delta) :
    revealedFreeEnergyAtRate p a (N+1) k gamma delta-revealedFreeEnergyAtRate p a N k gamma delta =
      uniformAverage Finset.univ delta (conditionalCavityIncrement p a N k gamma) := by
  unfold revealedFreeEnergyAtRate uniformAverage
  rw [← integral_sub
    ((memLp_uniformInterval (average_continuous _ _) hd 1).integrable le_rfl)
    ((memLp_uniformInterval (average_continuous _ _) hd 1).integrable le_rfl)]
  apply integral_congr_ae
  exact .of_forall fun theta ↦ bernoulli_cavity_increment_identity p hN hk hgamma a theta

/-- The last reveal changes the scalar RS potential only by the actual scalar
channel reveal cost. The deterministic RS penalty cancels exactly. -/
theorem lastReveal_scalarPotential_cost_bounds
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (k : ℕ) (gamma q : ℝ)
    {theta : ℝ} (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ (1-theta)*scalarPotential p a k gamma q+
      theta*(∫ s, scalarPotential (Measure.dirac s) a k gamma q ∂p)-scalarPotential p a k gamma q ∧
    (1-theta)*scalarPotential p a k gamma q+
      theta*(∫ s, scalarPotential (Measure.dirac s) a k gamma q ∂p)-scalarPotential p a k gamma q ≤
        theta*Real.log (Fintype.card S) := by
  have H := lastReveal_scalar_freeEnergy_cost_bounds p a ((k : ℝ)*gamma*q^(k-1)) ht0 ht1
  unfold scalarPotential
  rw [integral_sub Integrable.of_finite (integrable_const _),integral_const,probReal_univ,one_smul]
  constructor <;> linarith [H.1,H.2]

end
end TensorPCA.FinitePriorCavityAveragingProofs
