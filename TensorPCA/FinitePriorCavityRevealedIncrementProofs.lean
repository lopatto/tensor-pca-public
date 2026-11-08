-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityConditionalIncrementProofs
public import TensorPCA.FinitePriorCavityRevealProofs

/-! Common-mask revealed priors satisfy the exact conditional cavity
increment. The last-coordinate prior is its Dirac law when revealed
and the original scalar prior when unrevealed. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityRevealedIncrementProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorCavityFieldProofs FinitePriorCavityPartitionProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityRevealProofs FinitePriorCavityLawProofs
open FinitePriorCavityConditionalIncrementProofs FiniteRevealProofs FiniteProductRevealProofs
open TensorCavitySubsetProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] FiniteRevealProofs.posterior_probability

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem revealed_conditional_cavity_increment_ae
    (p : Measure S) [IsProbabilityMeasure p] {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) (A : Finset (Fin (N+1))) :
    ∀ᵐ X ∂configurationPrior p (N+1),
      let qFull := posterior (configurationPrior p (N+1)) A X
      let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
      let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
      Integrable (fun y ↦
        mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
          (freshSignal a N k gamma)-
        mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma))
        (mixtureLaw qOld (backgroundSignal a N k gamma)) ∧
      mixtureFreeEnergy qFull (tensorSignal a (N+1) k gamma)-mixtureFreeEnergy qOld (tensorSignal a N k gamma) =
        ∫ y, mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
          (freshSignal a N k gamma)-
          mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma)
            ∂mixtureLaw qOld (backgroundSignal a N k gamma) := by
  filter_upwards [configurationSplit_reveal_posterior_map_ae p A] with X hSplit
  have : IsProbabilityMeasure (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) := by
    split_ifs <;> infer_instance
  exact conditional_cavity_increment_formula hN hk hgamma
    (posterior (configurationPrior p (N+1)) A X)
    (posterior (configurationPrior p N) (oldPart A) (oldConfiguration X))
    (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) hSplit a

theorem integral_oldConfiguration (p : Measure S) [IsProbabilityMeasure p] (N : ℕ)
    (f : (Fin N → S) → ℝ) :
    (∫ X, f (oldConfiguration X) ∂configurationPrior p (N+1)) =
      ∫ x, f x ∂configurationPrior p N := by
  have H := integral_map (μ := configurationPrior p (N+1)) (measurable_of_finite oldConfiguration).aemeasurable
    (show AEStronglyMeasurable f ((configurationPrior p (N+1)).map oldConfiguration) from
      (measurable_of_finite f).aestronglyMeasurable)
  rw [oldConfiguration_prior_map p N] at H
  exact H.symm

/-- At one fixed common reveal mask, averaging the true planted sample gives
the perturbed old/new free-energy increment. The old mask is exactly oldPart A;
the full reveal prior is never replaced by an unperturbed product prior. -/
theorem revealed_cavity_increment_integral
    (p : Measure S) [IsProbabilityMeasure p] {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {gamma : ℝ} (hgamma : 0 < gamma) (a : S → ℝ) (A : Finset (Fin (N+1))) :
    (∫ X, mixtureFreeEnergy (posterior (configurationPrior p (N+1)) A X)
      (tensorSignal a (N+1) k gamma) ∂configurationPrior p (N+1))-
      (∫ x, mixtureFreeEnergy (posterior (configurationPrior p N) (oldPart A) x)
        (tensorSignal a N k gamma) ∂configurationPrior p N) =
      ∫ X,
        let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
        let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
        ∫ y, mixtureFreeEnergy ((posteriorKernel qOld (backgroundSignal a N k gamma) y).prod pLast)
          (freshSignal a N k gamma)-
          mixtureFreeEnergy (posteriorKernel qOld (backgroundSignal a N k gamma) y) (correctionSignal a N k gamma)
            ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p (N+1) := by
  let fPlus := fun X : Fin (N+1) → S ↦
    mixtureFreeEnergy (posterior (configurationPrior p (N+1)) A X) (tensorSignal a (N+1) k gamma)
  let fOld := fun x : Fin N → S ↦
    mixtureFreeEnergy (posterior (configurationPrior p N) (oldPart A) x) (tensorSignal a N k gamma)
  change (∫ X, fPlus X ∂configurationPrior p (N+1))-(∫ x, fOld x ∂configurationPrior p N) = _
  rw [← integral_oldConfiguration p N fOld,← integral_sub Integrable.of_finite Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [revealed_conditional_cavity_increment_ae p hN hk hgamma a A] with X hX
  exact hX.2

end
end TensorPCA.FinitePriorCavityRevealedIncrementProofs
