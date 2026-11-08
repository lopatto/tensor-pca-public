-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityPartitionProofs
public import TensorPCA.FinitePriorCavityNormalizationProofs

/-! Exact physical cavity logarithms and increment integrands. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityLogProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityPartitionProofs FinitePriorCavityNormalizationProofs
open GaussianPriorTransferProofs GaussianPosteriorProofs GaussianSideChannelProofs TensorOrbitCountProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

def correctionFactor (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w0 w1 : EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  mixtureLikelihood (backgroundPosterior p a N k gamma X w0) (correctionSignal a N k gamma)
    (correctionSignal a N k gamma X+w1)

theorem correctionFactor_pos (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w0 w1 : EuclideanSpace ℝ (KSubset N k)) : 0 < correctionFactor p a N k gamma X w0 w1 := by
  letI := backgroundPosterior_probability p a N k gamma X w0
  exact mixtureLikelihood_pos _ _ (measurable_of_finite _) _

theorem mixtureLikelihood_background_correction (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma)
    (a : S → ℝ) (X : Fin N → S) (w0 w1 : EuclideanSpace ℝ (KSubset N k)) :
    mixtureLikelihood (configurationPrior p N) (tensorSignal a N k gamma)
      (tensorSignal a N k gamma X+gaussianMix
        (TensorOrbitAggregationProofs.aggregateCoefficient (N+1) k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma)
        (correctionCoefficient N k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma) (w0,w1)) =
      backgroundPartition p a N k gamma X w0*correctionFactor p a N k gamma X w0 w1 := by
  rw [show backgroundPartition p a N k gamma X w0*correctionFactor p a N k gamma X w0 w1 =
    combinedLikelihood (configurationPrior p N) (correctionSignal a N k gamma) (backgroundSignal a N k gamma)
      (correctionSignal a N k gamma X+w1) (backgroundSignal a N k gamma X+w0) by
        exact (combinedLikelihood_factor _ _ _ (measurable_of_finite _) _ _).symm]
  unfold mixtureLikelihood combinedLikelihood
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change Real.exp (plantedHamiltonian a N k gamma X x (gaussianMix
      (TensorOrbitAggregationProofs.aggregateCoefficient (N+1) k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma)
      (correctionCoefficient N k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma) (w0,w1))) =
    Real.exp (correctionHamiltonian a N k gamma X x w1)*Real.exp (backgroundHamiltonian a N k gamma X x w0)
  rw [← plantedHamiltonian_background_correction hN hk hgamma a X x w0 w1,Real.exp_add,mul_comm]

theorem log_mixtureLikelihood_cavity (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (X : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    Real.log (mixtureLikelihood (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
      (tensorSignal a (N+1) k gamma X+w)) =
      Real.log (backgroundPartition p a N k gamma (oldConfiguration X) (disorderSplit hk w).1)+
        Real.log (∫ x, cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x
          ∂backgroundPosterior p a N k gamma (oldConfiguration X) (disorderSplit hk w).1) := by
  have hfactor := mixtureLikelihood_cavity_factor p hk a gamma X w
  have hfull := mixtureLikelihood_pos (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
    (measurable_tensorSignal a (N+1) k gamma) (tensorSignal a (N+1) k gamma X+w)
  rw [hfactor] at hfull
  have hbase := backgroundPartition_pos p a N k gamma (oldConfiguration X) (disorderSplit hk w).1
  have hcavity := (mul_pos_iff_of_pos_left hbase).mp hfull
  rw [hfactor,Real.log_mul hbase.ne' hcavity.ne']

theorem log_mixtureLikelihood_background_correction (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma)
    (a : S → ℝ) (X : Fin N → S) (w0 w1 : EuclideanSpace ℝ (KSubset N k)) :
    Real.log (mixtureLikelihood (configurationPrior p N) (tensorSignal a N k gamma)
      (tensorSignal a N k gamma X+gaussianMix
        (TensorOrbitAggregationProofs.aggregateCoefficient (N+1) k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma)
        (correctionCoefficient N k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma) (w0,w1))) =
      Real.log (backgroundPartition p a N k gamma X w0)+Real.log (correctionFactor p a N k gamma X w0 w1) := by
  rw [mixtureLikelihood_background_correction p hN hk hgamma,
    Real.log_mul (backgroundPartition_pos p a N k gamma X w0).ne' (correctionFactor_pos p a N k gamma X w0 w1).ne']

/-- Exact actual increment integrand: both logarithms use the same N+1
background and its genuine posterior; its normalizer cancels. -/
theorem cavity_log_increment (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {gamma : ℝ} (hgamma : 0 < gamma)
    (a : S → ℝ) (X : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k))
    (w1 : EuclideanSpace ℝ (KSubset N k)) :
    Real.log (mixtureLikelihood (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
      (tensorSignal a (N+1) k gamma X+w))-
    Real.log (mixtureLikelihood (configurationPrior p N) (tensorSignal a N k gamma)
      (tensorSignal a N k gamma (oldConfiguration X)+gaussianMix
        (TensorOrbitAggregationProofs.aggregateCoefficient (N+1) k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma)
        (correctionCoefficient N k gamma/TensorOrbitAggregationProofs.aggregateCoefficient N k gamma) ((disorderSplit hk w).1,w1))) =
    Real.log (∫ x, cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x
      ∂backgroundPosterior p a N k gamma (oldConfiguration X) (disorderSplit hk w).1)-
        Real.log (correctionFactor p a N k gamma (oldConfiguration X) (disorderSplit hk w).1 w1) := by
  rw [log_mixtureLikelihood_cavity p hk,log_mixtureLikelihood_background_correction p hN hk hgamma]
  ring

end
end TensorPCA.FinitePriorCavityLogProofs
