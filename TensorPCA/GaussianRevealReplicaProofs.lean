-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealTransportProofs

/-! # Exact replica response transport for the revealed Gaussian posterior -/
@[expose] public section

namespace TensorPCA.GaussianRevealReplicaProofs

open MeasureTheory ProbabilityTheory GaussianSideChannelProofs GaussianReplicaTransportProofs
open GaussianFiniteRevealProofs GaussianRevealTransportProofs FiniteEntropyProofs

attribute [local instance] condition_probability

variable {Omega E D U : Type*} [Fintype Omega] [MeasurableSpace Omega] [MeasurableSingletonClass Omega]
  [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

omit [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U] in
theorem measurable_replicaIntegral {Y : Type*} [MeasurableSpace Y]
    (kappa : Kernel Y Omega) [IsMarkovKernel kappa] (G : Omega × Omega → ℝ) :
    Measurable (fun y ↦ ∫ z, G z ∂(kappa y).prod (kappa y)) := by
  have h := (measurable_of_finite G).stronglyMeasurable.integral_kernel (κ := kappa ×ₖ kappa)
  simpa only [Kernel.prod_apply] using h.measurable

omit [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U] [MeasurableSingletonClass Omega] in
theorem replicaIntegral_abs_le (q : Measure Omega) [IsProbabilityMeasure q]
    (G : Omega × Omega → ℝ) : |∫ z, G z ∂q.prod q| ≤ ∑ z, |G z| := by
  rw [← Real.norm_eq_abs]
  have hb : ∀ᵐ z ∂q.prod q, ‖G z‖ ≤ ∑ z, |G z| := .of_forall fun z ↦ by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun z _ ↦ abs_nonneg (G z)) (Finset.mem_univ z)
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

/-- Finite Gaussian reveal commutation and output-law transport give precisely
the replica average of the revealed original full posterior. -/
theorem integral_reveal_replica_transport (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (G : Omega × Omega → ℝ) :
    (∫ x, ∫ y, ∫ z, G z
        ∂(combinedPosteriorKernel (condition mu r (r x)) A B y).prod
          (combinedPosteriorKernel (condition mu r (r x)) A B y)
      ∂pairObservationLaw (condition mu r (r x)) A B ∂mu) =
      ∫ y, ∫ x, ∫ z, G z
        ∂(condition (combinedPosteriorKernel mu A B y) r (r x)).prod
          (condition (combinedPosteriorKernel mu A B y) r (r x))
      ∂combinedPosteriorKernel mu A B y ∂pairObservationLaw mu A B := by
  have hk (u : U) : IsMarkovKernel (combinedPosteriorKernel (condition mu r u) A B) :=
    combinedPosteriorKernel_isMarkov (condition mu r u) A B hA hB
  have h := integral_reveal_output_transport mu A B hA hB r hr
    (fun u y ↦ ∫ z, G z ∂(combinedPosteriorKernel (condition mu r u) A B y).prod
      (combinedPosteriorKernel (condition mu r u) A B y))
    (fun u ↦ measurable_replicaIntegral _ G)
    (fun u y ↦ replicaIntegral_abs_le _ G)
  simpa only [combinedPosteriorKernel_condition mu A B hA hB r hr] using h


end TensorPCA.GaussianRevealReplicaProofs
