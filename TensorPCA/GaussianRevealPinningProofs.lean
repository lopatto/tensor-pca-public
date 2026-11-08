-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealReplicaProofs
public import TensorPCA.FiniteRevealAveragingProofs
public import TensorPCA.GuerraPinningProofs

/-! # Finite pinning applied to the full Gaussian posterior -/
@[expose] public section

namespace TensorPCA.GaussianRevealPinningProofs

open MeasureTheory ProbabilityTheory Set GaussianSideChannelProofs GaussianReplicaTransportProofs
open GaussianCombinedPosteriorProofs GaussianFiniteRevealProofs GaussianRevealReplicaProofs
open FiniteEntropyProofs FiniteRevealProofs FiniteRevealAveragingProofs GuerraPinningProofs

attribute [local instance] condition_probability posterior_probability

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega E D U : Type*} [Fintype Omega] [MeasurableSpace Omega] [MeasurableSingletonClass Omega]
  [MeasurableSpace U] [MeasurableSingletonClass U] [Fintype U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

omit [Fintype U] in
theorem integrable_revealedReplicaAverage (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (G : Omega × Omega → ℝ) :
    Integrable (fun y ↦ ∫ x, ∫ z, G z
      ∂(condition (combinedPosteriorKernel mu A B y) r (r x)).prod
        (condition (combinedPosteriorKernel mu A B y) r (r x))
      ∂combinedPosteriorKernel mu A B y) (pairObservationLaw mu A B) := by
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have : IsProbabilityMeasure (pairObservationLaw mu A B) := pairObservationLaw_probability mu A B hA hB
  have hk (x : Omega) : IsMarkovKernel (combinedPosteriorKernel (condition mu r (r x)) A B) :=
    combinedPosteriorKernel_isMarkov (condition mu r (r x)) A B hA hB
  have hmeas : Measurable (fun y ↦ ∫ x, ∫ z, G z
      ∂(condition (combinedPosteriorKernel mu A B y) r (r x)).prod
        (condition (combinedPosteriorKernel mu A B y) r (r x))
      ∂combinedPosteriorKernel mu A B y) := by
    have heq (y : D × E) : (∫ x, ∫ z, G z
        ∂(condition (combinedPosteriorKernel mu A B y) r (r x)).prod
          (condition (combinedPosteriorKernel mu A B y) r (r x))
        ∂combinedPosteriorKernel mu A B y) =
      ∑ x, (combinedPosteriorKernel mu A B y).real {x} *
        ∫ z, G z ∂(combinedPosteriorKernel (condition mu r (r x)) A B y).prod
          (combinedPosteriorKernel (condition mu r (r x)) A B y) := by
      simp_rw [← combinedPosteriorKernel_condition mu A B hA hB r hr]
      rw [integral_fintype Integrable.of_finite]
      rfl
    simp_rw [heq]
    apply Finset.measurable_sum
    intro x _
    exact ((Kernel.measurable_coe _ (measurableSet_singleton x)).ennreal_toReal).mul
      (measurable_replicaIntegral _ G)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ z, |G z|) ?_
  exact .of_forall fun y ↦ by
    have hb : ∀ᵐ x ∂combinedPosteriorKernel mu A B y,
        ‖∫ z, G z ∂(condition (combinedPosteriorKernel mu A B y) r (r x)).prod
          (condition (combinedPosteriorKernel mu A B y) r (r x))‖ ≤ ∑ z, |G z| :=
      .of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using replicaIntegral_abs_le _ G
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

section Configuration

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N : ℕ}

/-- The actual revealed Gaussian experiment has the signed tensor-response
lower bound from finite pinning, uniformly in the two Gaussian signal maps. -/
theorem actual_gaussian_pinning_tensor_response_lower_bound
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (A : (Fin N → S) → E) (B : (Fin N → S) → D) (hA : Measurable A) (hB : Measurable B)
    (a : S → ℝ) (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K)
    {k : ℕ} (hk : 0 < k) {m delta : ℝ} (hm : 0 ≤ m) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
      (k : ℝ)^2*K^(2*k)/(N : ℝ) ≤
    uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y, ∫ z,
      tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*PosteriorPairProofs.overlap a z
      ∂(combinedPosteriorKernel (posterior mu mask x) A B y).prod
        (combinedPosteriorKernel (posterior mu mask x) A B y)
      ∂pairObservationLaw (posterior mu mask x) A B ∂mu) := by
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have : IsProbabilityMeasure (pairObservationLaw mu A B) := pairObservationLaw_probability mu A B hA hB
  let G : (Fin N → S) × (Fin N → S) → ℝ := fun z ↦
    tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*PosteriorPairProofs.overlap a z
  have htrans (mask : Finset (Fin N)) := integral_reveal_replica_transport mu A B hA hB
    (observation mask) (measurable_of_finite _) G
  unfold posterior
  change _ ≤ uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y, ∫ z, G z
    ∂(combinedPosteriorKernel (condition mu (observation mask) (observation mask x)) A B y).prod
      (combinedPosteriorKernel (condition mu (observation mask) (observation mask x)) A B y)
    ∂pairObservationLaw (condition mu (observation mask) (observation mask x)) A B ∂mu)
  simp_rw [htrans]
  rw [uniformAverage_integral_comm Finset.univ hd0 (pairObservationLaw mu A B)
    _ (fun mask ↦ integrable_revealedReplicaAverage mu A B hA hB
      (observation mask) (measurable_of_finite _) G)]
  have hi : Integrable (fun y ↦ uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ z, G z
      ∂(posterior (combinedPosteriorKernel mu A B y) mask x).prod
        (posterior (combinedPosteriorKernel mu A B y) mask x)
      ∂combinedPosteriorKernel mu A B y)) (pairObservationLaw mu A B) := by
    simp_rw [uniformAverage_eq_sum Finset.univ hd0]
    exact integrable_finsetSum _ (fun mask _ ↦
      (integrable_revealedReplicaAverage mu A B hA hB (observation mask) (measurable_of_finite _) G).const_mul _)
  have h := integral_mono_ae (integrable_const
    ((1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
      (k : ℝ)^2*K^(2*k)/(N : ℝ))) hi
    (.of_forall fun y ↦ finite_pinning_tensor_response_lower_bound
      (combinedPosteriorKernel mu A B y) a hN hK ha hk hm hd0 hd1)
  simp only [integral_const, probReal_univ, one_smul] at h
  convert h using 1
  rfl

end Configuration


end TensorPCA.GaussianRevealPinningProofs
