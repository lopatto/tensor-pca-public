-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteLikelihoodUpdateProofs
public import TensorPCA.GaussianCombinedPosteriorProofs
public import TensorPCA.FiniteRevealProofs

/-! # Gaussian posterior conditioning commutes with finite reveals -/
@[expose] public section

namespace TensorPCA.GaussianFiniteRevealProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs FiniteEntropyProofs FiniteLikelihoodUpdateProofs
open scoped RealInnerProductSpace

attribute [local instance] condition_probability

variable {Omega E D : Type*} [Fintype Omega] [MeasurableSpace Omega] [MeasurableSingletonClass Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

omit [Fintype Omega] [MeasurableSingletonClass Omega]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
theorem combinedLikelihood_eq_integral_product (mu : Measure Omega) (A : Omega → E) (B : Omega → D)
    (p : D × E) : combinedLikelihood mu A B p.2 p.1 =
      ∫ x, mixtureWeight (B x) p.1 * mixtureWeight (A x) p.2 ∂mu := by
  apply integral_congr_ae
  exact .of_forall fun x ↦ mul_comm _ _

omit [MeasurableSingletonClass Omega] in
theorem combinedPosteriorKernel_eq_likelihoodUpdate (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B) (p : D × E) :
    combinedPosteriorKernel mu A B p =
      likelihoodUpdate mu (fun x ↦ mixtureWeight (B x) p.1 * mixtureWeight (A x) p.2) := by
  rw [combinedPosteriorKernel, Kernel.withDensity_apply _ (measurable_combinedPosteriorWeight mu A B hA hB),
    Kernel.const_apply, likelihoodUpdate]
  congr 1
  funext x
  rw [combinedPosteriorWeight, combinedLikelihood_eq_integral_product]

/-- Exact finite-reveal Bayes commutation, including null reveal fibers. -/
theorem combinedPosteriorKernel_condition {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (u : U) (p : D × E) :
    combinedPosteriorKernel (condition mu r u) A B p = condition (combinedPosteriorKernel mu A B p) r u := by
  rw [combinedPosteriorKernel_eq_likelihoodUpdate (condition mu r u) A B hA hB,
    combinedPosteriorKernel_eq_likelihoodUpdate mu A B hA hB]
  exact likelihoodUpdate_condition mu _ (fun x ↦ mul_pos (mixtureWeight_pos _ _) (mixtureWeight_pos _ _)) r hr u

theorem combinedLikelihood_reveal_evidence {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (u : U) (p : D × E) :
    mu.real (r ⁻¹' {u}) * combinedLikelihood (condition mu r u) A B p.2 p.1 =
      combinedLikelihood mu A B p.2 p.1 * (combinedPosteriorKernel mu A B p).real (r ⁻¹' {u}) := by
  rw [combinedLikelihood_eq_integral_product, combinedLikelihood_eq_integral_product,
    combinedPosteriorKernel_eq_likelihoodUpdate mu A B hA hB]
  exact (likelihoodUpdate_fiber_evidence mu _
    (fun x ↦ mul_pos (mixtureWeight_pos _ _) (mixtureWeight_pos _ _)) r hr u).symm

attribute [local instance] FiniteRevealProofs.posterior_probability

theorem combinedPosteriorKernel_coordinateReveal {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ} (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (A : (Fin N → S) → E) (B : (Fin N → S) → D) (hA : Measurable A) (hB : Measurable B)
    (mask : Finset (Fin N)) (x : Fin N → S) (p : D × E) :
    combinedPosteriorKernel (FiniteRevealProofs.posterior mu mask x) A B p =
      FiniteRevealProofs.posterior (combinedPosteriorKernel mu A B p) mask x :=
  combinedPosteriorKernel_condition mu A B hA hB (FiniteRevealProofs.observation mask)
    (measurable_of_finite _) (FiniteRevealProofs.observation mask x) p


end TensorPCA.GaussianFiniteRevealProofs
