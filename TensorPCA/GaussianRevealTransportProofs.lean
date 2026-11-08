-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianFiniteRevealProofs

/-! # Gaussian output transport under finite reveals -/
@[expose] public section

namespace TensorPCA.GaussianRevealTransportProofs

open MeasureTheory ProbabilityTheory GaussianPriorTransferProofs GaussianPosteriorProofs
open GaussianSideChannelProofs GaussianReplicaTransportProofs GaussianCombinedPosteriorProofs
open GaussianFiniteRevealProofs FiniteEntropyProofs

attribute [local instance] condition_probability

variable {Omega E D U : Type*} [Fintype Omega] [MeasurableSpace Omega]
  [MeasurableSingletonClass Omega] [MeasurableSpace U] [MeasurableSingletonClass U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

/-- Revealing a finite observable reweights the actual output law by its
posterior probability. The identity includes zero-mass reveal fibers. -/
theorem weighted_pairObservationLaw_condition (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (u : U) :
    mu (r ⁻¹' {u}) • pairObservationLaw (condition mu r u) A B =
      (pairObservationLaw mu A B).withDensity
        (fun y ↦ combinedPosteriorKernel mu A B y (r ⁻¹' {u})) := by
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have hZ : Measurable (fun p : D × E ↦ ENNReal.ofReal (combinedLikelihood mu A B p.2 p.1)) :=
    ((measurable_combinedLikelihood mu A B hA hB).comp measurable_swap).ennreal_ofReal
  have hC : Measurable (fun p : D × E ↦ ENNReal.ofReal (combinedLikelihood (condition mu r u) A B p.2 p.1)) :=
    ((measurable_combinedLikelihood (condition mu r u) A B hA hB).comp measurable_swap).ennreal_ofReal
  have hP := Kernel.measurable_coe (combinedPosteriorKernel mu A B) (hr (measurableSet_singleton u))
  rw [pairObservationLaw_eq_withDensity (condition mu r u) A B hA hB,
    pairObservationLaw_eq_withDensity mu A B hA hB, ← withDensity_smul _ hC,
    ← withDensity_mul _ hZ hP]
  congr 1
  funext y
  change mu (r ⁻¹' {u}) * ENNReal.ofReal (combinedLikelihood (condition mu r u) A B y.2 y.1) =
    ENNReal.ofReal (combinedLikelihood mu A B y.2 y.1) * combinedPosteriorKernel mu A B y (r ⁻¹' {u})
  have h := congrArg ENNReal.ofReal (combinedLikelihood_reveal_evidence mu A B hA hB r hr u y)
  rw [ENNReal.ofReal_mul measureReal_nonneg,
    ENNReal.ofReal_mul (combinedLikelihood_pos mu A B hA hB y.2 y.1).le] at h
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

/-- Exact integral transport, with the ordinary Bochner zero convention on
nonintegrable functions retained on both sides. -/
theorem weighted_integral_pairObservationLaw_condition (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (u : U) (f : D × E → ℝ) :
    mu.real (r ⁻¹' {u}) * ∫ y, f y ∂pairObservationLaw (condition mu r u) A B =
      ∫ y, (combinedPosteriorKernel mu A B y).real (r ⁻¹' {u}) * f y ∂pairObservationLaw mu A B := by
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have hP := Kernel.measurable_coe (combinedPosteriorKernel mu A B) (hr (measurableSet_singleton u))
  change (mu (r ⁻¹' {u})).toReal • (∫ y, f y ∂pairObservationLaw (condition mu r u) A B) = _
  rw [← integral_smul_measure, weighted_pairObservationLaw_condition mu A B hA hB r hr u,
    integral_withDensity_eq_integral_toReal_smul hP (Filter.Eventually.of_forall fun y ↦ measure_lt_top _ _) f]
  rfl

omit [Fintype Omega] [MeasurableSingletonClass Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
theorem integral_finite_observable [Fintype U] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (r : Omega → U) (hr : Measurable r) (f : U → ℝ) :
    ∫ x, f (r x) ∂mu = ∑ u, mu.real (r ⁻¹' {u}) * f u := by
  rw [← integral_map hr.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro u _
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]
  rfl

/-- Revealed-prior outputs and latent draws transport to the original actual
output and its actual posterior; no point conditioning on Gaussian values occurs. -/
theorem integral_reveal_output_transport [Fintype U] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (A : Omega → E) (B : Omega → D) (hA : Measurable A) (hB : Measurable B)
    (r : Omega → U) (hr : Measurable r) (F : U → D × E → ℝ)
    (hF : ∀ u, Measurable (F u)) {C : ℝ} (hFC : ∀ u y, |F u y| ≤ C) :
    (∫ x, ∫ y, F (r x) y ∂pairObservationLaw (condition mu r (r x)) A B ∂mu) =
      ∫ y, ∫ x, F (r x) y ∂combinedPosteriorKernel mu A B y ∂pairObservationLaw mu A B := by
  have : IsMarkovKernel (combinedPosteriorKernel mu A B) := combinedPosteriorKernel_isMarkov mu A B hA hB
  have : IsProbabilityMeasure (pairObservationLaw mu A B) := pairObservationLaw_probability mu A B hA hB
  have hi (u : U) : Integrable
      (fun y ↦ (combinedPosteriorKernel mu A B y).real (r ⁻¹' {u}) * F u y)
      (pairObservationLaw mu A B) := by
    refine Integrable.of_bound
      (((Kernel.measurable_coe (combinedPosteriorKernel mu A B) (hr (measurableSet_singleton u))).ennreal_toReal).mul (hF u)).aestronglyMeasurable C ?_
    exact .of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
      exact (mul_le_mul_of_nonneg_right measureReal_le_one (abs_nonneg _)).trans (by simpa using hFC u y)
  rw [integral_finite_observable mu r hr (fun u ↦ ∫ y, F u y ∂pairObservationLaw (condition mu r u) A B)]
  simp_rw [weighted_integral_pairObservationLaw_condition mu A B hA hB r hr]
  rw [← integral_finsetSum _ (fun u _ ↦ hi u)]
  apply integral_congr_ae
  exact .of_forall fun y ↦ (integral_finite_observable (combinedPosteriorKernel mu A B y) r hr (fun u ↦ F u y)).symm


end TensorPCA.GaussianRevealTransportProofs
