-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteEntropyProofs
public import TensorPCA.GaussianMixtureStabilityProofs

/-! Finite observable reveal cost for the full Gaussian mixture free energy, beginning with a finite positive-density mixture bound. -/
@[expose] public section
namespace TensorPCA.GaussianRevealCostProofs
open MeasureTheory ProbabilityTheory Set Real FiniteEntropyProofs
open GaussianPriorTransferProofs GaussianMixtureStabilityProofs
open scoped BigOperators ENNReal Classical RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DensityMixture
variable {U Y : Type*} [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace Y] (p : Measure U) [IsProbabilityMeasure p]

def densityMix (f : U → Y → ℝ) (y : Y) : ℝ := ∑ u : U, p.real {u}*f u y

omit [MeasurableSpace Y] in
theorem density_gap_nonneg (f : U → Y → ℝ) (hpos : ∀ u y, 0 < f u y) (y : Y) :
    0 ≤ (∑ u : U, p.real {u}*(f u y*Real.log (f u y)))-
      densityMix p f y*Real.log (densityMix p f y) := by
  have H : (∑ u : U, p.real {u}*Real.negMulLog (f u y)) ≤
      Real.negMulLog (densityMix p f y) := by
    exact Real.concaveOn_negMulLog.le_map_sum (by intro u _; exact measureReal_nonneg)
      (by simp) (by intro u _; exact (hpos u y).le)
  simp only [Real.negMulLog, neg_mul, mul_neg, Finset.sum_neg_distrib] at H
  linarith

omit [MeasurableSingletonClass U] [MeasurableSpace Y] [IsProbabilityMeasure p] in
theorem density_gap_le (f : U → Y → ℝ) (hpos : ∀ u y, 0 < f u y) (y : Y) :
    (∑ u : U, p.real {u}*(f u y*Real.log (f u y)))-
      densityMix p f y*Real.log (densityMix p f y) ≤
        ∑ u : U, Real.negMulLog (p.real {u})*f u y := by
  have hterm (u : U) : p.real {u}*(f u y*Real.log (f u y))-
      (p.real {u}*f u y)*Real.log (densityMix p f y) ≤ Real.negMulLog (p.real {u})*f u y := by
    by_cases hz : p.real {u} = 0
    · simp [hz, Real.negMulLog]
    have hp : 0 < p.real {u} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hz)
    have hm : p.real {u}*f u y ≤ densityMix p f y :=
      Finset.single_le_sum (fun v _ ↦ mul_nonneg measureReal_nonneg (hpos v y).le) (Finset.mem_univ u)
    have hl := Real.log_le_log (mul_pos hp (hpos u y)) hm
    rw [Real.log_mul hp.ne' (hpos u y).ne'] at hl
    have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hp.le (hpos u y).le)
    unfold Real.negMulLog
    nlinarith
  calc
    _ = ∑ u : U, (p.real {u}*(f u y*Real.log (f u y))-
        (p.real {u}*f u y)*Real.log (densityMix p f y)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ ≤ _ := Finset.sum_le_sum (fun u _ ↦ hterm u)

/-- The entropy gap of an actual finite normalized positive-density mixture
lies between zero and the entropy of the mixing label. All integrability
conditions concern these explicit densities and are discharged below for
the actual Gaussian likelihoods. -/
theorem finite_density_entropy_gap (mu : Measure Y) (f : U → Y → ℝ)
    (hpos : ∀ u y, 0 < f u y) (hint : ∀ u, Integrable (f u) mu)
    (hunit : ∀ u, (∫ y, f u y ∂mu) = 1)
    (hlog : ∀ u, Integrable (fun y ↦ f u y*Real.log (f u y)) mu)
    (hmix : Integrable (fun y ↦ densityMix p f y*Real.log (densityMix p f y)) mu) :
    0 ≤ (∑ u : U, p.real {u}*(∫ y, f u y*Real.log (f u y) ∂mu))-
        (∫ y, densityMix p f y*Real.log (densityMix p f y) ∂mu) ∧
    (∑ u : U, p.real {u}*(∫ y, f u y*Real.log (f u y) ∂mu))-
        (∫ y, densityMix p f y*Real.log (densityMix p f y) ∂mu) ≤ entropy p := by
  have hsum := integrable_finsetSum Finset.univ
    (fun u _ ↦ (hlog u).const_mul (p.real {u}))
  have hrhs := integrable_finsetSum Finset.univ
    (fun u _ ↦ (hint u).const_mul (Real.negMulLog (p.real {u})))
  constructor
  · have H : 0 ≤ ∫ y, (∑ u : U, p.real {u}*(f u y*Real.log (f u y)))-
        densityMix p f y*Real.log (densityMix p f y) ∂mu :=
      integral_nonneg (fun y ↦ density_gap_nonneg p f hpos y)
    rw [integral_sub hsum hmix, integral_finsetSum Finset.univ
      (fun u _ ↦ (hlog u).const_mul (p.real {u}))] at H
    simpa only [integral_const_mul] using H
  · have H := integral_mono_ae (hsum.sub hmix) hrhs
      (Filter.Eventually.of_forall (fun y ↦ density_gap_le p f hpos y))
    simp only [Pi.sub_apply] at H
    rw [integral_sub hsum hmix, integral_finsetSum Finset.univ
      (fun u _ ↦ (hlog u).const_mul (p.real {u})), integral_finsetSum Finset.univ
      (fun u _ ↦ (hint u).const_mul (Real.negMulLog (p.real {u})))] at H
    simpa only [integral_const_mul, hunit, mul_one, entropy] using H

end DensityMixture

theorem condition_absolutelyContinuous {Omega U : Type*} [MeasurableSpace Omega]
    [MeasurableSpace U] (q : Measure Omega) (r : Omega → U) (u : U) :
    condition q r u ≪ q := by
  unfold condition
  split_ifs
  · exact Measure.AbsolutelyContinuous.refl q
  · exact cond_absolutelyContinuous

theorem integral_eq_sum_conditions {Omega U : Type*} [MeasurableSpace Omega]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (q : Measure Omega) [IsProbabilityMeasure q] (r : Omega → U) (hr : Measurable r)
    (f : Omega → ℝ) (hint : ∀ u, Integrable f (condition q r u)) :
    (∫ x, f x ∂q) = ∑ u : U, q.real (r ⁻¹' {u})*(∫ x, f x ∂condition q r u) := by
  calc
    _ = ∫ x, f x ∂(∑ u : U, q (r ⁻¹' {u}) • condition q r u) := by
      rw [sum_weighted_condition q r hr]
    _ = _ := by
      rw [integral_finsetSum_measure (fun u _ ↦ (hint u).smul_measure (measure_ne_top q _))]
      simp only [integral_smul_measure, smul_eq_mul, measureReal_def]

section Gaussian
variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem mixture_density_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) : Integrable (mixtureLikelihood q A) (stdGaussian E) := by
  have := mixtureLaw_probability q A hA
  have hi : Integrable (fun _ : E ↦ (1 : ℝ)) (mixtureLaw q A) := integrable_const 1
  rw [mixtureLaw_eq_withDensity q A hA] at hi
  have hh := (integrable_withDensity_iff (measurable_mixtureLikelihood q A hA).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (mixtureLikelihood_pos q A hA _).le, one_mul] using hh

theorem integral_mixture_density (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) : (∫ y, mixtureLikelihood q A y ∂stdGaussian E) = 1 := by
  have := mixtureLaw_probability q A hA
  have H : (∫ y : E, (1 : ℝ) ∂mixtureLaw q A) = 1 := by simp
  rw [mixtureLaw_eq_withDensity q A hA, integral_withDensity_eq_integral_toReal_smul
    (measurable_mixtureLikelihood q A hA).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))] at H
  simpa only [ENNReal.toReal_ofReal (mixtureLikelihood_pos q A hA _).le, smul_eq_mul, mul_one] using H

theorem mixture_density_log_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) (hA2 : MemLp A 2 q) :
    Integrable (fun y ↦ mixtureLikelihood q A y*Real.log (mixtureLikelihood q A y)) (stdGaussian E) := by
  have hi := integrable_mixtureLogLikelihood q A hA hA2
  rw [mixtureLaw_eq_withDensity q A hA] at hi
  have hh := (integrable_withDensity_iff (measurable_mixtureLikelihood q A hA).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (mixtureLikelihood_pos q A hA _).le, mul_comm] using hh

theorem mixtureFreeEnergy_eq_densityIntegral (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) :
    mixtureFreeEnergy q A =
      ∫ y, mixtureLikelihood q A y*Real.log (mixtureLikelihood q A y) ∂stdGaussian E := by
  rw [mixtureFreeEnergy_eq_integral q A hA, mixtureLaw_eq_withDensity q A hA,
    integral_withDensity_eq_integral_toReal_smul (measurable_mixtureLikelihood q A hA).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mixtureLikelihood_pos q A hA _).le, smul_eq_mul]

theorem densityMix_conditional_likelihood {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (q : Measure Omega) [IsProbabilityMeasure q]
    (r : Omega → U) (hr : Measurable r) (A : Omega → E) (hA : Measurable A) :
    densityMix (q.map r) (fun u ↦ mixtureLikelihood (condition q r u) A) = mixtureLikelihood q A := by
  funext y
  have hint (u : U) : Integrable (fun x ↦ mixtureWeight (A x) y) (condition q r u) := by
    have := condition_probability q r u
    exact integrable_mixtureWeight _ A hA y
  rw [mixtureLikelihood, integral_eq_sum_conditions q r hr _ hint]
  apply Finset.sum_congr rfl
  intro u _
  change (q.map r).real {u}*(∫ x, mixtureWeight (A x) y ∂condition q r u) = _
  rw [measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]
  rfl

/-- Revealing a finite observable increases the actual output free energy
by a quantity between zero and the actual entropy of that observable.
All conditional priors, including the explicit null-fiber fallback, retain
the full nonunit Gaussian signal penalty. -/
theorem gaussian_reveal_freeEnergy_cost {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (q : Measure Omega) [IsProbabilityMeasure q]
    (r : Omega → U) (hr : Measurable r) (A : Omega → E) (hA : Measurable A)
    {K : ℝ} (hAB : ∀ᵐ x ∂q, ‖A x‖ ≤ K) :
    0 ≤ (∑ u : U, q.real (r ⁻¹' {u})*mixtureFreeEnergy (condition q r u) A)-mixtureFreeEnergy q A ∧
    (∑ u : U, q.real (r ⁻¹' {u})*mixtureFreeEnergy (condition q r u) A)-mixtureFreeEnergy q A ≤
      entropy (q.map r) := by
  have : IsProbabilityMeasure (q.map r) := (Measure.isProbabilityMeasure_map_iff hr.aemeasurable).mpr inferInstance
  have hA2 : MemLp A 2 q := MemLp.of_bound hA.aestronglyMeasurable K hAB
  have hU2 (u : U) : MemLp A 2 (condition q r u) := by
    have := condition_probability q r u
    exact MemLp.of_bound hA.aestronglyMeasurable K ((condition_absolutelyContinuous q r u).ae_le hAB)
  have hi (u : U) : Integrable (mixtureLikelihood (condition q r u) A) (stdGaussian E) := by
    have := condition_probability q r u
    exact mixture_density_integrable _ A hA
  have hu (u : U) : (∫ y, mixtureLikelihood (condition q r u) A y ∂stdGaussian E) = 1 := by
    have := condition_probability q r u
    exact integral_mixture_density _ A hA
  have hp (u : U) (y : E) : 0 < mixtureLikelihood (condition q r u) A y := by
    have := condition_probability q r u
    exact mixtureLikelihood_pos _ A hA y
  have hl (u : U) : Integrable (fun y ↦ mixtureLikelihood (condition q r u) A y*
      Real.log (mixtureLikelihood (condition q r u) A y)) (stdGaussian E) := by
    have := condition_probability q r u
    exact mixture_density_log_integrable _ A hA (hU2 u)
  have hm : Integrable (fun y ↦ densityMix (q.map r) (fun u ↦ mixtureLikelihood (condition q r u) A) y*
      Real.log (densityMix (q.map r) (fun u ↦ mixtureLikelihood (condition q r u) A) y)) (stdGaussian E) := by
    rw [densityMix_conditional_likelihood q r hr A hA]
    exact mixture_density_log_integrable q A hA hA2
  have H := finite_density_entropy_gap (q.map r) (stdGaussian E)
    (fun u ↦ mixtureLikelihood (condition q r u) A) hp hi hu hl hm
  rw [densityMix_conditional_likelihood q r hr A hA,
    ← mixtureFreeEnergy_eq_densityIntegral q A hA] at H
  have hFE (u : U) : (∫ y, mixtureLikelihood (condition q r u) A y*
      Real.log (mixtureLikelihood (condition q r u) A y) ∂stdGaussian E) =
      mixtureFreeEnergy (condition q r u) A := by
    have := condition_probability q r u
    exact (mixtureFreeEnergy_eq_densityIntegral _ A hA).symm
  have hw (u : U) : (q.map r).real {u} = q.real (r ⁻¹' {u}) := by
    simp only [measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]
  simpa only [hFE,hw] using H

theorem gaussian_reveal_freeEnergy_cost_integral {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] (q : Measure Omega) [IsProbabilityMeasure q]
    (r : Omega → U) (hr : Measurable r) (A : Omega → E) (hA : Measurable A)
    {K : ℝ} (hAB : ∀ᵐ x ∂q, ‖A x‖ ≤ K) :
    0 ≤ (∫ x, mixtureFreeEnergy (condition q r (r x)) A ∂q)-mixtureFreeEnergy q A ∧
    (∫ x, mixtureFreeEnergy (condition q r (r x)) A ∂q)-mixtureFreeEnergy q A ≤ entropy (q.map r) := by
  let f : U → ℝ := fun u ↦ mixtureFreeEnergy (condition q r u) A
  have hi := integral_map (μ := q) hr.aemeasurable (Integrable.of_finite (f := f)).aestronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at hi
  have hw (u : U) : (q.map r).real {u} = q.real (r ⁻¹' {u}) := by
    simp only [measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]
  simp only [hw, smul_eq_mul] at hi
  rw [← hi]
  exact gaussian_reveal_freeEnergy_cost q r hr A hA hAB

end Gaussian
end
end TensorPCA.GaussianRevealCostProofs
