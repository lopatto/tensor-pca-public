-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.BayesianPinningVarianceProofs

/-! # Finite linearity of the uniform-parameter Bernoulli reveal average -/
@[expose] public section

namespace TensorPCA.FiniteRevealAveragingProofs

open MeasureTheory ProbabilityTheory Set RevealPolynomialProofs BayesianPinningVarianceProofs BayesianPinningProofs

variable {ι : Type*} [DecidableEq ι]

noncomputable def uniformAverage (I : Finset ι) (delta : ℝ) (f : Finset ι → ℝ) : ℝ :=
  ∫ theta, RevealPolynomialProofs.average I f theta ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)

theorem continuous_weight (I A : Finset ι) : Continuous (weight I A) := by
  unfold weight
  apply continuous_finsetProd
  intro i _
  by_cases h : i ∈ A
  · simp only [h, ite_true]
    exact continuous_id
  · simp only [h, ite_false]
    exact continuous_const.sub continuous_id

theorem uniformAverage_eq_sum (I : Finset ι) {delta : ℝ} (hd0 : 0 < delta) (f : Finset ι → ℝ) :
    uniformAverage I delta f = ∑ A ∈ I.powerset,
      (∫ theta, weight I A theta ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) * f A := by
  unfold uniformAverage RevealPolynomialProofs.average
  rw [integral_finsetSum _ (fun A _ ↦
    ((memLp_uniformInterval (continuous_weight I A) hd0 1).integrable le_rfl).mul_const (f A))]
  simp_rw [integral_mul_const]

theorem uniformAverage_const (I : Finset ι) {delta : ℝ} (hd0 : 0 < delta) (c : ℝ) :
    uniformAverage I delta (fun _ ↦ c) = c := by
  have := uniformInterval_probability hd0
  simp only [uniformAverage, BayesianPinningVarianceProofs.average_const, integral_const, probReal_univ, one_smul]

theorem uniformAverage_hasDerivAt (I : Finset ι) {delta t : ℝ} (hd0 : 0 < delta)
    (F : Finset ι → ℝ → ℝ) (d : Finset ι → ℝ) (hF : ∀ A, HasDerivAt (F A) (d A) t) :
    HasDerivAt (fun s ↦ uniformAverage I delta (fun A ↦ F A s)) (uniformAverage I delta d) t := by
  simp_rw [uniformAverage_eq_sum I hd0]
  exact HasDerivAt.fun_sum (fun A _ ↦ (hF A).const_mul _)

theorem continuous_uniformAverage (I : Finset ι) {delta : ℝ} (hd0 : 0 < delta)
    {Y : Type*} [TopologicalSpace Y] (F : Finset ι → Y → ℝ) (hF : ∀ A, Continuous (F A)) :
    Continuous (fun t ↦ uniformAverage I delta (fun A ↦ F A t)) := by
  simp_rw [uniformAverage_eq_sum I hd0]
  exact continuous_finsetSum _ (fun A _ ↦ continuous_const.mul (hF A))

theorem uniformAverage_integral_comm (I : Finset ι) {delta : ℝ} (hd0 : 0 < delta)
    {Y : Type*} [MeasurableSpace Y] (nu : Measure Y) (F : Finset ι → Y → ℝ)
    (hF : ∀ A, Integrable (F A) nu) :
    uniformAverage I delta (fun A ↦ ∫ y, F A y ∂nu) =
      ∫ y, uniformAverage I delta (fun A ↦ F A y) ∂nu := by
  simp_rw [uniformAverage_eq_sum I hd0]
  rw [integral_finsetSum _ (fun A _ ↦ (hF A).const_mul _)]
  simp_rw [integral_const_mul]

theorem finite_integral_hasDerivAt {Omega : Type*} [Fintype Omega] [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega → ℝ → ℝ) (d : Omega → ℝ) {t : ℝ} (hF : ∀ x, HasDerivAt (F x) (d x) t) :
    HasDerivAt (fun s ↦ ∫ x, F x s ∂mu) (∫ x, d x ∂mu) t := by
  simp_rw [integral_fintype Integrable.of_finite, smul_eq_mul]
  exact HasDerivAt.fun_sum (fun x _ ↦ (hF x).const_mul _)


end TensorPCA.FiniteRevealAveragingProofs
