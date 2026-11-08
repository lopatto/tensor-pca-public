-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteRevealProofs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Probability.Distributions.Uniform

/-! Finite reveal pinning for an arbitrary posterior law.
The entropy center remains random when this result is applied pointwise to
an observation-dependent posterior. -/
@[expose] public section
namespace TensorPCA.BayesianPinningProofs
open MeasureTheory ProbabilityTheory Set Real FiniteRevealProofs RevealPolynomialProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem average_neg {ι : Type*} [DecidableEq ι] (I : Finset ι) (h : Finset ι → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ -h A) theta = -RevealPolynomialProofs.average I h theta := by
  unfold RevealPolynomialProofs.average
  simp only [mul_neg, Finset.sum_neg_distrib]

theorem average_sum {ι κ : Type*} [DecidableEq ι] (I : Finset ι) (J : Finset κ)
    (h : κ → Finset ι → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ ∑ i ∈ J, h i A) theta = ∑ i ∈ J, RevealPolynomialProofs.average I (h i) theta := by
  unfold RevealPolynomialProofs.average
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_div_const {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (h : Finset ι → ℝ) (theta c : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ h A/c) theta =
      RevealPolynomialProofs.average I h theta/c := by
  simp only [RevealPolynomialProofs.average, mul_div_assoc, Finset.sum_div]

/-- The standard conditional-volume law on a nondegenerate interval is
the actual uniform probability law. -/
theorem uniformInterval_probability {delta : ℝ} (hd : 0 < delta) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) delta)) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_Icc, sub_zero, ne_eq, ENNReal.ofReal_eq_zero] using not_le.mpr hd
  · simp only [Real.volume_Icc, sub_zero, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]

theorem integral_uniformInterval (f : ℝ → ℝ) {delta : ℝ} (hd : 0 ≤ delta) :
    (∫ theta, f theta ∂ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) delta)) =
      (∫ theta in (0 : ℝ)..delta, f theta)/delta := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hd,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd]
  simp only [smul_eq_mul]
  ring

theorem average_erase_of_insert_zero {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (h : Finset ι → ℝ) (i : ι) (hi : i ∈ I)
    (hz : ∀ A, h (insert i A) = 0) (theta : ℝ) :
    RevealPolynomialProofs.average I h theta = (1-theta)*RevealPolynomialProofs.average (I.erase i) h theta := by
  have he := average_insert (I.erase i) h i (Finset.notMem_erase i I) theta
  rw [Finset.insert_erase hi] at he
  have hzero : RevealPolynomialProofs.average (I.erase i) (fun A ↦ h (insert i A)) theta = 0 := by
    unfold RevealPolynomialProofs.average
    apply Finset.sum_eq_zero
    intro A _
    change weight (I.erase i) A theta*h (insert i A) = 0
    rw [hz, mul_zero]
  rw [hzero, mul_zero, add_zero] at he
  exact he

section Posterior
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]

def entropyPotential (I : Finset (Fin N)) (theta : ℝ) : ℝ :=
  ∑ i ∈ I, RevealPolynomialProofs.average (I.erase i) (fun A ↦ coordinateEntropy q A i) theta

def excludedInformation (I : Finset (Fin N)) (theta : ℝ) : ℝ :=
  ∑ i ∈ I, ∑ j ∈ I.erase i,
    RevealPolynomialProofs.average ((I.erase i).erase j) (fun A ↦ revealedPairInformation q A i j) theta

def totalInformation (I : Finset (Fin N)) (theta : ℝ) : ℝ :=
  RevealPolynomialProofs.average I (fun A ↦ ∑ i ∈ I, ∑ j ∈ I, revealedPairInformation q A i j) theta

omit [MeasurableSingletonClass S] in
theorem entropyPotential_nonneg (I : Finset (Fin N)) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    0 ≤ entropyPotential q I theta := by
  apply Finset.sum_nonneg
  intro i _
  exact average_nonneg _ _ h0 h1 (fun A _ ↦ coordinateEntropy_nonneg q A i)

theorem entropyPotential_le (I : Finset (Fin N)) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    entropyPotential q I theta ≤ (I.card : ℝ)*Real.log (Fintype.card S) := by
  calc
    _ ≤ ∑ i ∈ I, Real.log (Fintype.card S) := by
      apply Finset.sum_le_sum
      intro i _
      exact average_le_const _ _ h0 h1 (fun A _ ↦ coordinateEntropy_le_log_card q A i)
    _ = _ := by simp

omit [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem excludedInformation_nonneg (I : Finset (Fin N)) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    0 ≤ excludedInformation q I theta := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact average_nonneg _ _ h0 h1 (fun A _ ↦ revealedPairInformation_nonneg q A i j)

/-- The finite entropy potential has the actual negative excluded-pair
information as its derivative. No derivative identity is assumed. -/
theorem entropyPotential_hasDerivAt (I : Finset (Fin N)) (theta : ℝ) :
    HasDerivAt (entropyPotential q I) (-excludedInformation q I theta) theta := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ I) ↦
    average_hasDerivAt (I.erase i) (fun A ↦ coordinateEntropy q A i) theta)
  have he : (∑ i ∈ I, ∑ j ∈ I.erase i,
      RevealPolynomialProofs.average ((I.erase i).erase j) (fun A ↦ coordinateEntropy q (insert j A) i-coordinateEntropy q A i) theta) =
      -excludedInformation q I theta := by
    unfold excludedInformation
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hfun : (fun A ↦ coordinateEntropy q (insert j A) i-coordinateEntropy q A i) =
        (fun A ↦ -revealedPairInformation q A i j) := funext (fun A ↦ coordinateEntropy_insert q A i j)
    rw [hfun, average_neg]
  rw [he] at hd
  convert! hd using 1

omit [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem excludedInformation_continuous (I : Finset (Fin N)) : Continuous (excludedInformation q I) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact average_continuous _ _

theorem average_pairInformation_le_excluded (I : Finset (Fin N)) (i j : Fin N)
    (hi : i ∈ I) (hj : j ∈ I) (hji : j ≠ i) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    RevealPolynomialProofs.average I (fun A ↦ revealedPairInformation q A i j) theta ≤
      RevealPolynomialProofs.average ((I.erase i).erase j)
        (fun A ↦ revealedPairInformation q A i j) theta := by
  rw [average_erase_of_insert_zero I _ i hi (fun A ↦
    revealedPairInformation_eq_zero_of_mem_left q (insert i A) i j (Finset.mem_insert_self _ _))]
  rw [average_erase_of_insert_zero (I.erase i) _ j (Finset.mem_erase.mpr ⟨hji,hj⟩) (fun A ↦
    revealedPairInformation_eq_zero_of_mem_right q (insert j A) i j (Finset.mem_insert_self _ _))]
  have ha := average_nonneg ((I.erase i).erase j)
    (fun A ↦ revealedPairInformation q A i j) h0 h1
      (fun A _ ↦ revealedPairInformation_nonneg q A i j)
  have hfactor : (1-theta)*(1-theta) ≤ 1 := by nlinarith
  simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hfactor ha

theorem totalInformation_le (I : Finset (Fin N)) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    totalInformation q I theta ≤ (I.card : ℝ)*Real.log (Fintype.card S)+excludedInformation q I theta := by
  unfold totalInformation excludedInformation
  rw [average_sum]
  calc
    _ ≤ ∑ i ∈ I, (Real.log (Fintype.card S)+
        ∑ j ∈ I.erase i, RevealPolynomialProofs.average ((I.erase i).erase j)
          (fun A ↦ revealedPairInformation q A i j) theta) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [average_sum, ← Finset.add_sum_erase _ _ hi]
      apply add_le_add
      · exact average_le_const I _ h0 h1 (fun A _ ↦ by
          rw [revealedPairInformation_diagonal]
          exact coordinateEntropy_le_log_card q A i)
      · apply Finset.sum_le_sum
        intro j hj
        exact average_pairInformation_le_excluded q I i j hi (Finset.mem_erase.mp hj).2
          (Finset.mem_erase.mp hj).1 h0 h1
    _ = _ := by rw [Finset.sum_add_distrib]; simp

omit [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem totalInformation_continuous (I : Finset (Fin N)) : Continuous (totalInformation q I) :=
  average_continuous _ _

theorem integral_excludedInformation (I : Finset (Fin N)) (delta : ℝ) :
    (∫ theta in (0 : ℝ)..delta, excludedInformation q I theta) =
      entropyPotential q I 0-entropyPotential q I delta := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta (_ : theta ∈ Set.uIcc (0 : ℝ) delta) ↦ entropyPotential_hasDerivAt q I theta)
    ((excludedInformation_continuous q I).neg.intervalIntegrable (0 : ℝ) delta)
  rw [intervalIntegral.integral_neg] at H
  linarith

theorem integral_totalInformation_le (I : Finset (Fin N)) {delta : ℝ}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (∫ theta in (0 : ℝ)..delta, totalInformation q I theta) ≤
      2*(I.card : ℝ)*Real.log (Fintype.card S) := by
  have hC : 0 ≤ (I.card : ℝ)*Real.log (Fintype.card S) :=
    (entropyPotential_nonneg q I (theta := 0) le_rfl zero_le_one).trans
      (entropyPotential_le q I (theta := 0) le_rfl zero_le_one)
  have H := intervalIntegral.integral_mono_on (μ := volume) hd0
    ((totalInformation_continuous q I).intervalIntegrable 0 delta)
    ((continuous_const.add (excludedInformation_continuous q I)).intervalIntegrable 0 delta)
    (fun theta ht ↦ totalInformation_le q I ht.1 (ht.2.trans hd1))
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add (intervalIntegrable_const)
    ((excludedInformation_continuous q I).intervalIntegrable 0 delta),
    intervalIntegral.integral_const, integral_excludedInformation] at H
  have hF0 := entropyPotential_le q I (theta := 0) le_rfl zero_le_one
  have hFd := entropyPotential_nonneg q I hd0 hd1
  simp only [sub_zero, smul_eq_mul] at H
  nlinarith [mul_le_mul_of_nonneg_right hd1 hC]

theorem integral_posterior_averagePairInformation (A : Finset (Fin N)) :
    (∫ x, PosteriorPairProofs.averagePairInformation (posterior q A x) ∂q) =
      (∑ i : Fin N, ∑ j : Fin N, revealedPairInformation q A i j)/(N : ℝ)^2 := by
  unfold PosteriorPairProofs.averagePairInformation
  rw [integral_div]
  congr 1
  rw [integral_finsetSum Finset.univ (fun i _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ ↦ Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  exact (revealedPairInformation_eq_integral q A i j).symm

/-- The actual uniform-parameter Bernoulli reveal average of the actual
posterior pair KL obeys the finite Montanari bound. The posterior retains
the explicit probability fallback on null reveal atoms. -/
theorem finite_pinning_information_bound (hN : 0 < N) {delta : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, PosteriorPairProofs.averagePairInformation (posterior q A x) ∂q) theta
      ∂ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) delta)) ≤
        2*Real.log (Fintype.card S)/((N : ℝ)*delta) := by
  have heq (theta : ℝ) : RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, PosteriorPairProofs.averagePairInformation (posterior q A x) ∂q) theta =
      totalInformation q Finset.univ theta/(N : ℝ)^2 := by
    simp_rw [integral_posterior_averagePairInformation]
    exact average_div_const _ _ _ _
  simp_rw [heq]
  rw [integral_uniformInterval _ hd0.le, intervalIntegral.integral_div]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have H := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (integral_totalInformation_le q Finset.univ hd0.le hd1)
      (sq_nonneg (N : ℝ))) hd0.le
  simp only [Finset.card_univ, Fintype.card_fin] at H
  refine H.trans_eq ?_
  field_simp [hn.ne', hd0.ne']


end Posterior
end
end TensorPCA.BayesianPinningProofs
