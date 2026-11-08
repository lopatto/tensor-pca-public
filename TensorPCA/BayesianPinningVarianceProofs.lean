-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.BayesianPinningProofs

/-! Averaged thermal replica variance after finite pinning.
The center remains the posterior-dependent sum of squared coordinate means. -/
@[expose] public section
namespace TensorPCA.BayesianPinningVarianceProofs
open MeasureTheory ProbabilityTheory Set Real FiniteRevealProofs RevealPolynomialProofs
open BayesianPinningProofs PosteriorPairProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integral_sqrt_le_sqrt_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hs : MemLp (fun x ↦ Real.sqrt (f x)) 2 μ) :
    (∫ x, Real.sqrt (f x) ∂μ) ≤ Real.sqrt (∫ x, f x ∂μ) := by
  have hpq : Real.HolderConjugate (2 : ℝ) 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (f := fun x ↦ Real.sqrt (f x)) (g := fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall (fun x ↦ Real.sqrt_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ ↦ zero_le_one))
    (by simpa only [ENNReal.ofReal_ofNat] using hs) (memLp_const (1 : ℝ))
  have he : (∫ x, (Real.sqrt (f x))^2 ∂μ) = ∫ x, f x ∂μ :=
    integral_congr_ae (hf.mono (fun x hx ↦ Real.sq_sqrt hx))
  simpa only [mul_one, Real.rpow_two, he, Real.one_rpow, integral_const,
    probReal_univ, one_smul, ← Real.sqrt_eq_rpow, one_pow, Real.sqrt_one] using hh

theorem average_add {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f g : Finset ι → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ f A+g A) theta =
      RevealPolynomialProofs.average I f theta+RevealPolynomialProofs.average I g theta := by
  simp only [RevealPolynomialProofs.average, mul_add, Finset.sum_add_distrib]

theorem average_sub {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f g : Finset ι → ℝ) (theta : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ f A-g A) theta =
      RevealPolynomialProofs.average I f theta-RevealPolynomialProofs.average I g theta := by
  simp only [RevealPolynomialProofs.average, mul_sub, Finset.sum_sub_distrib]

theorem average_const_mul {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f : Finset ι → ℝ) (theta c : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ c*f A) theta =
      c*RevealPolynomialProofs.average I f theta := by
  unfold RevealPolynomialProofs.average
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem average_const {ι : Type*} [DecidableEq ι] (I : Finset ι) (theta c : ℝ) :
    RevealPolynomialProofs.average I (fun _ ↦ c) theta = c := by
  have H := average_const_mul I (fun _ ↦ 1) theta c
  simpa only [mul_one, average_one] using H

theorem average_mono {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f g : Finset ι → ℝ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hfg : ∀ A, f A ≤ g A) :
    RevealPolynomialProofs.average I f theta ≤ RevealPolynomialProofs.average I g theta := by
  apply Finset.sum_le_sum
  intro A _
  exact mul_le_mul_of_nonneg_left (hfg A) (weight_nonneg I A h0 h1)

theorem average_sqrt_le {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f : Finset ι → ℝ) (hf : ∀ A, 0 ≤ f A) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    RevealPolynomialProofs.average I (fun A ↦ Real.sqrt (f A)) theta ≤
      Real.sqrt (RevealPolynomialProofs.average I f theta) := by
  let m := RevealPolynomialProofs.average I (fun A ↦ Real.sqrt (f A)) theta
  have hp := average_nonneg I (fun A ↦ (Real.sqrt (f A)-m)^2) h0 h1 (fun A _ ↦ sq_nonneg _)
  have he : (fun A ↦ (Real.sqrt (f A)-m)^2) =
      (fun A ↦ (f A-(2*m)*Real.sqrt (f A))+m^2) := by
    funext A
    nlinarith [Real.sq_sqrt (hf A)]
  rw [he, average_add, average_sub, average_const_mul, average_const] at hp
  have hm : 0 ≤ RevealPolynomialProofs.average I f theta := average_nonneg I f h0 h1 (fun A _ ↦ hf A)
  change m ≤ Real.sqrt (RevealPolynomialProofs.average I f theta)
  dsimp only [m] at hp ⊢
  nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg (RevealPolynomialProofs.average I f theta)]

theorem memLp_uniformInterval {f : ℝ → ℝ} (hf : Continuous f) {delta : ℝ}
    (hd : 0 < delta) (p : ℝ≥0∞) :
    MemLp f p (ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) := by
  have := uniformInterval_probability hd
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_cond_of_forall_mem measurableSet_Icc hB

section Posterior
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem averagePairInformation_nonneg : 0 ≤ averagePairInformation q := by
  unfold averagePairInformation
  positivity

theorem latent_posterior_sqrt_information_le (A : Finset (Fin N)) :
    (∫ x, Real.sqrt (2*averagePairInformation (posterior q A x)) ∂q) ≤
      Real.sqrt (2*(∫ x, averagePairInformation (posterior q A x) ∂q)) := by
  have H := integral_sqrt_le_sqrt_integral q
    (f := fun x ↦ 2*averagePairInformation (posterior q A x))
    (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (by norm_num) (averagePairInformation_nonneg _)))
    MemLp.of_discrete
  simpa only [integral_const_mul] using H

theorem mask_posterior_sqrt_information_le {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, Real.sqrt (2*averagePairInformation (posterior q A x)) ∂q) theta ≤
    Real.sqrt (2*RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, averagePairInformation (posterior q A x) ∂q) theta) := by
  calc
    _ ≤ RevealPolynomialProofs.average Finset.univ
        (fun A ↦ Real.sqrt (2*(∫ x, averagePairInformation (posterior q A x) ∂q))) theta :=
      average_mono _ _ _ h0 h1 (latent_posterior_sqrt_information_le q)
    _ ≤ Real.sqrt (RevealPolynomialProofs.average Finset.univ
        (fun A ↦ 2*(∫ x, averagePairInformation (posterior q A x) ∂q)) theta) :=
      average_sqrt_le _ _ (fun A ↦ mul_nonneg (by norm_num)
        (integral_nonneg (fun x ↦ averagePairInformation_nonneg _))) h0 h1
    _ = _ := by rw [average_const_mul]

theorem pinned_sqrt_information_le {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, Real.sqrt (2*averagePairInformation (posterior q A x)) ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ≤
    Real.sqrt (2*(∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, averagePairInformation (posterior q A x) ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))) := by
  have := uniformInterval_probability hd0
  have hcont : Continuous (fun theta ↦ 2*RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, averagePairInformation (posterior q A x) ∂q) theta) :=
    continuous_const.mul (average_continuous _ _)
  have H := integral_mono_ae
    ((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl)
    ((memLp_uniformInterval hcont.sqrt hd0 1).integrable le_rfl)
    (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦
      mask_posterior_sqrt_information_le q ht.1 (ht.2.trans hd1)))
  refine H.trans ?_
  have hj := integral_sqrt_le_sqrt_integral
    (ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))
    (f := fun theta ↦ 2*RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, averagePairInformation (posterior q A x) ∂q) theta)
    (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ mul_nonneg (by norm_num)
      (average_nonneg _ _ ht.1 (ht.2.trans hd1)
        (fun A _ ↦ integral_nonneg (fun x ↦ averagePairInformation_nonneg _)))))
    (memLp_uniformInterval hcont.sqrt hd0 2)
  simpa only [integral_const_mul] using hj

theorem latent_posterior_variance_le (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (A : Finset (Fin N)) :
    (∫ x, replicaVariance (posterior q A x) a ∂q) ≤
      2*K^4*(∫ x, Real.sqrt (2*averagePairInformation (posterior q A x)) ∂q) := by
  have H := integral_mono_ae (μ := q) (f := fun x ↦ replicaVariance (posterior q A x) a)
    (g := fun x ↦ 2*K^4*Real.sqrt (2*averagePairInformation (posterior q A x)))
    Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall (fun x ↦ by
      have := posterior_probability q A x
      exact replicaVariance_le_pairInformation _ a hN hK hb))
  simpa only [integral_const_mul] using H

/-- Thermal variance around the actual random posterior center, averaged
over the actual latent law, Bernoulli reveals and uniform reveal parameter.
No concentration of the posterior center over external data is asserted. -/
theorem finite_pinning_replica_variance_bound (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) {delta : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, replicaVariance (posterior q A x) a ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ≤
        4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)) := by
  have := uniformInterval_probability hd0
  have H := integral_mono_ae
    ((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl)
    (((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl).const_mul (2*K^4))
    (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ by
      have hm := average_mono Finset.univ _ _ ht.1 (ht.2.trans hd1)
        (latent_posterior_variance_le q a hN hK hb)
      rwa [average_const_mul] at hm))
  rw [integral_const_mul] at H
  calc
    _ ≤ 2*K^4*(∫ theta, RevealPolynomialProofs.average Finset.univ
        (fun A ↦ ∫ x, Real.sqrt (2*averagePairInformation (posterior q A x)) ∂q) theta
        ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) := H
    _ ≤ 2*K^4*Real.sqrt (2*(∫ theta, RevealPolynomialProofs.average Finset.univ
        (fun A ↦ ∫ x, averagePairInformation (posterior q A x) ∂q) theta
        ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))) :=
      mul_le_mul_of_nonneg_left (pinned_sqrt_information_le q hd0 hd1) (by positivity)
    _ ≤ 2*K^4*Real.sqrt (2*(2*Real.log (Fintype.card S)/((N : ℝ)*delta))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (finite_pinning_information_bound q hN hd0 hd1) (by norm_num))) (by positivity)
    _ = _ := by
      rw [show 2*(2*Real.log (Fintype.card S)/((N : ℝ)*delta)) =
        4*(Real.log (Fintype.card S)/((N : ℝ)*delta)) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hs4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hs4]
      ring

end Posterior

end
end TensorPCA.BayesianPinningVarianceProofs
