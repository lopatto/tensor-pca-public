-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealCostProofs
public import TensorPCA.BayesianPinningVarianceProofs

/-! Gaussian free-energy cost of finite Bernoulli coordinate reveals. -/
@[expose] public section
namespace TensorPCA.FiniteRevealFreeEnergyProofs
open MeasureTheory ProbabilityTheory Set Real FiniteEntropyProofs FiniteConditionalEntropyProofs
open PosteriorPairProofs FiniteRevealProofs RevealPolynomialProofs BayesianPinningProofs
open BayesianPinningVarianceProofs GaussianPriorTransferProofs GaussianRevealCostProofs
open scoped BigOperators ENNReal Classical RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem average_congr {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (f g : Finset ι → ℝ) (theta : ℝ) (hfg : ∀ A ⊆ I, f A = g A) :
    RevealPolynomialProofs.average I f theta = RevealPolynomialProofs.average I g theta := by
  apply Finset.sum_congr rfl
  intro A hA
  rw [hfg A (Finset.mem_powerset.mp hA)]

theorem average_card {ι : Type*} [DecidableEq ι] (I : Finset ι) (theta : ℝ) :
    RevealPolynomialProofs.average I (fun A ↦ (A.card : ℝ)) theta = (I.card : ℝ)*theta := by
  induction I using Finset.induction_on with
  | empty => simp [RevealPolynomialProofs.average, weight]
  | @insert i I hi ih =>
    rw [average_insert I _ i hi, ih]
    have hc : RevealPolynomialProofs.average I (fun A ↦ ((insert i A).card : ℝ)) theta =
        RevealPolynomialProofs.average I (fun A ↦ (A.card : ℝ)+1) theta := by
      apply average_congr
      intro A hA
      have hiA : i ∉ A := fun h ↦ hi (hA h)
      rw [Finset.card_insert_of_notMem hiA, Nat.cast_add, Nat.cast_one]
    rw [hc, BayesianPinningVarianceProofs.average_add, BayesianPinningVarianceProofs.average_const,
      ih, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    ring

section Configuration
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]

/-- A revealed mask exposes only its selected coordinates, so its actual
entropy is bounded by the cardinality of the selected-coordinate alphabet. -/
theorem entropy_observation_le_card (A : Finset (Fin N)) :
    entropy (q.map (observation (S := S) A)) ≤ (A.card : ℝ)*Real.log (Fintype.card S) := by
  let r : Configuration S N → (A → S) := fun x i ↦ x i.1
  let f : (A → S) → Observation S N := fun u i ↦ if hi : i ∈ A then Sum.inr (u ⟨i,hi⟩) else Sum.inl ()
  have hr : Measurable r := measurable_of_finite _
  have hf : Measurable f := measurable_of_finite _
  have he : f ∘ r = observation (S := S) A := by
    funext x i
    simp only [Function.comp_apply, f, r, observation]
    split_ifs <;> rfl
  have hm : (q.map r).map f = q.map (observation (S := S) A) := by
    rw [Measure.map_map hf hr, he]
  have h1 := entropy_map_le (q.map r) f hf
  rw [hm] at h1
  have h2 := entropy_le_log_card (q.map r)
  have hc : Real.log (Fintype.card (A → S)) = (A.card : ℝ)*Real.log (Fintype.card S) := by
    rw [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow, Real.log_pow]
  exact h1.trans (h2.trans_eq hc)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def revealFreeEnergyCost (F : Configuration S N → E) (A : Finset (Fin N)) : ℝ :=
  (∫ x, mixtureFreeEnergy (posterior q A x) F ∂q)-mixtureFreeEnergy q F

theorem revealFreeEnergyCost_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) (A : Finset (Fin N)) :
    0 ≤ revealFreeEnergyCost q F A ∧
      revealFreeEnergyCost q F A ≤ (A.card : ℝ)*Real.log (Fintype.card S) := by
  have H := gaussian_reveal_freeEnergy_cost_integral q (observation (S := S) A)
    (measurable_of_finite _) F hF hFB
  exact ⟨H.1,H.2.trans (entropy_observation_le_card q A)⟩

theorem bernoulli_revealFreeEnergyCost_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    0 ≤ RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta ∧
      RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta ≤
        (N : ℝ)*theta*Real.log (Fintype.card S) := by
  constructor
  · exact average_nonneg _ _ h0 h1 (fun A _ ↦ (revealFreeEnergyCost_bounds q F hF hFB A).1)
  · calc
      _ ≤ RevealPolynomialProofs.average Finset.univ
          (fun A ↦ Real.log (Fintype.card S)*(A.card : ℝ)) theta := by
        apply average_mono _ _ _ h0 h1
        intro A
        simpa only [mul_comm] using (revealFreeEnergyCost_bounds q F hF hFB A).2
      _ = _ := by
        rw [BayesianPinningVarianceProofs.average_const_mul, average_card]
        simp only [Finset.card_univ, Fintype.card_fin]
        ring

/-- Actual uniform-parameter Bernoulli reveal free-energy cost. The bound
is uniform over every bounded signal map and thus over an interpolation. -/
theorem uniform_revealFreeEnergyCost_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    0 ≤ (∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ∧
    (∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ≤
        (N : ℝ)*delta*Real.log (Fintype.card S) := by
  have := uniformInterval_probability hd0
  have hC : 0 ≤ (N : ℝ)*Real.log (Fintype.card S) := by
    have hn := entropy_nonneg (q.map (observation (S := S) Finset.univ))
    have hb := entropy_observation_le_card q Finset.univ
    simpa only [Finset.card_univ, Fintype.card_fin] using hn.trans hb
  have hi := (memLp_uniformInterval (average_continuous Finset.univ (revealFreeEnergyCost q F)) hd0 1).integrable le_rfl
  constructor
  · exact integral_nonneg_of_ae (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦
      (bernoulli_revealFreeEnergyCost_bounds q F hF hFB ht.1 (ht.2.trans hd1)).1))
  · have H := integral_mono_ae hi (integrable_const ((N : ℝ)*delta*Real.log (Fintype.card S)))
      (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ by
        apply (bernoulli_revealFreeEnergyCost_bounds q F hF hFB ht.1 (ht.2.trans hd1)).2.trans
        convert! mul_le_mul_of_nonneg_left ht.2 hC using 1 <;> ring))
    simpa only [integral_const, probReal_univ, one_smul] using H

theorem normalized_uniform_revealFreeEnergyCost_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) (hN : 0 < N) {delta : ℝ}
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    0 ≤ (∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))/(N : ℝ) ∧
    (∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))/(N : ℝ) ≤ delta*Real.log (Fintype.card S) := by
  have H := uniform_revealFreeEnergyCost_bounds q F hF hFB hd0 hd1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨div_nonneg H.1 hn.le,(div_le_iff₀ hn).mpr ?_⟩
  simpa only [mul_assoc, mul_comm, mul_left_comm] using H.2

end Configuration
end
end TensorPCA.FiniteRevealFreeEnergyProofs
