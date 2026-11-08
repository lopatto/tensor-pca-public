-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianFinitePriorApproximationScalarProofs
public import TensorPCA.GaussianRevealCostProofs
public import TensorPCA.RevealPolynomialProofs

/-! # Scalar and revealed-last-coordinate cavity endpoints -/
@[expose] public section

namespace TensorPCA.FinitePriorCavityScalarEndpointProofs

open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianTwoChannelFreeEnergyProofs
open GaussianFinitePriorApproximationScalarProofs GaussianRevealCostProofs FiniteEntropyProofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega S E : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A signal depending only on the fresh coordinate has precisely the fresh
prior's channel free energy, even when the background prior is arbitrary. -/
theorem mixtureFreeEnergy_prod_snd (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (F : S → E) (hF : Measurable F) :
    mixtureFreeEnergy (q.prod p) (fun z ↦ F z.2) = mixtureFreeEnergy p F := by
  have h := mixtureFreeEnergy_map_prior (q.prod p) Prod.snd measurable_snd F hF
  simpa only [Measure.map_snd_prod, measure_univ, one_smul, Function.comp_def] using h.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mixtureLikelihood_const (q : Measure Omega) [IsProbabilityMeasure q] (v y : E) :
    mixtureLikelihood q (fun _ ↦ v) y = mixtureWeight v y := by
  simp only [mixtureLikelihood, integral_const, probReal_univ, one_smul]

/-- The constant-signal likelihood retains its quadratic penalty, giving the
actual Gaussian shift relative entropy. -/
theorem mixtureFreeEnergy_const (q : Measure Omega) [IsProbabilityMeasure q] (v : E) :
    mixtureFreeEnergy q (fun _ ↦ v) = ‖v‖^2/2 := by
  rw [mixtureFreeEnergy_eq_integral_experiment q _ measurable_const]
  simp_rw [mixtureLikelihood_const]
  rw [integral_fun_snd (fun w ↦ Real.log (mixtureWeight v (v+w)))]
  simp only [probReal_univ, one_smul]
  have he (w : E) : Real.log (mixtureWeight v (v+w)) = ‖v‖^2/2+inner ℝ v w := by
    rw [mixtureWeight, Real.log_exp, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  simp_rw [he]
  have hi : Integrable (fun w : E ↦ inner ℝ v w) (stdGaussian E) :=
    (innerSL ℝ v).integrable_comp IsGaussian.integrable_id
  have hz := integral_strongDual_stdGaussian (innerSL ℝ v)
  change (∫ w : E, inner ℝ v w ∂stdGaussian E) = 0 at hz
  rw [integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul, hz, add_zero]

theorem mixtureFreeEnergy_dirac [MeasurableSingletonClass S] (s : S) (F : S → E) (hF : Measurable F) :
    mixtureFreeEnergy (Measure.dirac s) F = ‖F s‖^2/2 := by
  have h := mixtureFreeEnergy_map_prior (Measure.dirac ()) (fun _ : Unit ↦ s) measurable_const F hF
  simp only [Measure.map_dirac, Function.comp_def] at h
  exact h.trans (mixtureFreeEnergy_const (Measure.dirac ()) (F s))

section Finite

variable [Fintype S] [MeasurableSingletonClass S]

theorem condition_id_eq_dirac (p : Measure S) [IsProbabilityMeasure p] (s : S) (hs : p {s} ≠ 0) :
    condition p id s = Measure.dirac s := by
  apply Measure.ext_of_singleton
  intro t
  unfold condition
  rw [ite_eq_right (by simpa only [Set.preimage_id] using hs)]
  change p[{t} | {s}] = (Measure.dirac s) {t}
  rw [cond_apply (measurableSet_singleton s)]
  by_cases ht : t = s
  · subst t
    simp [ENNReal.inv_mul_cancel hs (measure_ne_top _ _)]
  · have hst : ({s} : Set S) ∩ {t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact ht ((Set.mem_singleton_iff.mp hx.2).symm.trans (Set.mem_singleton_iff.mp hx.1))
    simp [hst, Ne.symm ht]

/-- An actual completely revealed fresh symbol has a channel free-energy
gain between zero and the finite prior entropy, including zero-probability symbols. -/
theorem full_scalar_reveal_cost_bounds (p : Measure S) [IsProbabilityMeasure p]
    (F : S → E) :
    0 ≤ (∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p)-mixtureFreeEnergy p F ∧
    (∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p)-mixtureFreeEnergy p F ≤ Real.log (Fintype.card S) := by
  obtain ⟨K,_,hK⟩ := FinitePriorChannelProofs.finite_signal_bound F
  have h := gaussian_reveal_freeEnergy_cost_integral p id measurable_id F (measurable_of_finite _)
    (.of_forall hK)
  have heq : (∫ s, mixtureFreeEnergy (condition p id s) F ∂p) =
      ∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p := by
    apply integral_congr_ae
    have hn : ∀ᵐ s ∂p, p {s} ≠ 0 := ae_iff_of_countable.mpr (fun s hs ↦ hs)
    filter_upwards [hn] with s hs
    rw [condition_id_eq_dirac p s hs]
  change 0 ≤ (∫ s, mixtureFreeEnergy (condition p id s) F ∂p)-mixtureFreeEnergy p F ∧
    (∫ s, mixtureFreeEnergy (condition p id s) F ∂p)-mixtureFreeEnergy p F ≤ entropy (p.map id) at h
  rw [heq, Measure.map_id] at h
  exact ⟨h.1,h.2.trans (entropy_le_log_card p)⟩

/-- Fixed-coefficient actual Bernoulli reveal cost of the fresh coordinate.
The coefficient may later be supplied by the independent background experiment. -/
theorem lastReveal_freeEnergy_cost_bounds (p : Measure S) [IsProbabilityMeasure p]
    (F : S → E) {theta : ℝ} (ht0 : 0 ≤ theta) (_ht1 : theta ≤ 1) :
    0 ≤ (1-theta)*mixtureFreeEnergy p F+
      theta*(∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p)-mixtureFreeEnergy p F ∧
    (1-theta)*mixtureFreeEnergy p F+
      theta*(∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p)-mixtureFreeEnergy p F ≤
        theta*Real.log (Fintype.card S) := by
  have h := full_scalar_reveal_cost_bounds p F
  constructor
  · nlinarith [mul_nonneg ht0 h.1]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 ht0]

theorem lastReveal_scalar_freeEnergy_cost_bounds (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (c : ℝ) {theta : ℝ} (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ (1-theta)*mixtureFreeEnergy p (fun s ↦ Real.sqrt c*a s)+
      theta*(∫ s, mixtureFreeEnergy (Measure.dirac s) (fun x ↦ Real.sqrt c*a x) ∂p)-
        mixtureFreeEnergy p (fun s ↦ Real.sqrt c*a s) ∧
    (1-theta)*mixtureFreeEnergy p (fun s ↦ Real.sqrt c*a s)+
      theta*(∫ s, mixtureFreeEnergy (Measure.dirac s) (fun x ↦ Real.sqrt c*a x) ∂p)-
        mixtureFreeEnergy p (fun s ↦ Real.sqrt c*a s) ≤ theta*Real.log (Fintype.card S) :=
  lastReveal_freeEnergy_cost_bounds p _ ht0 ht1

theorem scalar_product_endpoint (q : Measure Omega) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (c : ℝ) :
    mixtureFreeEnergy (q.prod p) (fun z ↦ Real.sqrt c*a z.2) =
      mixtureFreeEnergy p (fun s ↦ Real.sqrt c*a s) :=
  mixtureFreeEnergy_prod_snd (E := ℝ) q p (fun s ↦ Real.sqrt c*a s) (measurable_of_finite _)

omit [BorelSpace E] [Fintype S] [MeasurableSingletonClass S] in
/-- The literal one-coordinate reveal polynomial averages the actual
unrevealed prior and the Dirac prior of the planted fresh symbol. -/
theorem singleton_reveal_average_eq (p : Measure S) [IsProbabilityMeasure p] (F : S → E) (theta : ℝ) :
    RevealPolynomialProofs.average ({()} : Finset Unit)
      (fun mask ↦ ∫ s, mixtureFreeEnergy (if () ∈ mask then Measure.dirac s else p) F ∂p) theta =
      (1-theta)*mixtureFreeEnergy p F+theta*(∫ s, mixtureFreeEnergy (Measure.dirac s) F ∂p) := by
  rw [show ({()} : Finset Unit) = insert () ∅ from rfl,
    RevealPolynomialProofs.average_insert ∅ _ () (Finset.notMem_empty _)]
  simp [RevealPolynomialProofs.average, RevealPolynomialProofs.weight]

theorem singleton_reveal_cost_bounds (p : Measure S) [IsProbabilityMeasure p]
    (F : S → E) {theta : ℝ} (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ RevealPolynomialProofs.average ({()} : Finset Unit)
      (fun mask ↦ ∫ s, mixtureFreeEnergy (if () ∈ mask then Measure.dirac s else p) F ∂p) theta-
        mixtureFreeEnergy p F ∧
    RevealPolynomialProofs.average ({()} : Finset Unit)
      (fun mask ↦ ∫ s, mixtureFreeEnergy (if () ∈ mask then Measure.dirac s else p) F ∂p) theta-
        mixtureFreeEnergy p F ≤ theta*Real.log (Fintype.card S) := by
  rw [singleton_reveal_average_eq]
  exact lastReveal_freeEnergy_cost_bounds p F ht0 ht1

end Finite


end TensorPCA.FinitePriorCavityScalarEndpointProofs
