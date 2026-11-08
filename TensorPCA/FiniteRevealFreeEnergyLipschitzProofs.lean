-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteRevealFreeEnergyProofs

/-! Insertion and reveal-rate Lipschitz bounds for Gaussian reveal free energy, including explicit null-event conditional-law towers. -/
@[expose] public section
namespace TensorPCA.FiniteRevealFreeEnergyLipschitzProofs
open MeasureTheory ProbabilityTheory Set Real FiniteEntropyProofs FiniteRevealProofs
open FiniteRevealFreeEnergyProofs GaussianRevealCostProofs
open scoped BigOperators ENNReal Classical RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ConditionalLaw
variable {Omega U V : Type*} [MeasurableSpace Omega] [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSingletonClass U] [MeasurableSingletonClass V]
  (q : Measure Omega) [IsProbabilityMeasure q]
  (r : Omega → U) (s : Omega → V) (hr : Measurable r) (hs : Measurable s)

omit [MeasurableSpace Omega] [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSingletonClass U] [MeasurableSingletonClass V] in
theorem pair_fiber_eq (u : U) (v : V) :
    (fun x ↦ (r x,s x)) ⁻¹' {(u,v)} = (r ⁻¹' {u}) ∩ (s ⁻¹' {v}) := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_inter_iff]

include hr hs

/-- On an actual positive joint fiber the explicit probability fallback is
inactive, and the two successive conditional laws equal the joint condition. -/
theorem condition_condition_eq_pair_of_ne_zero (u : U) (v : V)
    (hj : q ((r ⁻¹' {u}) ∩ (s ⁻¹' {v})) ≠ 0) :
    condition (condition q r u) s v = condition q (fun x ↦ (r x,s x)) (u,v) := by
  have hE : q (r ⁻¹' {u}) ≠ 0 := fun h ↦ hj (measure_mono_null inter_subset_left h)
  have hinner : q[s ⁻¹' {v} | r ⁻¹' {u}] ≠ 0 :=
    (cond_pos_of_inter_ne_zero (hr (measurableSet_singleton u)) hj).ne'
  have he : condition q r u = q[|r ⁻¹' {u}] := by simp only [condition, hE, ite_false]
  rw [he]
  unfold condition
  rw [ite_eq_right hinner, pair_fiber_eq r s u v, ite_eq_right hj]
  exact cond_cond_eq_cond_inter (hr (measurableSet_singleton u)) (hs (measurableSet_singleton v)) q

/-- Weighted conditional towers hold even on null fibers: their actual
outer weights are zero, and no equality of arbitrary fallback laws is used. -/
theorem weighted_condition_tower_term (Phi : Measure Omega → ℝ) (u : U) (v : V) :
    q.real (r ⁻¹' {u})*((condition q r u).real (s ⁻¹' {v})*
      Phi (condition (condition q r u) s v)) =
    q.real ((fun x ↦ (r x,s x)) ⁻¹' {(u,v)})*Phi (condition q (fun x ↦ (r x,s x)) (u,v)) := by
  have hw := weighted_condition_apply_real q r hr u (s ⁻¹' {v})
  rw [pair_fiber_eq r s u v]
  rw [← mul_assoc, hw]
  by_cases hj : q ((r ⁻¹' {u}) ∩ (s ⁻¹' {v})) = 0
  · simp only [measureReal_def, hj, ENNReal.toReal_zero, zero_mul]
  · rw [condition_condition_eq_pair_of_ne_zero q r s hr hs u v hj]

theorem weighted_condition_tower [Fintype U] [Fintype V] (Phi : Measure Omega → ℝ) :
    (∑ u : U, q.real (r ⁻¹' {u})*(∑ v : V, (condition q r u).real (s ⁻¹' {v})*
      Phi (condition (condition q r u) s v))) =
    ∑ p : U × V, q.real ((fun x ↦ (r x,s x)) ⁻¹' {p})*Phi (condition q (fun x ↦ (r x,s x)) p) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact weighted_condition_tower_term q r s hr hs Phi u v

end ConditionalLaw

theorem integral_condition_functional {Omega U : Type*} [MeasurableSpace Omega]
    [Fintype U] [MeasurableSpace U] [MeasurableSingletonClass U]
    (q : Measure Omega) [IsProbabilityMeasure q] (r : Omega → U) (hr : Measurable r)
    (Phi : Measure Omega → ℝ) :
    (∫ x, Phi (condition q r (r x)) ∂q) = ∑ u : U, q.real (r ⁻¹' {u})*Phi (condition q r u) := by
  let f : U → ℝ := fun u ↦ Phi (condition q r u)
  have H := integral_map (μ := q) hr.aemeasurable (Integrable.of_finite (f := f)).aestronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at H
  have hw (u : U) : (q.map r).real {u} = q.real (r ⁻¹' {u}) := by
    simp only [measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]
  simpa only [hw, smul_eq_mul, f] using H.symm

section Refinement
variable {Omega E U V : Type*} [MeasurableSpace Omega]
  [Fintype U] [Fintype V] [MeasurableSpace U] [MeasurableSpace V]
  [MeasurableSingletonClass U] [MeasurableSingletonClass V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Revealing one more finite observable after any finite observation costs
at most the log alphabet size, uniformly in the first observation. -/
theorem refinement_freeEnergy_cost_bounds (q : Measure Omega) [IsProbabilityMeasure q]
    (r : Omega → U) (s : Omega → V) (hr : Measurable r) (hs : Measurable s)
    (F : Omega → E) (hF : Measurable F) {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) :
    0 ≤ (∫ x, GaussianPriorTransferProofs.mixtureFreeEnergy
      (condition q (fun y ↦ (r y,s y)) (r x,s x)) F ∂q)-
      (∫ x, GaussianPriorTransferProofs.mixtureFreeEnergy (condition q r (r x)) F ∂q) ∧
    (∫ x, GaussianPriorTransferProofs.mixtureFreeEnergy
      (condition q (fun y ↦ (r y,s y)) (r x,s x)) F ∂q)-
      (∫ x, GaussianPriorTransferProofs.mixtureFreeEnergy (condition q r (r x)) F ∂q) ≤
        Real.log (Fintype.card V) := by
  let Phi : Measure Omega → ℝ := fun nu ↦ GaussianPriorTransferProofs.mixtureFreeEnergy nu F
  have hb (u : U) : 0 ≤
      (∑ v : V, (condition q r u).real (s ⁻¹' {v})*Phi (condition (condition q r u) s v))-
      Phi (condition q r u) ∧
      (∑ v : V, (condition q r u).real (s ⁻¹' {v})*Phi (condition (condition q r u) s v))-
      Phi (condition q r u) ≤ Real.log (Fintype.card V) := by
    have := condition_probability q r u
    have hB := (condition_absolutelyContinuous q r u).ae_le hFB
    have h := gaussian_reveal_freeEnergy_cost (condition q r u) s hs F hF hB
    have he := entropy_le_log_card ((condition q r u).map s)
    exact ⟨h.1,h.2.trans he⟩
  have hsum : (∑ u : U, q.real (r ⁻¹' {u})) = 1 := by
    rw [sum_measureReal_preimage_singleton Finset.univ (fun u _ ↦ hr (measurableSet_singleton u))]
    simp
  have hj := weighted_condition_tower q r s hr hs Phi
  have he :
      (∑ p : U × V, q.real ((fun x ↦ (r x,s x)) ⁻¹' {p})*Phi (condition q (fun x ↦ (r x,s x)) p))-
      (∑ u : U, q.real (r ⁻¹' {u})*Phi (condition q r u)) =
      ∑ u : U, q.real (r ⁻¹' {u})*((∑ v : V, (condition q r u).real (s ⁻¹' {v})*
        Phi (condition (condition q r u) s v))-Phi (condition q r u)) := by
    rw [← hj, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  change 0 ≤ (∫ x, Phi (condition q (fun y ↦ (r y,s y)) (r x,s x)) ∂q)-
      (∫ x, Phi (condition q r (r x)) ∂q) ∧ _
  rw [integral_condition_functional q _ (hr.prodMk hs) Phi,
    integral_condition_functional q r hr Phi, he]
  constructor
  · exact Finset.sum_nonneg (fun u _ ↦ mul_nonneg measureReal_nonneg (hb u).1)
  · calc
      _ ≤ ∑ u : U, q.real (r ⁻¹' {u})*Real.log (Fintype.card V) :=
        Finset.sum_le_sum (fun u _ ↦ mul_le_mul_of_nonneg_left (hb u).2 measureReal_nonneg)
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

end Refinement

theorem uniformInterval_integral_scale (f : ℝ → ℝ) {delta : ℝ} (hd : 0 < delta) :
    (∫ theta, f theta ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) =
    ∫ u, f (delta*u) ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) 1) := by
  rw [BayesianPinningProofs.integral_uniformInterval f hd.le,
    BayesianPinningProofs.integral_uniformInterval _ zero_le_one,
    intervalIntegral.integral_comp_mul_left f hd.ne']
  simp only [mul_zero, mul_one, inv_one, one_mul, smul_eq_mul, div_eq_mul_inv, mul_comm]

section Configuration
open PosteriorPairProofs GaussianPriorTransferProofs
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem observation_eq_iff (A : Finset (Fin N)) (x y : Configuration S N) :
    observation A x = observation A y ↔ ∀ i ∈ A, x i = y i := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [observation, hi, ite_true, Sum.inr.injEq] using he
  · intro h
    funext i
    by_cases hi : i ∈ A
    · simp only [observation, hi, ite_true, h i hi]
    · simp only [observation, hi, ite_false]

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem condition_pair_observation_eq (A : Finset (Fin N)) (i : Fin N) (x : Configuration S N) :
    condition q (fun y ↦ (observation A y,y i)) (observation A x,x i) = posterior q (insert i A) x := by
  have he : (fun y ↦ (observation A y,y i)) ⁻¹' {(observation A x,x i)} =
      observation (S := S) (insert i A) ⁻¹' {observation (insert i A) x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, observation_eq_iff,
      Finset.forall_mem_insert]
    exact and_comm
  unfold posterior condition
  rw [he]

theorem revealFreeEnergyCost_insert_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) (A : Finset (Fin N)) (i : Fin N) :
    0 ≤ revealFreeEnergyCost q F (insert i A)-revealFreeEnergyCost q F A ∧
      revealFreeEnergyCost q F (insert i A)-revealFreeEnergyCost q F A ≤ Real.log (Fintype.card S) := by
  have H := refinement_freeEnergy_cost_bounds q (observation (S := S) A) (fun x ↦ x i)
    (measurable_of_finite _) (measurable_pi_apply i) F hF hFB
  simp_rw [condition_pair_observation_eq q A i] at H
  have he : revealFreeEnergyCost q F (insert i A)-revealFreeEnergyCost q F A =
      (∫ x, mixtureFreeEnergy (posterior q (insert i A) x) F ∂q)-
        (∫ x, mixtureFreeEnergy (posterior q A x) F ∂q) := by
    unfold revealFreeEnergyCost
    ring
  rw [he]
  exact H

def insertionDerivative (F : Configuration S N → E) (theta : ℝ) : ℝ :=
  ∑ i : Fin N, RevealPolynomialProofs.average (Finset.univ.erase i)
    (fun A ↦ revealFreeEnergyCost q F (insert i A)-revealFreeEnergyCost q F A) theta

omit [Fintype S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] [BorelSpace E] in
theorem bernoulli_revealFreeEnergyCost_hasDerivAt (F : Configuration S N → E) (theta : ℝ) :
    HasDerivAt (RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F))
      (insertionDerivative q F theta) theta := by
  exact RevealPolynomialProofs.average_hasDerivAt Finset.univ (revealFreeEnergyCost q F) theta

theorem insertionDerivative_bounds (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    0 ≤ insertionDerivative q F theta ∧ insertionDerivative q F theta ≤ (N : ℝ)*Real.log (Fintype.card S) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ RevealPolynomialProofs.average_nonneg _ _ h0 h1
      (fun A _ ↦ (revealFreeEnergyCost_insert_bounds q F hF hFB A i).1))
  · calc
      _ ≤ ∑ _i : Fin N, Real.log (Fintype.card S) :=
        Finset.sum_le_sum (fun i _ ↦ RevealPolynomialProofs.average_le_const _ _ h0 h1
          (fun A _ ↦ (revealFreeEnergyCost_insert_bounds q F hF hFB A i).2))
      _ = _ := by simp

/-- Genuine Bernoulli reveal-rate Lipschitz control from the actual finite
insertion derivative. In particular it controls unnormalized cavity increments. -/
theorem bernoulli_revealFreeEnergyCost_lipschitz (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) {theta theta' : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) 1) (ht' : theta' ∈ Icc (0 : ℝ) 1) :
    |RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta-
      RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta'| ≤
        (N : ℝ)*|theta-theta'| * Real.log (Fintype.card S) := by
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F))
    (f' := insertionDerivative q F)
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ (bernoulli_revealFreeEnergyCost_hasDerivAt q F t).hasDerivWithinAt)
    (fun t ht ↦ by
      have hb := insertionDerivative_bounds q F hF hFB ht.1 ht.2
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
    (convex_Icc (0 : ℝ) 1) ht' ht
  simpa only [Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using H

/-- Coupling two actual uniform reveal parameters by the same uniform u
preserves the sharp N times rate-difference bound needed in the cavity step. -/
theorem uniform_revealFreeEnergyCost_lipschitz (F : Configuration S N → E) (hF : Measurable F)
    {K : ℝ} (hFB : ∀ᵐ x ∂q, ‖F x‖ ≤ K) {delta delta' : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hd' : 0 < delta') (hd1' : delta' ≤ 1) :
    |(∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
        ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta))-
      (∫ theta, RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) theta
        ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta'))| ≤
        (N : ℝ)*|delta-delta'| * Real.log (Fintype.card S) := by
  have := BayesianPinningProofs.uniformInterval_probability (by norm_num : (0 : ℝ) < 1)
  rw [uniformInterval_integral_scale _ hd, uniformInterval_integral_scale _ hd']
  have hC : 0 ≤ (N : ℝ)*Real.log (Fintype.card S) := by
    have hb := insertionDerivative_bounds q F hF hFB (theta := 0) le_rfl zero_le_one
    exact hb.1.trans hb.2
  have hc := RevealPolynomialProofs.average_continuous Finset.univ (revealFreeEnergyCost q F)
  have hcd : Continuous (fun u : ℝ ↦ RevealPolynomialProofs.average Finset.univ
      (revealFreeEnergyCost q F) (delta*u)) := hc.comp (continuous_const.mul continuous_id)
  have hcd' : Continuous (fun u : ℝ ↦ RevealPolynomialProofs.average Finset.univ
      (revealFreeEnergyCost q F) (delta'*u)) := hc.comp (continuous_const.mul continuous_id)
  have hi := (BayesianPinningVarianceProofs.memLp_uniformInterval
    hcd (by norm_num : (0 : ℝ) < 1) 1).integrable le_rfl
  have hi' := (BayesianPinningVarianceProofs.memLp_uniformInterval
    hcd' (by norm_num : (0 : ℝ) < 1) 1).integrable le_rfl
  rw [← integral_sub hi hi']
  have H := norm_integral_le_of_norm_le_const
    (μ := ProbabilityTheory.cond volume (Icc (0 : ℝ) 1))
    (f := fun u ↦ RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) (delta*u)-
      RevealPolynomialProofs.average Finset.univ (revealFreeEnergyCost q F) (delta'*u))
    (ae_cond_of_forall_mem measurableSet_Icc (fun u hu ↦ by
      have ht : delta*u ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hd.le hu.1,
        ((mul_le_mul_of_nonneg_left hu.2 hd.le).trans_eq (mul_one delta)).trans hd1⟩
      have ht' : delta'*u ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg hd'.le hu.1,
        ((mul_le_mul_of_nonneg_left hu.2 hd'.le).trans_eq (mul_one delta')).trans hd1'⟩
      have hs : |delta*u-delta'*u| ≤ |delta-delta'| := by
        rw [← sub_mul, abs_mul, abs_of_nonneg hu.1]
        exact (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)).trans_eq (mul_one _)
      rw [Real.norm_eq_abs]
      apply (bernoulli_revealFreeEnergyCost_lipschitz q F hF hFB ht ht').trans
      convert! mul_le_mul_of_nonneg_left hs hC using 1
      ring))
  simpa only [probReal_univ, mul_one, one_mul, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using H

end Configuration

/-- Dimension times the adjacent inverse-square-root reveal-rate difference
is at most one over the next square-root dimension. -/
theorem squareRootRevealRate_increment_le (n : ℕ) :
    ((n+1 : ℕ) : ℝ)*|1/Real.sqrt (n+2 : ℕ)-1/Real.sqrt (n+1 : ℕ)| ≤
      1/Real.sqrt (n+2 : ℕ) := by
  let a := Real.sqrt (n+1 : ℕ)
  let b := Real.sqrt (n+2 : ℕ)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (n+1))
  have hsa : a^2 = ((n+1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hsb : b^2 = ((n+1 : ℕ) : ℝ)+1 := by
    dsimp only [b]
    rw [Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hinv : 1/b ≤ 1/a := one_div_le_one_div_of_le ha hab
  change ((n+1 : ℕ) : ℝ)*|1/b-1/a| ≤ 1/b
  rw [abs_of_nonpos (sub_nonpos.mpr hinv), neg_sub]
  have he : ((n+1 : ℕ) : ℝ)*(1/a-1/b) = a*(b-a)/b := by
    rw [← hsa]
    field_simp [ha.ne',hb.ne']
  rw [he]
  apply div_le_div_of_nonneg_right _ hb.le
  have hm := mul_le_mul_of_nonneg_right hab hb.le
  nlinarith

theorem squareRootRevealRate_increment_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ ((n+1 : ℕ) : ℝ)*
      |1/Real.sqrt (n+2 : ℕ)-1/Real.sqrt (n+1 : ℕ)|) Filter.atTop (nhds 0) := by
  have hd : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)+2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n+2 : ℕ)) Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using Real.tendsto_sqrt_atTop.comp hd
  exact squeeze_zero (fun n ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    squareRootRevealRate_increment_le (hs.const_div_atTop 1)

end
end TensorPCA.FiniteRevealFreeEnergyLipschitzProofs
