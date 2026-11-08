-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- The finite Jensen entropy bound follows the proof of
-- PFR.ForMathlib.Entropy.Measure.measureEntropy_le_card_aux at immutable
-- Apache-2.0 revision https://github.com/teorth/pfr/blob/3d7898164ebff70a809dce618f9082a7b39e7850/PFR/ForMathlib/Entropy/Measure.lean
-- Here the law is already a probability on a finite alphabet, so no support
-- classes or normalized entropy of arbitrary measures are needed.
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite-law entropy and probability-valued conditioning on finite
observations, with an explicit fallback on null fibers. -/
@[expose] public section
namespace TensorPCA.FiniteEntropyProofs
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def entropy {T : Type*} [Fintype T] [MeasurableSpace T] (μ : Measure T) : ℝ :=
  ∑ t : T, Real.negMulLog (μ.real {t})

theorem entropy_nonneg {T : Type*} [Fintype T] [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] : 0 ≤ entropy μ := by
  apply Finset.sum_nonneg
  intro t _
  exact Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one

theorem entropy_le_log_card {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] :
    entropy μ ≤ Real.log (Fintype.card T) := by
  have : Nonempty T := μ.nonempty_of_neZero
  let n : ℝ := Fintype.card T
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card T)
  have hsum : (∑ t : T, μ.real {t}) = 1 := by
    simp
  calc
    entropy μ = n*∑ t : T, n⁻¹*Real.negMulLog (μ.real {t}) := by
      rw [Finset.mul_sum]
      unfold entropy
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ n*Real.negMulLog (∑ t : T, n⁻¹*μ.real {t}) := by
      apply mul_le_mul_of_nonneg_left _ hn.le
      exact Real.concaveOn_negMulLog.le_map_sum
        (by intro _ _; exact inv_nonneg.mpr hn.le) (by simp [n]) (by simp)
    _ = n*Real.negMulLog n⁻¹ := by rw [← Finset.mul_sum, hsum, mul_one]
    _ = Real.log (Fintype.card T) := by
      simp [Real.negMulLog, n]

/-- On a null observation fiber the original probability law is retained as
an explicit fallback. Its outer weighting is zero, so it never changes any
conditional average. -/
def condition {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure T) (r : T → U) (u : U) : Measure T :=
  if μ (r ⁻¹' {u}) = 0 then μ else μ[|r ← u]

theorem condition_probability {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure T) [IsProbabilityMeasure μ] (r : T → U) (u : U) :
    IsProbabilityMeasure (condition μ r u) := by
  unfold condition
  split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure h

theorem weighted_condition_eq {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure T) (r : T → U) (u : U) :
    μ (r ⁻¹' {u}) • condition μ r u = μ (r ⁻¹' {u}) • μ[|r ← u] := by
  unfold condition
  split_ifs with h
  · simp [h]
  · rfl

/-- The actual probability-valued conditional laws reconstruct the original
law, including observations whose fibers have mass zero. -/
theorem sum_weighted_condition {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [Fintype U] [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (hr : Measurable r) :
    (∑ u : U, μ (r ⁻¹' {u}) • condition μ r u) = μ := by
  simp_rw [weighted_condition_eq]
  exact sum_meas_smul_cond_fiber hr μ

def conditionalEntropy {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] (μ : Measure T) (r : T → U) : ℝ :=
  ∑ u : U, μ.real (r ⁻¹' {u})*entropy (condition μ r u)

theorem null_fiber_entropy_weight {T U : Type*} [Fintype T]
    [MeasurableSpace T] [MeasurableSpace U] (μ : Measure T) (r : T → U) (u : U)
    (hu : μ (r ⁻¹' {u}) = 0) :
    μ.real (r ⁻¹' {u})*entropy (condition μ r u) = 0 := by
  simp [measureReal_def, hu]

theorem conditionalEntropy_nonneg {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) : 0 ≤ conditionalEntropy μ r := by
  apply Finset.sum_nonneg
  intro u _
  have := condition_probability μ r u
  exact mul_nonneg measureReal_nonneg (entropy_nonneg _)

theorem conditionalEntropy_le_log_card {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (hr : Measurable r) : conditionalEntropy μ r ≤ Real.log (Fintype.card T) := by
  have hsum : (∑ u : U, μ.real (r ⁻¹' {u})) = 1 := by
    rw [sum_measureReal_preimage_singleton Finset.univ (fun u _ ↦ hr (measurableSet_singleton u))]
    simp
  calc
    _ ≤ ∑ u : U, μ.real (r ⁻¹' {u})*Real.log (Fintype.card T) := by
      apply Finset.sum_le_sum
      intro u _
      have := condition_probability μ r u
      exact mul_le_mul_of_nonneg_left (entropy_le_log_card _) measureReal_nonneg
    _ = Real.log (Fintype.card T) := by rw [← Finset.sum_mul, hsum, one_mul]

theorem weighted_condition_apply_real {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (hr : Measurable r) (u : U) (s : Set T) :
    μ.real (r ⁻¹' {u})*(condition μ r u).real s = μ.real ((r ⁻¹' {u}) ∩ s) := by
  have h := congrArg (fun ν : Measure T ↦ ν s) (weighted_condition_eq μ r u)
  simp only [Measure.smul_apply, smul_eq_mul] at h
  have hc := h.trans ((mul_comm _ _).trans (cond_mul_eq_inter (hr (measurableSet_singleton u)) s μ))
  simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal hc

theorem atom_eq_fiber_mul_condition {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (hr : Measurable r) (x : T) :
    μ.real {x} = μ.real (r ⁻¹' {r x})*(condition μ r (r x)).real {x} := by
  have h := weighted_condition_apply_real μ r hr (r x) {x}
  have hset : (r ⁻¹' {r x}) ∩ ({x} : Set T) = {x} :=
    inter_eq_right.mpr (singleton_subset_iff.mpr rfl)
  rw [hset] at h
  exact h.symm

theorem condition_singleton_eq_zero_of_ne {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSingletonClass U] (μ : Measure T) (r : T → U) (hr : Measurable r) (u : U)
    (hu : μ (r ⁻¹' {u}) ≠ 0) (x : T) (hx : r x ≠ u) : condition μ r u {x} = 0 := by
  unfold condition
  rw [ite_eq_right hu, cond_apply (hr (measurableSet_singleton u))]
  have hset : (r ⁻¹' {u}) ∩ ({x} : Set T) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hz, rfl⟩
    exact hx hz
  rw [hset, measure_empty, mul_zero]

theorem condition_fiber_real {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
    (μ : Measure T) [IsProbabilityMeasure μ] (r : T → U) (u : U)
    (hu : μ (r ⁻¹' {u}) ≠ 0) : (condition μ r u).real (r ⁻¹' {u}) = 1 := by
  unfold condition
  rw [ite_eq_right hu, measureReal_def, cond_apply_self hu (measure_ne_top _ _), ENNReal.toReal_one]

theorem condition_entropy_filter {T U : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSingletonClass U] (μ : Measure T)
    (r : T → U) (hr : Measurable r) (u : U) (hu : μ (r ⁻¹' {u}) ≠ 0) :
    (∑ x ∈ Finset.univ.filter (fun x ↦ r x = u), Real.negMulLog ((condition μ r u).real {x})) =
      entropy (condition μ r u) := by
  unfold entropy
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  have hxu : r x ≠ u := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
  rw [measureReal_def, condition_singleton_eq_zero_of_ne μ r hr u hu x hxu,
    ENNReal.toReal_zero, Real.negMulLog_zero]

theorem sum_condition_atoms_fiber {T U : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (u : U) (hu : μ (r ⁻¹' {u}) ≠ 0) :
    (∑ x ∈ Finset.univ.filter (fun x ↦ r x = u), (condition μ r u).real {x}) = 1 := by
  have := condition_probability μ r u
  rw [sum_measureReal_singleton]
  have hset : (↑(Finset.univ.filter (fun x ↦ r x = u)) : Set T) = r ⁻¹' {u} := by
    ext x
    simp
  rw [hset, condition_fiber_real μ r u hu]

/-- The exact finite entropy decomposition on one observation fiber. The
zero-mass case is proved using its zero outer weight, including the fallback. -/
theorem entropy_fiber_decomposition {T U : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (μ : Measure T) [IsProbabilityMeasure μ] (r : T → U) (hr : Measurable r) (u : U) :
    (∑ x ∈ Finset.univ.filter (fun x ↦ r x = u), Real.negMulLog (μ.real {x})) =
      Real.negMulLog (μ.real (r ⁻¹' {u}))+μ.real (r ⁻¹' {u})*entropy (condition μ r u) := by
  by_cases hu : μ (r ⁻¹' {u}) = 0
  · have hz : μ.real (r ⁻¹' {u}) = 0 := by simp [measureReal_def, hu]
    rw [hz, Real.negMulLog_zero, zero_mul, zero_add]
    apply Finset.sum_eq_zero
    intro x hx
    have hxu : r x = u := (Finset.mem_filter.mp hx).2
    have hzero : μ {x} = 0 := measure_mono_null (singleton_subset_iff.mpr hxu) hu
    simp [measureReal_def, hzero]
  have heq : (∑ x ∈ Finset.univ.filter (fun x ↦ r x = u), Real.negMulLog (μ.real {x})) =
      ∑ x ∈ Finset.univ.filter (fun x ↦ r x = u),
        ((condition μ r u).real {x}*Real.negMulLog (μ.real (r ⁻¹' {u}))+
          μ.real (r ⁻¹' {u})*Real.negMulLog ((condition μ r u).real {x})) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxu : r x = u := (Finset.mem_filter.mp hx).2
    rw [atom_eq_fiber_mul_condition μ r hr x, hxu, Real.negMulLog_mul]
  rw [heq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_condition_atoms_fiber μ r u hu, one_mul, condition_entropy_filter μ r hr u hu]

/-- Genuine finite-law conditional entropy chain rule. It is applied only
pointwise to a finite posterior, before any continuous-data integration. -/
theorem entropy_chain_rule {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (r : T → U) (hr : Measurable r) :
    entropy μ = entropy (μ.map r)+conditionalEntropy μ r := by
  calc
    entropy μ = ∑ u : U, ∑ x ∈ Finset.univ.filter (fun x ↦ r x = u),
        Real.negMulLog (μ.real {x}) := (Finset.sum_fiberwise Finset.univ r _).symm
    _ = ∑ u : U, (Real.negMulLog (μ.real (r ⁻¹' {u}))+
        μ.real (r ⁻¹' {u})*entropy (condition μ r u)) := by
      apply Finset.sum_congr rfl
      intro u _
      exact entropy_fiber_decomposition μ r hr u
    _ = entropy (μ.map r)+conditionalEntropy μ r := by
      rw [Finset.sum_add_distrib]
      congr 1
      unfold entropy
      apply Finset.sum_congr rfl
      intro u _
      simp only [measureReal_def, Measure.map_apply hr (measurableSet_singleton u)]

end
end TensorPCA.FiniteEntropyProofs
