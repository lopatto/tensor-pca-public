-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteEntropyProofs
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Finite positive-likelihood updates commute with finite reveals -/
@[expose] public section

namespace TensorPCA.FiniteLikelihoodUpdateProofs

open MeasureTheory ProbabilityTheory FiniteEntropyProofs
open scoped ENNReal

variable {Omega : Type*} [Fintype Omega] [MeasurableSpace Omega] [MeasurableSingletonClass Omega]

noncomputable def likelihoodUpdate (mu : Measure Omega) (w : Omega → ℝ) : Measure Omega :=
  mu.withDensity (fun x ↦ ENNReal.ofReal ((∫ x, w x ∂mu)⁻¹*w x))

theorem integral_weight_pos (mu : Measure Omega) [IsProbabilityMeasure mu]
    (w : Omega → ℝ) (hw : ∀ x, 0 < w x) : 0 < ∫ x, w x ∂mu := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (hw x).le) Integrable.of_finite]
  have hs : Function.support w = Set.univ := by
    ext x
    simp only [Function.mem_support, ne_eq, (hw x).ne', not_false_eq_true, Set.mem_univ]
  rw [hs, measure_univ]
  exact zero_lt_one

theorem likelihoodUpdate_probability (mu : Measure Omega) [IsProbabilityMeasure mu]
    (w : Omega → ℝ) (hw : ∀ x, 0 < w x) : IsProbabilityMeasure (likelihoodUpdate mu w) := by
  refine ⟨?_⟩
  rw [likelihoodUpdate, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (.of_forall fun x ↦ mul_nonneg (inv_nonneg.mpr (integral_weight_pos mu w hw).le) (hw x).le),
    integral_const_mul, inv_mul_cancel₀ (integral_weight_pos mu w hw).ne', ENNReal.ofReal_one]

omit [Fintype Omega] [MeasurableSingletonClass Omega] in
theorem likelihoodUpdate_absolutelyContinuous (mu : Measure Omega) (w : Omega → ℝ) :
    likelihoodUpdate mu w ≪ mu := withDensity_absolutelyContinuous mu _

theorem absolutelyContinuous_likelihoodUpdate (mu : Measure Omega) [IsProbabilityMeasure mu]
    (w : Omega → ℝ) (hw : ∀ x, 0 < w x) : mu ≪ likelihoodUpdate mu w := by
  apply withDensity_absolutelyContinuous'
  · exact (measurable_of_finite _).aemeasurable
  · exact .of_forall fun x ↦ (ENNReal.ofReal_pos.mpr
      (mul_pos (inv_pos.mpr (integral_weight_pos mu w hw)) (hw x))).ne'

theorem likelihoodUpdate_real_apply (mu : Measure Omega) [IsProbabilityMeasure mu]
    (w : Omega → ℝ) (hw : ∀ x, 0 < w x) (s : Set Omega) (hs : MeasurableSet s) :
    (likelihoodUpdate mu w).real s = (∫ x, w x ∂mu)⁻¹ * ∫ x in s, w x ∂mu := by
  rw [likelihoodUpdate, withDensity_real_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (.of_forall fun x ↦ mul_nonneg (inv_nonneg.mpr (integral_weight_pos mu w hw).le) (hw x).le),
    ENNReal.toReal_ofReal (integral_nonneg (fun x ↦
      mul_nonneg (inv_nonneg.mpr (integral_weight_pos mu w hw).le) (hw x).le)), integral_const_mul]

theorem likelihoodUpdate_real_singleton (mu : Measure Omega) [IsProbabilityMeasure mu]
    (w : Omega → ℝ) (hw : ∀ x, 0 < w x) (x : Omega) :
    (likelihoodUpdate mu w).real {x} = (∫ x, w x ∂mu)⁻¹ * w x * mu.real {x} := by
  rw [likelihoodUpdate_real_apply mu w hw _ (measurableSet_singleton x), integral_singleton]
  simp only [smul_eq_mul]
  ring

omit [Fintype Omega] [MeasurableSingletonClass Omega] in
theorem weighted_condition_measure {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (r : Omega → U) (hr : Measurable r) (u : U) :
    mu (r ⁻¹' {u}) • condition mu r u = mu.restrict (r ⁻¹' {u}) := by
  apply Measure.ext
  intro s hs
  have h := congrArg (fun nu : Measure Omega ↦ nu s) (weighted_condition_eq mu r u)
  simp only [Measure.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_comm, cond_mul_eq_inter (hr (measurableSet_singleton u)) s mu,
    Measure.restrict_apply hs, Set.inter_comm]

omit [Fintype Omega] [MeasurableSingletonClass Omega] in
theorem weighted_condition_integral {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (r : Omega → U) (hr : Measurable r) (u : U)
    (w : Omega → ℝ) :
    mu.real (r ⁻¹' {u}) * (∫ x, w x ∂condition mu r u) = ∫ x in r ⁻¹' {u}, w x ∂mu := by
  have h := congrArg (fun nu : Measure Omega ↦ ∫ x, w x ∂nu) (weighted_condition_measure mu r hr u)
  rw [integral_smul_measure] at h
  simpa only [measureReal_def, smul_eq_mul] using h

theorem likelihoodUpdate_fiber_evidence {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (w : Omega → ℝ) (hw : ∀ x, 0 < w x)
    (r : Omega → U) (hr : Measurable r) (u : U) :
    (∫ x, w x ∂mu) * (likelihoodUpdate mu w).real (r ⁻¹' {u}) =
      mu.real (r ⁻¹' {u}) * ∫ x, w x ∂condition mu r u := by
  rw [likelihoodUpdate_real_apply mu w hw _ (hr (measurableSet_singleton u)),
    ← mul_assoc, mul_inv_cancel₀ (integral_weight_pos mu w hw).ne', one_mul]
  exact (weighted_condition_integral mu r hr u w).symm

theorem likelihoodUpdate_condition {U : Type*} [MeasurableSpace U] [MeasurableSingletonClass U]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (w : Omega → ℝ) (hw : ∀ x, 0 < w x)
    (r : Omega → U) (hr : Measurable r) (u : U) :
    likelihoodUpdate (condition mu r u) w = condition (likelihoodUpdate mu w) r u := by
  have : IsProbabilityMeasure (condition mu r u) := condition_probability mu r u
  have : IsProbabilityMeasure (likelihoodUpdate mu w) := likelihoodUpdate_probability mu w hw
  have : IsProbabilityMeasure (likelihoodUpdate (condition mu r u) w) :=
    likelihoodUpdate_probability (condition mu r u) w hw
  have : IsProbabilityMeasure (condition (likelihoodUpdate mu w) r u) :=
    condition_probability (likelihoodUpdate mu w) r u
  have hNull : (likelihoodUpdate mu w) (r ⁻¹' {u}) = 0 ↔ mu (r ⁻¹' {u}) = 0 :=
    ⟨fun h ↦ absolutelyContinuous_likelihoodUpdate mu w hw h,
      fun h ↦ likelihoodUpdate_absolutelyContinuous mu w h⟩
  by_cases hzero : mu (r ⁻¹' {u}) = 0
  · simp only [condition, hzero, hNull.mpr hzero, ite_true]
  · have hnu : (likelihoodUpdate mu w) (r ⁻¹' {u}) ≠ 0 := fun h ↦ hzero (hNull.mp h)
    have hnuReal : (likelihoodUpdate mu w).real (r ⁻¹' {u}) ≠ 0 :=
      (ENNReal.toReal_pos hnu (measure_ne_top _ _)).ne'
    have hZ := (integral_weight_pos mu w hw).ne'
    have hZE := (integral_weight_pos (condition mu r u) w hw).ne'
    have he := likelihoodUpdate_fiber_evidence mu w hw r hr u
    have hc : (likelihoodUpdate mu w).real (r ⁻¹' {u}) * (∫ x, w x ∂condition mu r u)⁻¹ =
        (∫ x, w x ∂mu)⁻¹ * mu.real (r ⁻¹' {u}) := by
      field_simp [hZ,hZE]
      nlinarith [he]
    apply Measure.ext_of_singleton
    intro x
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (likelihoodUpdate (condition mu r u) w).real {x} =
      (condition (likelihoodUpdate mu w) r u).real {x}
    rw [likelihoodUpdate_real_singleton (condition mu r u) w hw]
    by_cases hx : r x = u
    · have hm := atom_eq_fiber_mul_condition mu r hr x
      have hn := atom_eq_fiber_mul_condition (likelihoodUpdate mu w) r hr x
      rw [hx] at hm hn
      rw [likelihoodUpdate_real_singleton mu w hw, hm] at hn
      apply mul_left_cancel₀ hnuReal
      calc
        _ = ((likelihoodUpdate mu w).real (r ⁻¹' {u}) * (∫ x, w x ∂condition mu r u)⁻¹) *
            (w x * (condition mu r u).real {x}) := by ring
        _ = ((∫ x, w x ∂mu)⁻¹ * mu.real (r ⁻¹' {u})) *
            (w x * (condition mu r u).real {x}) := by rw [hc]
        _ = (∫ x, w x ∂mu)⁻¹ * w x *
            (mu.real (r ⁻¹' {u}) * (condition mu r u).real {x}) := by ring
        _ = _ := hn
    · have hm : (condition mu r u).real {x} = 0 := by
        rw [measureReal_def, condition_singleton_eq_zero_of_ne mu r hr u hzero x hx, ENNReal.toReal_zero]
      have hn : (condition (likelihoodUpdate mu w) r u).real {x} = 0 := by
        rw [measureReal_def, condition_singleton_eq_zero_of_ne (likelihoodUpdate mu w) r hr u hnu x hx,
          ENNReal.toReal_zero]
      rw [hm,hn,mul_zero]


end TensorPCA.FiniteLikelihoodUpdateProofs
