-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- The variational KL proof is a narrow attributed port from
-- LatticeProb/Prob/Pinsker.lean at immutable Apache-2.0 revision
-- https://github.com/nitromannitol/Lattice-Probability/blob/a40ffead0cc9abcfc25ab00544a772d4339edf8d/LatticeProb/Prob/Pinsker.lean
-- The variational proof is retained apart from a local haveI-to-have linter
-- update; imports and namespace are specialized locally.
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-! A finite relative-entropy bound controls every bounded observable. -/
@[expose] public section
namespace TensorPCA.KLBoundProofs
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact exponential-tilt variational inequality, without a supplied
variational representation of KL. -/
theorem integral_sub_log_integral_exp_le_of_klDiv_le
    {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun x => Real.exp (f x)) ν)
    {δ : ℝ} (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) :
    (∫ x, f x ∂μ) - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ δ := by
  have hne : klDiv μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
  have := isProbabilityMeasure_tilted he
  have hnonneg := integral_llr_add_sub_measure_univ_nonneg
    (hac.trans (absolutelyContinuous_tilted he)) (integrable_llr_tilted_right hac hf hint he)
  simp only [probReal_univ, add_sub_cancel_right] at hnonneg
  rw [integral_llr_tilted_right hac hf he hint] at hnonneg
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
  rw [toReal_klDiv hac hint, ENNReal.toReal_ofReal hδ] at hle
  simp only [probReal_univ, add_sub_cancel_right] at hle
  linarith

/-- Hoeffding's centered log-MGF bound and KL give a quadratic bound at every
real tilt. All integrability follows from the observable bound. -/
theorem bounded_integral_tilt_le {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : Ω → ℝ) (hf : Measurable f)
    {B δ : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) (t : ℝ) :
    t*((∫ x, f x ∂μ)-(∫ x, f x ∂ν)) ≤ δ+B^2*t^2/2 := by
  have hab (x : Ω) : f x ∈ Set.Icc (-B) B := abs_le.mp (hb x)
  have hi : Integrable f μ := Integrable.of_mem_Icc (-B) B hf.aemeasurable
    (Filter.Eventually.of_forall hab)
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := ν) hf.aemeasurable
    (Filter.Eventually.of_forall hab)
  have hv := integral_sub_log_integral_exp_le_of_klDiv_le
    ((hi.sub (integrable_const (∫ x, f x ∂ν))).const_mul t)
    (hsg.integrable_exp_mul t) hδ hkl
  have hm : (∫ x, t*(f x-(∫ x, f x ∂ν)) ∂μ) =
      t*((∫ x, f x ∂μ)-(∫ x, f x ∂ν)) := by
    rw [integral_const_mul, integral_sub hi (integrable_const _),
      integral_const, probReal_univ, one_smul]
  simp only [Pi.sub_apply] at hv
  rw [hm] at hv
  have hc := hsg.cgf_le t
  have hproxy : (((‖B-(-B)‖₊/2)^2 : ℝ≥0) : ℝ) = B^2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (add_nonneg hB hB)]
    ring
  rw [hproxy] at hc
  change Real.log (∫ x, Real.exp (t*(f x-(∫ x, f x ∂ν))) ∂ν) ≤ B^2*t^2/2 at hc
  linarith

theorem bounded_integral_sub_sq_le_of_klDiv_le {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) {B δ : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) :
    ((∫ x, f x ∂μ)-(∫ x, f x ∂ν))^2 ≤ 2*B^2*δ := by
  by_cases hzero : B = 0
  · have hfzero : f = fun _ ↦ 0 := by
      funext x
      exact abs_eq_zero.mp (le_antisymm (hzero ▸ hb x) (abs_nonneg _))
    simp [hfzero, hzero]
  have hpos : 0 < B^2 := sq_pos_of_ne_zero hzero
  let d := (∫ x, f x ∂μ)-(∫ x, f x ∂ν)
  have hh := bounded_integral_tilt_le f hf hB hb hδ hkl (d/B^2)
  change d/B^2*d ≤ δ+B^2*(d/B^2)^2/2 at hh
  have hm := mul_le_mul_of_nonneg_left hh (le_of_lt (mul_pos (by norm_num : (0 : ℝ)<2) hpos))
  field_simp [hzero] at hm
  nlinarith [sq_nonneg d]

/-- Bounded-observable Pinsker, with no finite-alphabet cardinality factor. -/
theorem abs_integral_sub_integral_le_of_klDiv_le {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) {B δ : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) :
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)| ≤ B*Real.sqrt (2*δ) := by
  have hh := bounded_integral_sub_sq_le_of_klDiv_le f hf hB hb hδ hkl
  have hs : (B*Real.sqrt (2*δ))^2 = 2*B^2*δ := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hn : 0 ≤ B*Real.sqrt (2*δ) := mul_nonneg hB (Real.sqrt_nonneg _)
  nlinarith [sq_abs ((∫ x, f x ∂μ)-(∫ x, f x ∂ν))]

end
end TensorPCA.KLBoundProofs
