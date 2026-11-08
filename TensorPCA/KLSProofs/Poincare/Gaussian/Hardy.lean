-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed KLS proof port. Original Apache-2.0 source:
https://github.com/human-ai-mathematics/kls-lean/blob/33fff6ea218ae07e42115bd1eacfcf7d39c534cb/formalization/FunctionalInequalities/Poincare/Gaussian/Hardy.lean
The source proof bodies and definitions are retained. The module/namespace
prefix FunctionalInequalities is changed to TensorPCA.KLSProofs, with imports
redirected to this exact local closure. See the repository LICENSE. -/
module

public import TensorPCA.KLSProofs.Poincare.SmoothTest.Basic
public import TensorPCA.KLSProofs.Poincare.Gaussian.Density
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Analytic upper bound for the one-dimensional Gaussian Poincaré inequality

This module isolates the direct density/Hardy argument used by
`Poincare.SmoothTest.holds_gaussianReal`. It contains the finite-interval FTC--Cauchy estimate,
variance minimization, density-weighted integrability bridges, the two nonnegative Tonelli
identities, the half-line bounds, and their full-line anchored consequence.

For positive variance `v`, the two Gaussian first-moment tails contribute exactly
`v * gaussianPDFReal m v`; adding the two half-line estimates therefore preserves the sharp
factor `v`. The proof requires no global Lebesgue L² hypothesis on the derivative and no decay
assumption on the test function.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TensorPCA.KLSProofs.Poincare.SmoothTest

/-- Source: local finite-interval helper for the density proof, using
`intervalIntegral.integral_deriv_of_contDiffOn_Icc` and integral Cauchy–Schwarz (the exponent-two
case of `integral_mul_le_Lp_mul_Lq_of_nonneg`). Global C¹ regularity supplies all required
integrability on `[a, b]`; global Lebesgue integrability of the derivative is not required. -/
theorem interval_sq_sub_le_integral_sq_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ t in a..b, (deriv f t) ^ 2 := by
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hftc : ∫ t in a..b, deriv f t = f b - f a :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hf.contDiffOn hab
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hone_mem : MemLp (fun _ : ℝ ↦ (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioc a b)) := memLp_const 1
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcont.continuousOn
  have habs_mem : MemLp (fun t ↦ |deriv f t|) (ENNReal.ofReal 2)
      (volume.restrict (Set.Ioc a b)) := by
    refine MemLp.of_bound hcont.abs.aestronglyMeasurable.restrict C ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx ↦ ?_)
    simpa [Real.norm_eq_abs, abs_abs] using hC x (Set.Ioc_subset_Icc_self hx)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (deriv f x)) hone_mem habs_mem
  have h1 : (∫ x in Set.Ioc a b, (1 : ℝ) * |deriv f x|) = ∫ t in a..b, |deriv f t| := by
    rw [intervalIntegral.integral_of_le hab]
    simp only [one_mul]
  have h2 : (∫ _x in Set.Ioc a b, (1 : ℝ) ^ (2 : ℝ)) = b - a := by
    rw [integral_const]
    simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab)]
  have h3 : (∫ x in Set.Ioc a b, |deriv f x| ^ (2 : ℝ)) =
      ∫ x in Set.Ioc a b, (deriv f x) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    show |deriv f x| ^ (2 : ℝ) = (deriv f x) ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [h1, h2, h3] at hHolder
  have habs_int : |f b - f a| ≤ ∫ t in a..b, |deriv f t| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have hA_nonneg : (0 : ℝ) ≤ ∫ x in Set.Ioc a b, (deriv f x) ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hbase_nonneg : (0 : ℝ) ≤
      (b - a) ^ (1 / 2 : ℝ) * (∫ x in Set.Ioc a b, (deriv f x) ^ 2) ^ (1 / 2 : ℝ) := by
    have hba : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
    positivity
  calc (f b - f a) ^ 2 = |f b - f a| ^ 2 := (sq_abs _).symm
    _ ≤ ((b - a) ^ (1 / 2 : ℝ) * (∫ x in Set.Ioc a b, (deriv f x) ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        exact habs_int.trans hHolder
    _ = (b - a) * ∫ x in Set.Ioc a b, (deriv f x) ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast ((b - a) ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_natCast ((∫ x in Set.Ioc a b, (deriv f x) ^ 2) ^ (1 / 2 : ℝ)) 2,
          ← Real.rpow_mul (sub_nonneg.2 hab), ← Real.rpow_mul hA_nonneg]
        norm_num
    _ = (b - a) * ∫ t in a..b, (deriv f t) ^ 2 := by
        rw [intervalIntegral.integral_of_le hab]

/-- Source: local variance-minimization helper from Mathlib's `variance_sub_const` and
`variance_le_expectation_sq`. `Admissible.memLp_two` and probability normalization ensure that
the squared integral is finite. The anchor `c` need not be the expectation of `f`. -/
theorem Admissible.variance_le_integral_sq_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Admissible μ f) (c : ℝ) :
    variance f μ ≤ ∫ x, (f x - c) ^ 2 ∂μ := by
  have hmeas : AEStronglyMeasurable f μ := hf.memLp_two.aestronglyMeasurable
  have hvar : variance (fun x ↦ f x - c) μ = variance f μ := variance_sub_const hmeas c
  have hle := variance_le_expectation_sq (μ := μ) (X := fun x ↦ f x - c)
    (hmeas.sub aestronglyMeasurable_const)
  rw [hvar] at hle
  simpa using hle

/-- Source: local integrability obligation for the density route, using
`Admissible.memLp_two`, Gaussian probability normalization, and `integrable_gaussianReal_iff`.
The positive-variance premise is required for passage to a Lebesgue density. -/
theorem Admissible.integrable_gaussianPDFReal_mul_sq_sub {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (f x - c) ^ 2) volume := by
  have hmem : MemLp (fun x ↦ f x - c) 2 (gaussianReal m v) :=
    hf.memLp_two.sub (memLp_const c)
  exact (integrable_gaussianReal_iff m hv _).mp hmem.integrable_sq

/-- Source: local integrability obligation from `Admissible.energy_integrable`, Mathlib's
`gradient_eq_deriv'`, and `integrable_gaussianReal_iff`. This is Gaussian-weighted finite energy;
it does not assert that the derivative is globally in L² of Lebesgue measure. -/
theorem Admissible.integrable_gaussianPDFReal_mul_sq_deriv {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (deriv f x) ^ 2) volume := by
  have henergy : Integrable (fun x ↦ (deriv f x) ^ 2) (gaussianReal m v) := by
    refine hf.energy_integrable.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    show ‖gradient f x‖ ^ 2 = (deriv f x) ^ 2
    rw [gradient_eq_deriv', Real.norm_eq_abs, sq_abs]
  exact (integrable_gaussianReal_iff m hv _).mp henergy

/-- Source: local nonnegative Tonelli helper, using Mathlib's `lintegral_lintegral_swap` and
`integral_Ioi_centered_gaussianPDFReal`. It integrates the region `m < t < x`. No finite-integral
hypothesis is imposed on `g`; both sides are extended nonnegative integrals. -/
theorem lintegral_gaussian_right_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0) (g : ℝ → ENNReal)
    (hg : Measurable g) :
    (∫⁻ x in Set.Ioi m, ENNReal.ofReal (x - m) * gaussianPDF m v x * ∫⁻ t in Set.Ioo m x, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Ioi m, gaussianPDF m v t * g t := by
  set F : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (x - m) * gaussianPDF m v x with hF
  have hF_meas : Measurable F :=
    ((measurable_id.sub_const m).ennreal_ofReal).mul (measurable_gaussianPDF m v)
  have hF_ne_top : ∀ x, F x ≠ ⊤ := fun x ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top gaussianPDF_lt_top.ne
  set s : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 < p.1} with hs
  have hs_meas : MeasurableSet s := measurableSet_lt measurable_snd measurable_fst
  set K : ℝ × ℝ → ENNReal := fun p ↦ F p.1 * s.indicator (fun q ↦ g q.2) p with hK
  have hK_meas : Measurable K :=
    (hF_meas.comp measurable_fst).mul ((hg.comp measurable_snd).indicator hs_meas)
  have step1 :
    (∫⁻ x in Set.Ioi m, F x * ∫⁻ t in Set.Ioo m x, g t) =
      ∫⁻ x in Set.Ioi m, ∫⁻ t in Set.Ioi m, K (x, t) := by
    refine lintegral_congr fun x ↦ ?_
    have h1 : ∀ t : ℝ, K (x, t) = F x * (Set.Iio x).indicator g t := by
      intro t
      by_cases hxt : t < x <;> simp [hK, hs, Set.indicator_apply, hxt]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ (hF_ne_top x)]
    congr 1
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_comm, Set.Ioi_inter_Iio]
  have step2 :
    (∫⁻ x in Set.Ioi m, ∫⁻ t in Set.Ioi m, K (x, t)) =
      ∫⁻ t in Set.Ioi m, ∫⁻ x in Set.Ioi m, K (x, t) :=
    lintegral_lintegral_swap hK_meas.aemeasurable
  have hEval : ∀ t ∈ Set.Ioi m, (∫⁻ x in Set.Ioi t, F x) = (v : ENNReal) * gaussianPDF m v t := by
    intro t ht
    have hmt : m < t := ht
    have h1 :
      Set.EqOn F (fun x ↦ ENNReal.ofReal ((x - m) * gaussianPDFReal m v x)) (Set.Ioi t) := by
      intro x hx
      have hxt : t < x := hx
      simp only [hF, gaussianPDF]
      rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ x - m)]
    rw [setLIntegral_congr_fun measurableSet_Ioi h1, ←
      ofReal_integral_eq_lintegral_ofReal
        (integrable_centered_gaussianPDFReal m hv).integrableOn
        ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall fun x hx ↦
            mul_nonneg (by linarith [Set.mem_Ioi.mp hx] : (0 : ℝ) ≤ x - m)
              (gaussianPDFReal_nonneg m v x))),
      integral_Ioi_centered_gaussianPDFReal m hv t, ENNReal.ofReal_mul v.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, gaussianPDF]
  have step3 :
    (∫⁻ t in Set.Ioi m, ∫⁻ x in Set.Ioi m, K (x, t)) =
      ∫⁻ t in Set.Ioi m, (v : ENNReal) * gaussianPDF m v t * g t := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have hmt : m < t := ht
    have h1 : ∀ x : ℝ, K (x, t) = (Set.Ioi t).indicator (fun x ↦ F x * g t) x := by
      intro x
      by_cases hxt : t < x <;> simp [hK, hs, Set.indicator_apply, hxt]
    simp_rw [h1]
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hmt.le), lintegral_mul_const _ hF_meas,
      hEval t ht]
  calc
    (∫⁻ x in Set.Ioi m, F x * ∫⁻ t in Set.Ioo m x, g t) =
        ∫⁻ x in Set.Ioi m, ∫⁻ t in Set.Ioi m, K (x, t) :=
      step1
    _ = ∫⁻ t in Set.Ioi m, ∫⁻ x in Set.Ioi m, K (x, t) := step2
    _ = ∫⁻ t in Set.Ioi m, (v : ENNReal) * gaussianPDF m v t * g t := step3
    _ = (v : ENNReal) * ∫⁻ t in Set.Ioi m, gaussianPDF m v t * g t := by
      simp_rw [mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- Source: local nonnegative Tonelli helper, using Mathlib's `lintegral_lintegral_swap` and
`integral_Iio_centered_gaussianPDFReal`. It integrates the region `x < t < m`. The reversed
orientation changes the nonnegative length factor to `m - x`; no integrability of `g` is assumed. -/
theorem lintegral_gaussian_left_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0) (g : ℝ → ENNReal)
    (hg : Measurable g) :
    (∫⁻ x in Set.Iio m, ENNReal.ofReal (m - x) * gaussianPDF m v x * ∫⁻ t in Set.Ioo x m, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Iio m, gaussianPDF m v t * g t := by
  set F : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (m - x) * gaussianPDF m v x with hF
  have hF_meas : Measurable F :=
    ((measurable_const.sub measurable_id).ennreal_ofReal).mul (measurable_gaussianPDF m v)
  have hF_ne_top : ∀ x, F x ≠ ⊤ := fun x ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top gaussianPDF_lt_top.ne
  set s : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < p.2} with hs
  have hs_meas : MeasurableSet s := measurableSet_lt measurable_fst measurable_snd
  set K : ℝ × ℝ → ENNReal := fun p ↦ F p.1 * s.indicator (fun q ↦ g q.2) p with hK
  have hK_meas : Measurable K :=
    (hF_meas.comp measurable_fst).mul ((hg.comp measurable_snd).indicator hs_meas)
  have step1 :
    (∫⁻ x in Set.Iio m, F x * ∫⁻ t in Set.Ioo x m, g t) =
      ∫⁻ x in Set.Iio m, ∫⁻ t in Set.Iio m, K (x, t) := by
    refine lintegral_congr fun x ↦ ?_
    have h1 : ∀ t : ℝ, K (x, t) = F x * (Set.Ioi x).indicator g t := by
      intro t
      by_cases hxt : x < t <;> simp [hK, hs, Set.indicator_apply, hxt]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ (hF_ne_top x)]
    congr 1
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Set.Ioi_inter_Iio]
  have step2 :
    (∫⁻ x in Set.Iio m, ∫⁻ t in Set.Iio m, K (x, t)) =
      ∫⁻ t in Set.Iio m, ∫⁻ x in Set.Iio m, K (x, t) :=
    lintegral_lintegral_swap hK_meas.aemeasurable
  have hEval : ∀ t ∈ Set.Iio m, (∫⁻ x in Set.Iio t, F x) = (v : ENNReal) * gaussianPDF m v t := by
    intro t ht
    have hmt : t < m := ht
    have h1 :
      Set.EqOn F (fun x ↦ ENNReal.ofReal ((m - x) * gaussianPDFReal m v x)) (Set.Iio t) := by
      intro x hx
      have hxt : x < t := hx
      simp only [hF, gaussianPDF]
      rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ m - x)]
    have hint : Integrable (fun x ↦ (m - x) * gaussianPDFReal m v x) volume := by
      refine
        (integrable_centered_gaussianPDFReal m hv).neg.congr
          (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.neg_apply]
      ring
    rw [setLIntegral_congr_fun measurableSet_Iio h1, ←
      ofReal_integral_eq_lintegral_ofReal hint.integrableOn
        ((ae_restrict_iff' measurableSet_Iio).2
          (Filter.Eventually.of_forall fun x hx ↦
            mul_nonneg (by linarith [Set.mem_Iio.mp hx] : (0 : ℝ) ≤ m - x)
              (gaussianPDFReal_nonneg m v x))),
      integral_Iio_centered_gaussianPDFReal m hv t, ENNReal.ofReal_mul v.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, gaussianPDF]
  have step3 :
    (∫⁻ t in Set.Iio m, ∫⁻ x in Set.Iio m, K (x, t)) =
      ∫⁻ t in Set.Iio m, (v : ENNReal) * gaussianPDF m v t * g t := by
    refine setLIntegral_congr_fun measurableSet_Iio fun t ht ↦ ?_
    have hmt : t < m := ht
    have h1 : ∀ x : ℝ, K (x, t) = (Set.Iio t).indicator (fun x ↦ F x * g t) x := by
      intro x
      by_cases hxt : x < t <;> simp [hK, hs, Set.indicator_apply, hxt]
    simp_rw [h1]
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      Set.inter_eq_left.mpr (Set.Iio_subset_Iio hmt.le), lintegral_mul_const _ hF_meas,
      hEval t ht]
  calc
    (∫⁻ x in Set.Iio m, F x * ∫⁻ t in Set.Ioo x m, g t) =
        ∫⁻ x in Set.Iio m, ∫⁻ t in Set.Iio m, K (x, t) :=
      step1
    _ = ∫⁻ t in Set.Iio m, ∫⁻ x in Set.Iio m, K (x, t) := step2
    _ = ∫⁻ t in Set.Iio m, (v : ENNReal) * gaussianPDF m v t * g t := step3
    _ = (v : ENNReal) * ∫⁻ t in Set.Iio m, gaussianPDF m v t * g t := by
      simp_rw [mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- Source: local right-half-line estimate in the direct proof of the manuscript's Gaussian
Poincaré upper bound. Combine `interval_sq_sub_le_integral_sq_deriv`,
`lintegral_gaussian_right_triangle`, and the two admissible weighted-integrability helpers.
The right-hand side retains only the energy on the same half-line, preserving the sharp factor. -/
theorem Admissible.integral_Ioi_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2 := by
  have hC1 : ContDiff ℝ 1 f := hf.smooth'.of_le (by simp)
  have hcont : Continuous (deriv f) := hC1.continuous_deriv le_rfl
  have hint_sub : IntegrableOn (fun x ↦ gaussianPDFReal m v x * (f x - f m) ^ 2)
      (Set.Ioi m) := (hf.integrable_gaussianPDFReal_mul_sq_sub hv (f m)).integrableOn
  have hint_deriv : IntegrableOn (fun x ↦ gaussianPDFReal m v x * (deriv f x) ^ 2)
      (Set.Ioi m) := (hf.integrable_gaussianPDFReal_mul_sq_deriv hv).integrableOn
  have hg_meas : Measurable fun t ↦ ENNReal.ofReal ((deriv f t) ^ 2) :=
    (hcont.measurable.pow_const 2).ennreal_ofReal
  have hpoint : ∀ x ∈ Set.Ioi m,
      ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
        ENNReal.ofReal (x - m) * gaussianPDF m v x *
          ∫⁻ t in Set.Ioo m x, ENNReal.ofReal ((deriv f t) ^ 2) := by
    intro x hx
    have hmx : m < x := hx
    have hival := interval_sq_sub_le_integral_sq_deriv f hC1 m x hmx.le
    have h1 : gaussianPDFReal m v x * (f x - f m) ^ 2 ≤
        gaussianPDFReal m v x * ((x - m) * ∫ t in m..x, (deriv f t) ^ 2) :=
      mul_le_mul_of_nonneg_left hival (gaussianPDFReal_nonneg m v x)
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    have hIocInt : IntegrableOn (fun t ↦ (deriv f t) ^ 2) (Set.Ioc m x) :=
      (hcont.pow 2).integrableOn_Ioc
    have hofReal : ENNReal.ofReal (∫ t in Set.Ioc m x, (deriv f t) ^ 2) =
        ∫⁻ t in Set.Ioc m x, ENNReal.ofReal ((deriv f t) ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hIocInt
        (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    have hIooIoc : (∫⁻ t in Set.Ioo m x, ENNReal.ofReal ((deriv f t) ^ 2)) =
        ∫⁻ t in Set.Ioc m x, ENNReal.ofReal ((deriv f t) ^ 2) :=
      setLIntegral_congr (Ioo_ae_eq_Ioc' (measure_singleton x))
    rw [intervalIntegral.integral_of_le hmx.le,
      ENNReal.ofReal_mul (gaussianPDFReal_nonneg m v x),
      ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ x - m), hofReal, ← hIooIoc, gaussianPDF]
    ring
  have hlhs : ENNReal.ofReal (∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2) =
      ∫⁻ x in Set.Ioi m, ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2) :=
    ofReal_integral_eq_lintegral_ofReal hint_sub
      (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))
  have hrhs : ENNReal.ofReal (∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2) =
      ∫⁻ x in Set.Ioi m, gaussianPDF m v x * ENNReal.ofReal ((deriv f x) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_deriv
      (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg m v x), gaussianPDF]
  have hmain : ENNReal.ofReal (∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      ENNReal.ofReal ((v : ℝ) * ∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2) := by
    rw [ENNReal.ofReal_mul v.coe_nonneg, ENNReal.ofReal_coe_nnreal, hlhs, hrhs]
    calc (∫⁻ x in Set.Ioi m, ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2))
        ≤ ∫⁻ x in Set.Ioi m, ENNReal.ofReal (x - m) * gaussianPDF m v x *
            ∫⁻ t in Set.Ioo m x, ENNReal.ofReal ((deriv f t) ^ 2) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
            (Filter.Eventually.of_forall hpoint))
      _ = (v : ENNReal) *
            ∫⁻ t in Set.Ioi m, gaussianPDF m v t * ENNReal.ofReal ((deriv f t) ^ 2) :=
          lintegral_gaussian_right_triangle m hv _ hg_meas
  refine (ENNReal.ofReal_le_ofReal_iff ?_).1 hmain
  exact mul_nonneg v.coe_nonneg (integral_nonneg fun x ↦
    mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))

/-- Source: local left-half-line estimate in the direct Gaussian proof. Use the finite-interval
bound on `[x, m]`, `lintegral_gaussian_left_triangle`, and the admissible weighted-integrability
helpers. The two half-line energies are added, so the resulting full-line coefficient is `v`. -/
theorem Admissible.integral_Iio_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2 := by
  have hC1 : ContDiff ℝ 1 f := hf.smooth'.of_le (by simp)
  have hcont : Continuous (deriv f) := hC1.continuous_deriv le_rfl
  have hint_sub : IntegrableOn (fun x ↦ gaussianPDFReal m v x * (f x - f m) ^ 2)
      (Set.Iio m) := (hf.integrable_gaussianPDFReal_mul_sq_sub hv (f m)).integrableOn
  have hint_deriv : IntegrableOn (fun x ↦ gaussianPDFReal m v x * (deriv f x) ^ 2)
      (Set.Iio m) := (hf.integrable_gaussianPDFReal_mul_sq_deriv hv).integrableOn
  have hg_meas : Measurable fun t ↦ ENNReal.ofReal ((deriv f t) ^ 2) :=
    (hcont.measurable.pow_const 2).ennreal_ofReal
  have hpoint : ∀ x ∈ Set.Iio m,
      ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
        ENNReal.ofReal (m - x) * gaussianPDF m v x *
          ∫⁻ t in Set.Ioo x m, ENNReal.ofReal ((deriv f t) ^ 2) := by
    intro x hx
    have hxm : x < m := hx
    have hival := interval_sq_sub_le_integral_sq_deriv f hC1 x m hxm.le
    have h1 : gaussianPDFReal m v x * (f x - f m) ^ 2 ≤
        gaussianPDFReal m v x * ((m - x) * ∫ t in x..m, (deriv f t) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (gaussianPDFReal_nonneg m v x)
      calc (f x - f m) ^ 2 = (f m - f x) ^ 2 := by ring
        _ ≤ (m - x) * ∫ t in x..m, (deriv f t) ^ 2 := hival
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    have hIocInt : IntegrableOn (fun t ↦ (deriv f t) ^ 2) (Set.Ioc x m) :=
      (hcont.pow 2).integrableOn_Ioc
    have hofReal : ENNReal.ofReal (∫ t in Set.Ioc x m, (deriv f t) ^ 2) =
        ∫⁻ t in Set.Ioc x m, ENNReal.ofReal ((deriv f t) ^ 2) :=
      ofReal_integral_eq_lintegral_ofReal hIocInt
        (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
    have hIooIoc : (∫⁻ t in Set.Ioo x m, ENNReal.ofReal ((deriv f t) ^ 2)) =
        ∫⁻ t in Set.Ioc x m, ENNReal.ofReal ((deriv f t) ^ 2) :=
      setLIntegral_congr (Ioo_ae_eq_Ioc' (measure_singleton m))
    rw [intervalIntegral.integral_of_le hxm.le,
      ENNReal.ofReal_mul (gaussianPDFReal_nonneg m v x),
      ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ m - x), hofReal, ← hIooIoc, gaussianPDF]
    ring
  have hlhs : ENNReal.ofReal (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) =
      ∫⁻ x in Set.Iio m, ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2) :=
    ofReal_integral_eq_lintegral_ofReal hint_sub
      (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))
  have hrhs : ENNReal.ofReal (∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2) =
      ∫⁻ x in Set.Iio m, gaussianPDF m v x * ENNReal.ofReal ((deriv f x) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint_deriv
      (Filter.Eventually.of_forall fun x ↦
        mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg m v x), gaussianPDF]
  have hmain : ENNReal.ofReal (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      ENNReal.ofReal ((v : ℝ) * ∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2) := by
    rw [ENNReal.ofReal_mul v.coe_nonneg, ENNReal.ofReal_coe_nnreal, hlhs, hrhs]
    calc (∫⁻ x in Set.Iio m, ENNReal.ofReal (gaussianPDFReal m v x * (f x - f m) ^ 2))
        ≤ ∫⁻ x in Set.Iio m, ENNReal.ofReal (m - x) * gaussianPDF m v x *
            ∫⁻ t in Set.Ioo x m, ENNReal.ofReal ((deriv f t) ^ 2) :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Iio).2
            (Filter.Eventually.of_forall hpoint))
      _ = (v : ENNReal) *
            ∫⁻ t in Set.Iio m, gaussianPDF m v t * ENNReal.ofReal ((deriv f t) ^ 2) :=
          lintegral_gaussian_left_triangle m hv _ hg_meas
  refine (ENNReal.ofReal_le_ofReal_iff ?_).1 hmain
  exact mul_nonneg v.coe_nonneg (integral_nonneg fun x ↦
    mul_nonneg (gaussianPDFReal_nonneg m v x) (sq_nonneg _))

/-- Source: local anchored form of the Gaussian upper bound, obtained by joining the two
half-line estimates, discarding the Lebesgue-null endpoint, and using Mathlib's
`integral_gaussianReal_eq_integral_smul` and `gradient_eq_deriv'`. The weighted-integrability
helpers justify the real-integral equalities. No assumption `f m = ∫ x, f x ∂gaussianReal m v`
is made. This step uses the positive-variance density representation. -/
theorem Admissible.integral_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x, (f x - f m) ^ 2 ∂gaussianReal m v) ≤
      (v : ℝ) * energy (gaussianReal m v) f := by
  have hint_sub := hf.integrable_gaussianPDFReal_mul_sq_sub hv (f m)
  have hint_deriv := hf.integrable_gaussianPDFReal_mul_sq_deriv hv
  have hLHS : (∫ x, (f x - f m) ^ 2 ∂gaussianReal m v) =
      ∫ x, gaussianPDFReal m v x * (f x - f m) ^ 2 := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp_rw [smul_eq_mul]
  have hEnergy : energy (gaussianReal m v) f =
      ∫ x, gaussianPDFReal m v x * (deriv f x) ^ 2 := by
    rw [energy]
    have h1 : ∀ x : ℝ, ‖gradient f x‖ ^ 2 = (deriv f x) ^ 2 := fun x ↦ by
      rw [gradient_eq_deriv', Real.norm_eq_abs, sq_abs]
    simp_rw [h1]
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp_rw [smul_eq_mul]
  have hsplit_sub : (∫ x, gaussianPDFReal m v x * (f x - f m) ^ 2) =
      (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) +
        ∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hint_sub.integrableOn hint_sub.integrableOn,
      integral_Iic_eq_integral_Iio]
  have hsplit_deriv : (∫ x, gaussianPDFReal m v x * (deriv f x) ^ 2) =
      (∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2) +
        ∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2 := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hint_deriv.integrableOn hint_deriv.integrableOn,
      integral_Iic_eq_integral_Iio]
  rw [hLHS, hEnergy, hsplit_sub, hsplit_deriv, mul_add]
  exact add_le_add (hf.integral_Iio_sq_sub_gaussian_le hv)
    (hf.integral_Ioi_sq_sub_gaussian_le hv)

end TensorPCA.KLSProofs.Poincare.SmoothTest
