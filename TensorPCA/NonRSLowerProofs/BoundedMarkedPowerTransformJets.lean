-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! All-order smoothness and moment jets of the bounded mark transform. The derivative
family is private and consists of literal Bochner integrals.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff
noncomputable section
variable {V : Type*} [MeasurableSpace V]

private def powerJet (nu : Measure V) (Z : V→ℝ) (alpha : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (descPochhammer ℝ n).eval alpha*(∫v,(-Z v)^n*(1-t*Z v)^(alpha-(n : ℝ)) ∂nu)

private theorem powerJet_hasDerivAt (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (alpha : ℝ) (n : ℕ) {t : ℝ}
    (ht : |t| *(A+1)<1/2) :
    HasDerivAt (powerJet nu Z alpha n) (powerJet nu Z alpha (n+1) t) t := by
  have H := weighted_power_hasDerivAt nu hZ hA hb (alpha-(n : ℝ)) n ht
  rw [show alpha-(n : ℝ)-1=alpha-((n : ℝ)+1) by ring] at H
  change HasDerivAt (fun s => (descPochhammer ℝ n).eval alpha*
    (∫v,(-Z v)^n*(1-s*Z v)^(alpha-(n : ℝ)) ∂nu))
    ((descPochhammer ℝ (n+1)).eval alpha*
    (∫v,(-Z v)^(n+1)*(1-t*Z v)^(alpha-((n+1 : ℕ) : ℝ)) ∂nu)) t
  simpa only [descPochhammer_succ_eval,Nat.cast_add,Nat.cast_one,mul_assoc]
    using H.const_mul ((descPochhammer ℝ n).eval alpha)

private theorem powerJet_contDiffOn (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (alpha : ℝ) (n j : ℕ) :
    ContDiffOn ℝ n (powerJet nu Z alpha j) {t | |t| *(A+1)<1/2} := by
  have hs : IsOpen {t : ℝ | |t| *(A+1)<1/2} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  have hd (j : ℕ) : DifferentiableOn ℝ (powerJet nu Z alpha j) {t | |t| *(A+1)<1/2} :=
    fun t ht => (powerJet_hasDerivAt nu hZ hA hb alpha j ht).differentiableAt.differentiableWithinAt
  induction n generalizing j with
  | zero => exact contDiffOn_zero.mpr (hd j).continuousOn
  | succ n ih =>
    rw [show ((n+1 : ℕ) : ℕ∞ω)=(n : ℕ∞ω)+1 by rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨hd j,by simp,?_⟩
    apply (ih (j+1)).congr
    intro t ht
    exact (powerJet_hasDerivAt nu hZ hA hb alpha j ht).deriv

private theorem iteratedDeriv_eq_powerJet (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (alpha : ℝ) (n : ℕ) {t : ℝ}
    (ht : |t| *(A+1)<1/2) :
    iteratedDeriv n (markTransform nu Z alpha) t=powerJet nu Z alpha n t := by
  induction n generalizing t with
  | zero => simp [markTransform,powerJet]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have H : iteratedDeriv n (markTransform nu Z alpha) =ᶠ[𝓝 t] powerJet nu Z alpha n := by
      have hs : IsOpen {s : ℝ | |s| *(A+1)<1/2} :=
        isOpen_lt (continuous_abs.mul continuous_const) continuous_const
      filter_upwards [hs.mem_nhds ht] with s hs
      exact ih hs
    rw [H.deriv_eq]
    exact (powerJet_hasDerivAt nu hZ hA hb alpha n ht).deriv

theorem markTransform_contDiffAt_zero (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (alpha : ℝ) (n : ℕ) :
    ContDiffAt ℝ n (markTransform nu Z alpha) 0 := by
  have H := powerJet_contDiffOn nu hZ hA hb alpha n 0
  have H0 : powerJet nu Z alpha 0=markTransform nu Z alpha := by
    funext t
    simp [powerJet,markTransform]
  rw [H0] at H
  exact H.contDiffAt ((isOpen_lt (continuous_abs.mul continuous_const) continuous_const).mem_nhds
    (by norm_num : |(0 : ℝ)| *(A+1)<1/2))

theorem markTransform_zero (nu : Measure V) [IsProbabilityMeasure nu] (Z : V→ℝ) (alpha : ℝ) :
    markTransform nu Z alpha 0=1 := by simp [markTransform]

theorem markTransform_iteratedDeriv_zero (nu : Measure V) [IsProbabilityMeasure nu]
    {Z : V→ℝ} (hZ : Measurable Z) {A : ℝ} (hA : 0≤A)
    (hb : ∀ᵐv∂nu,|Z v|≤A) (alpha : ℝ) (n : ℕ) :
    iteratedDeriv n (markTransform nu Z alpha) 0=
      ((-1 : ℝ)^n*(descPochhammer ℝ n).eval alpha)*(∫v,(Z v)^n ∂nu) := by
  rw [iteratedDeriv_eq_powerJet nu hZ hA hb alpha n (by norm_num)]
  simp only [powerJet,zero_mul,sub_zero,Real.one_rpow,mul_one]
  have H : (fun v : V => (-Z v)^n)=(fun v => (-1 : ℝ)^n*(Z v)^n) := by
    funext v
    rw [← mul_pow,neg_one_mul]
  rw [H]
  rw [integral_const_mul]
  ring

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedPowerTransform
