-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar

/-! A uniform continuous-window lower bound from first-moment and low-mass estimates. The
argument uses measure algebra.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGWindowLowerMass
open MeasureTheory Set
open FiniteGGWindowScalar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem window_lower (kappa w : ℝ) (hK : 0<kappa) (hw : 0≤w) :
    1-(if w≤kappa then 1 else 0)-(4/3 : ℝ)*w≤window kappa w := by
  have hNonneg := (window_mem_Icc kappa w).1
  by_cases hLo : w≤kappa
  · rw [if_pos hLo]
    nlinarith only [hNonneg,hw]
  · rw [if_neg hLo]
    by_cases hHi : w≤(3/4 : ℝ)
    · rw [window_eq_one hK (le_of_not_ge hLo) hHi]
      nlinarith only [hw]
    · have H : (3/4 : ℝ)<w := lt_of_not_ge hHi
      nlinarith only [hNonneg,H]

 theorem window_integral_lower_of_moment {S : Type*} [MeasurableSpace S]
    (mu : Measure S) [IsProbabilityMeasure mu] (A : Set S) (hA : MeasurableSet A)
    (W : S→Icc (0 : ℝ) 1) (hW : Measurable W) {kappa ell eta : ℝ} (hK : 0<kappa)
    (n : ℕ) (hn : 2≤n)
    (hLow : mu.real (A∩{s | (W s : ℝ)≤kappa})≤ell)
    (hMoment : (∫s,A.indicator (fun s ↦ (W s : ℝ)) s ∂mu)≤mu.real A/(n : ℝ)+eta) :
    mu.real A/3-ell-4*eta/3≤∫s,A.indicator (fun s ↦ window kappa (W s)) s ∂mu := by
  let Low := A∩{s | (W s : ℝ)≤kappa}
  have hWm : Measurable (fun s ↦ (W s : ℝ)) := continuous_subtype_val.measurable.comp hW
  have hLowSet : MeasurableSet Low := hA.inter (measurableSet_le hWm measurable_const)
  have hWi : Integrable (fun s ↦ (W s : ℝ)) mu := Integrable.of_bound hWm.aestronglyMeasurable 1
    (.of_forall (fun s ↦ by rw [Real.norm_of_nonneg (W s).property.1]; exact (W s).property.2))
  have hWindowi : Integrable (fun s ↦ window kappa (W s)) mu := Integrable.of_bound
    ((window_continuous kappa).measurable.comp hWm).aestronglyMeasurable 1
    (.of_forall (fun s ↦ by rw [Real.norm_of_nonneg (window_mem_Icc kappa (W s)).1]; exact (window_mem_Icc kappa (W s)).2))
  have hAi := (integrable_const (μ := mu) (1 : ℝ)).indicator hA
  have hLi := (integrable_const (μ := mu) (1 : ℝ)).indicator hLowSet
  have hFi := hWi.indicator hA
  have hChi := hWindowi.indicator hA
  have hPoint (s : S) : A.indicator (fun _ ↦ (1 : ℝ)) s-Low.indicator (fun _ ↦ (1 : ℝ)) s-
      (4/3 : ℝ)*A.indicator (fun s ↦ (W s : ℝ)) s≤A.indicator (fun s ↦ window kappa (W s)) s := by
    by_cases hs : s∈A
    · have H := window_lower kappa (W s) hK (W s).property.1
      by_cases hw : (W s : ℝ)≤kappa
      · have hl : s∈Low := ⟨hs,hw⟩
        simpa only [indicator_of_mem hs,indicator_of_mem hl,if_pos hw] using H
      · have hl : s∉Low := fun h ↦ hw h.2
        simpa only [indicator_of_mem hs,indicator_of_notMem hl,if_neg hw] using H
    · have hl : s∉Low := fun h ↦ hs h.1
      simp only [indicator_of_notMem hs,indicator_of_notMem hl,mul_zero,sub_zero,le_refl]
  have hDiff : Integrable (fun s ↦ A.indicator (fun _ ↦ (1 : ℝ)) s-Low.indicator (fun _ ↦ (1 : ℝ)) s) mu := hAi.sub hLi
  have hMult : Integrable (fun s ↦ (4/3 : ℝ)*A.indicator (fun s ↦ (W s : ℝ)) s) mu := hFi.const_mul _
  have H := integral_mono (hDiff.sub hMult) hChi hPoint
  simp only [Pi.sub_apply] at H
  rw [integral_sub hDiff hMult,integral_sub hAi hLi,
    integral_const_mul,integral_indicator_const 1 hA,integral_indicator_const 1 hLowSet] at H
  simp only [smul_eq_mul,mul_one] at H
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hHalf : mu.real A/(n : ℝ)≤mu.real A/2 :=
    div_le_div_of_nonneg_left measureReal_nonneg (by norm_num) hnR
  have hFirst := hMoment.trans (add_le_add hHalf (le_refl eta))
  change mu.real Low≤ell at hLow
  nlinarith only [H,hLow,hFirst]

end
end TensorPCA.NonRSLowerProofs.FiniteGGWindowLowerMass
