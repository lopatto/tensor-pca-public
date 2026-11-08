-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGConditionalLowMass

/-! Weighted candidate-window lower bounds under a conditional probability law. The only
moment premise is the displayed ordinary first moment; the low-candidate correction
is proved from pair mass.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGWeightedConditionalWindow
open MeasureTheory ProbabilityTheory Set
open FiniteGGConditionalLowMass FiniteGGWindowScalar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {P V : Type*} [MeasurableSpace P] [MeasurableSpace V]

theorem weighted_conditional_window_integral_lower (mu : Measure P) [IsProbabilityMeasure mu]
    (G : Kernel P V) [IsMarkovKernel G]
    (Omega : Set (P×V)) (hOmega : MeasurableSet Omega)
    (B : Set (P×(V×V))) (hB : MeasurableSet B)
    (f : P×V → ℝ) (hf : Measurable f) (hfb : ∀ q,0≤f q ∧ f q≤1)
    (hSupport : ∀ q,q∉Omega→f q=0)
    {kappa eta : ℝ} (hK : 0<kappa) (n : ℕ) (hn : 2≤n)
    (hMoment : (∫ q,f q*candidateMass G B q ∂(mu⊗ₘG))≤
      (∫ q,f q ∂(mu⊗ₘG))/(n : ℝ)+eta) :
    (∫ q,f q ∂(mu⊗ₘG))/3-kappa-Real.sqrt (∫ p,badPairMass G Omega B p ∂mu)-4*eta/3≤
      ∫ q,f q*window kappa (candidateMass G B q) ∂(mu⊗ₘG) := by
  let W := candidateMass G B
  let Low := Omega∩{q | W q≤kappa}
  have hWm : Measurable W := candidateMass_measurable G B hB
  have hLow : MeasurableSet Low := hOmega.inter (measurableSet_le hWm measurable_const)
  have hfi : Integrable f (mu⊗ₘG) := Integrable.of_bound hf.aestronglyMeasurable 1
    (.of_forall (fun q ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hfb q).1]; exact (hfb q).2))
  have hWi : Integrable (fun q ↦ f q*W q) (mu⊗ₘG) := Integrable.of_bound
    (hf.mul hWm).aestronglyMeasurable 1 (.of_forall (fun q ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hfb q).1 (candidateMass_mem_Icc G B q).1)]
      exact mul_le_one₀ (hfb q).2 (candidateMass_mem_Icc G B q).1 (candidateMass_mem_Icc G B q).2))
  have hChi : Integrable (fun q ↦ f q*window kappa (W q)) (mu⊗ₘG) := Integrable.of_bound
    (hf.mul ((window_continuous kappa).measurable.comp hWm)).aestronglyMeasurable 1 (.of_forall (fun q ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hfb q).1 (window_mem_Icc kappa (W q)).1)]
      exact mul_le_one₀ (hfb q).2 (window_mem_Icc kappa (W q)).1 (window_mem_Icc kappa (W q)).2))
  have hLi := (integrable_const (μ := mu⊗ₘG) (1 : ℝ)).indicator hLow
  have hPoint (q : P×V) : f q-Low.indicator (fun _ ↦ (1 : ℝ)) q-(4/3 : ℝ)*(f q*W q)≤
      f q*window kappa (W q) := by
    have hfw : 0≤f q*W q := mul_nonneg (hfb q).1 (candidateMass_mem_Icc G B q).1
    have hfc : 0≤f q*window kappa (W q) := mul_nonneg (hfb q).1 (window_mem_Icc kappa (W q)).1
    by_cases hw : W q≤kappa
    · by_cases hq : q∈Omega
      · rw [Set.indicator_of_mem (show q∈Low from ⟨hq,hw⟩)]
        nlinarith only [(hfb q).2,hfw,hfc]
      · have hL : q∉Low := fun h ↦ hq h.1
        rw [hSupport q hq,Set.indicator_of_notMem hL,zero_mul,zero_mul]
        norm_num
    · have hL : q∉Low := fun h ↦ hw h.2
      rw [Set.indicator_of_notMem hL,sub_zero]
      by_cases hHi : W q≤(3/4 : ℝ)
      · rw [window_eq_one hK (le_of_not_ge hw) hHi,mul_one]
        nlinarith only [hfw]
      · have hgt : (3/4 : ℝ)<W q := lt_of_not_ge hHi
        nlinarith only [hgt,hfc,(hfb q).1]
  have hDiff : Integrable (fun q ↦ f q-Low.indicator (fun _ ↦ (1 : ℝ)) q) (mu⊗ₘG) := hfi.sub hLi
  have hMult : Integrable (fun q ↦ (4/3 : ℝ)*(f q*W q)) (mu⊗ₘG) := hWi.const_mul _
  have H := integral_mono (hDiff.sub hMult) hChi hPoint
  simp only [Pi.sub_apply] at H
  rw [integral_sub hDiff hMult,integral_sub hfi hLi,integral_const_mul,
    integral_indicator_const (1 : ℝ) hLow,smul_eq_mul,mul_one] at H
  have hLowMass := conditional_low_mass_le mu G Omega hOmega B hB Omega hOmega (Subset.refl _) hK.le
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hHalf : (∫ q,f q ∂(mu⊗ₘG))/(n : ℝ)≤(∫ q,f q ∂(mu⊗ₘG))/2 :=
    div_le_div_of_nonneg_left (integral_nonneg (fun q ↦ (hfb q).1)) (by norm_num) hnR
  have hFirst := hMoment.trans (add_le_add hHalf (le_refl eta))
  change (mu⊗ₘG).real Low≤kappa+Real.sqrt (∫ p,badPairMass G Omega B p ∂mu) at hLowMass
  nlinarith only [H,hLowMass,hFirst]

end
end TensorPCA.NonRSLowerProofs.FiniteGGWeightedConditionalWindow
