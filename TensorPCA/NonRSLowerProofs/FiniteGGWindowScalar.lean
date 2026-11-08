-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGNoDuplicationMass
public import TensorPCA.NonRSLowerProofs.FiniteGGContinuousMomentTransfer
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FunProp

/-! Scalar indicator-mass algebra and an explicit continuous window. The rational tilt
identity here is scalar algebra; no Gibbs indicator transport is asserted by these
lemmas.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
open MeasureTheory Set
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def indicatorTiltMass (t w : ℝ) : ℝ := Real.exp t*w/(1-w+Real.exp t*w)

 theorem indicator_tilt_denominator_pos {t w : ℝ} (ht : 0≤t) (hw : w∈Icc (0 : ℝ) 1) :
    0<1-w+Real.exp t*w := by
  have H := mul_le_mul_of_nonneg_right (Real.one_le_exp ht) hw.1
  nlinarith only [H]

 theorem original_mass_le_of_tilted_le {t w : ℝ} (ht : 0≤t) (hw : w∈Icc (0 : ℝ) 1)
    (hTilt : indicatorTiltMass t w≤(7/8 : ℝ)) : w≤7*Real.exp (-t) := by
  have hd := indicator_tilt_denominator_pos ht hw
  have H := (div_le_iff₀ hd).mp hTilt
  have hEW : Real.exp t*w≤7 := by nlinarith only [H,hw.1]
  have hW : w≤7/Real.exp t := (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hEW)
  simpa only [Real.exp_neg,div_eq_mul_inv] using hW

 theorem root_decay {t gamma delta D : ℝ} (ht : 0≤t) (hDelta : 0≤delta)
    (hGamma : gamma≤1-delta) :
    Real.exp (t*gamma)*(7*Real.exp (-t)+Real.sqrt D)≤
      7*Real.exp (-t*delta)+Real.exp t*Real.sqrt D := by
  have hFirst : Real.exp (t*gamma)*Real.exp (-t)≤Real.exp (-t*delta) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have H := mul_le_mul_of_nonneg_left hGamma ht
    nlinarith only [H]
  have hSecond : Real.exp (t*gamma)≤Real.exp t := by
    apply Real.exp_le_exp.mpr
    have H := mul_le_mul_of_nonneg_left (show gamma≤1 by linarith) ht
    simpa only [mul_one] using H
  calc
    _=7*(Real.exp (t*gamma)*Real.exp (-t))+Real.exp (t*gamma)*Real.sqrt D := by ring
    _≤_ := add_le_add (mul_le_mul_of_nonneg_left hFirst (by norm_num))
      (mul_le_mul_of_nonneg_right hSecond (Real.sqrt_nonneg _))

 theorem weighted_small_section_mass_le {Omega : Type*} [MeasurableSpace Omega]
    (nu : Measure Omega) [IsProbabilityMeasure nu]
    (B : Omega→Set Omega) (hB : MeasurableSet {p : Omega×Omega | p.2∈B p.1})
    (S : Set Omega) (hS : MeasurableSet S) {t gamma delta : ℝ}
    (ht : 0≤t) (hDelta : 0≤delta) (hGamma : gamma≤1-delta)
    (hTilt : ∀u∈S,indicatorTiltMass t (nu.real (B u))≤(7/8 : ℝ)) :
    Real.exp (t*gamma)*nu.real S≤7*Real.exp (-t*delta)+Real.exp t*
      Real.sqrt ((nu.prod nu).real {p : Omega×Omega | p.1∈S ∧ p.2∈S ∧ p.2∉B p.1}) := by
  have hSmall : ∀u∈S,nu.real (B u)≤7*Real.exp (-t) := by
    intro u hu
    have hOne : nu.real (B u)≤1 := by
      simpa only [probReal_univ] using (measureReal_mono (μ := nu) (subset_univ (B u)))
    exact original_mass_le_of_tilted_le ht ⟨measureReal_nonneg,hOne⟩ (hTilt u hu)
  have H := FiniteGGNoDuplicationMass.small_section_set_mass_le nu B hB S hS
    (by positivity : 0≤7*Real.exp (-t)) hSmall
  exact (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans (root_decay ht hDelta hGamma)

/-- A literal continuous [0,1]-valued window, with no measurable selection. -/
def window (kappa w : ℝ) : ℝ :=
  max 0 (min 1 (2*w/kappa-1))*max 0 (min 1 (7-8*w))

 theorem window_continuous (kappa : ℝ) : Continuous (window kappa) := by
  unfold window
  fun_prop

 theorem window_mem_Icc (kappa w : ℝ) : window kappa w∈Icc (0 : ℝ) 1 := by
  have hClip (r : ℝ) : 0≤max 0 (min 1 r) ∧ max 0 (min 1 r)≤1 :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hA := hClip (2*w/kappa-1)
  have hB := hClip (7-8*w)
  exact ⟨mul_nonneg hA.1 hB.1,(mul_le_mul hA.2 hB.2 hB.1 (by norm_num)).trans_eq (by norm_num)⟩

 theorem window_eq_one {kappa w : ℝ} (hK : 0<kappa) (hLo : kappa≤w) (hHi : w≤(3/4 : ℝ)) :
    window kappa w=1 := by
  have hA : 1≤2*w/kappa-1 := by
    have H : 2≤2*w/kappa := (le_div_iff₀ hK).mpr (by linarith)
    linarith only [H]
  have hB : 1≤7-8*w := by linarith only [hHi]
  simp only [window,min_eq_left hA,min_eq_left hB,max_eq_right zero_le_one,one_mul]

 theorem window_eq_zero_of_le_half {kappa w : ℝ} (hK : 0<kappa) (hW : w≤kappa/2) :
    window kappa w=0 := by
  have hA : 2*w/kappa-1≤0 := by
    have H : 2*w/kappa≤1 := (div_le_iff₀ hK).mpr (by linarith)
    linarith only [H]
  unfold window
  rw [max_eq_left ((min_le_right _ _).trans hA),zero_mul]

 theorem window_eq_zero_of_upper {kappa w : ℝ} (hW : (7/8 : ℝ)≤w) : window kappa w=0 := by
  have hB : 7-8*w≤0 := by linarith only [hW]
  unfold window
  rw [max_eq_left ((min_le_right _ _).trans hB),mul_zero]

 theorem window_pos_imp_bounds {kappa w : ℝ} (hK : 0<kappa) (hW : 0<window kappa w) :
    kappa/2<w ∧ w<(7/8 : ℝ) := by
  constructor
  · by_contra h
    have H := window_eq_zero_of_le_half hK (le_of_not_gt h)
    linarith only [H,hW]
  · by_contra h
    have H := window_eq_zero_of_upper (kappa := kappa) (le_of_not_gt h)
    linarith only [H,hW]

 def windowTest (kappa : ℝ) : FiniteGGContinuousMomentTransfer.Tests :=
  ⟨fun r ↦ window kappa r,(window_continuous kappa).comp continuous_subtype_val⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGGWindowScalar
