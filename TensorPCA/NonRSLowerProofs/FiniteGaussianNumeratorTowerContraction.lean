-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsExponentialGrowth
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingScalar

/-! Numerator tower stability for Y>=Z>=1. Increasing masses make every parent exponent
at most one. The error contracts to the ordinary all-zero-mass Gaussian expectation,
without a depth or mass-gap cost.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianNumeratorTowerContraction
open MeasureTheory ProbabilityTheory Filter
open OneStepGaussianStepLipschitz FiniteGaussianLogStepsCompression
open FiniteGaussianOrdinaryStepsExponentialGrowth NumeratorMarkClippingScalar
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

private theorem step_nonneg {K : ℝ≥0} {G : Model.Vector M→ℝ} (hG : LipschitzWith K G)
    (hG0 : ∀z,0≤G z) (T : Model.Vector M→L[ℝ]Model.Vector M) {m : ℝ} (hm : 0<m) (z : Model.Vector M) :
    0≤gaussianLogStep T m G z := by
  have H := integral_mono (integrable_const (1 : ℝ)) (shifted_exp_integrable hG T m z)
    (fun g => Real.one_le_exp_iff.mpr (mul_nonneg hm.le (hG0 _)))
  simp only [integral_const,probReal_univ,one_smul] at H
  rw [gaussianLogStep,if_neg hm.ne']
  exact div_nonneg (Real.log_nonneg H) hm.le

theorem steps_nonneg_mono (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {L K : ℝ≥0} {F G : Model.Vector M→ℝ} (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (hb : ∀z,0≤G z ∧ G z≤F z) (hm : ∀s∈steps,0<s.1) (z : Model.Vector M) :
    0≤gaussianLogSteps steps G z ∧ gaussianLogSteps steps G z≤gaussianLogSteps steps F z := by
  induction steps generalizing z with
  | nil => exact hb z
  | cons s steps ih =>
    have hTail : ∀b∈steps,0<b.1 := fun b h => hm b (by simp [h])
    have HG := gaussianLogSteps_lipschitz hG steps
    have HF := gaussianLogSteps_lipschitz hF steps
    exact ⟨step_nonneg HG (fun y => (ih hTail y).1) s.2 (hm s (by simp)) z,
      OneStepGaussianStepLipschitzOrder.gaussianLogStep_mono HG HF s.2 (hm s (by simp)).le
        (fun y => (ih hTail y).2) z⟩

private theorem exp_mul_step {L : ℝ≥0} {F : Model.Vector M→ℝ} (hF : LipschitzWith L F)
    (T : Model.Vector M→L[ℝ]Model.Vector M) {m : ℝ} (hm : m≠0) (p : ℝ) (z : Model.Vector M) :
    Real.exp (p*gaussianLogStep T m F z)=(gaussianNormalizer T m F z)^(p/m) := by
  rw [gaussianLogStep,if_neg hm,Real.rpow_def_of_pos (gaussianNormalizer_pos hF T m z)]
  congr 1
  ring

private theorem ordinary_cons_eq (s : ℝ×(Model.Vector M→L[ℝ]Model.Vector M))
    (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M))) (F : Model.Vector M→ℝ) (z : Model.Vector M) :
    gaussianLogSteps ((s::steps).map (fun s => (0,s.2))) F z=
      ∫g : Model.Vector M,gaussianLogSteps (steps.map (fun s => (0,s.2))) F (z+s.2 g) ∂stdGaussian (Model.Vector M) := by
  simp only [List.map_cons,gaussianLogSteps,List.foldr_cons,gaussianLogStep,if_pos rfl,ite_true]

theorem power_contraction (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {L K : ℝ≥0} {F G : Model.Vector M→ℝ} (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (hb : ∀z,0≤G z ∧ G z≤F z) (hm : ∀s∈steps,0<s.1 ∧ s.1≤1)
    (horder : steps.Pairwise (fun s t => s.1≤t.1)) {p : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (hpm : ∀s∈steps,p≤s.1) (z : Model.Vector M) :
    0≤Real.exp (p*gaussianLogSteps steps F z)-Real.exp (p*gaussianLogSteps steps G z) ∧
      Real.exp (p*gaussianLogSteps steps F z)-Real.exp (p*gaussianLogSteps steps G z)≤
        p*gaussianLogSteps (steps.map (fun s => (0,s.2))) (fun y => Real.exp (F y)-Real.exp (G y)) z := by
  induction steps generalizing p z with
  | nil =>
    have hGF := Real.exp_le_exp.mpr (hb z).2
    have H := abs_rpow_sub_le hp hp1 (Real.one_le_exp_iff.mpr (hb z).1)
      (Real.one_le_exp_iff.mpr ((hb z).1.trans (hb z).2))
    have HE (q : ℝ) : Real.exp (p*q)=(Real.exp q)^p := by rw [mul_comm,Real.exp_mul]
    have HP : 0≤Real.exp (p*F z)-Real.exp (p*G z) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb z).2 hp))
    refine ⟨HP,?_⟩
    simpa only [gaussianLogSteps,List.foldr_nil,List.map_nil,← HE,
      abs_of_nonneg HP,abs_of_nonneg (sub_nonneg.mpr hGF)] using H
  | cons s steps ih =>
    have hSM := hm s (by simp)
    have hTail : ∀b∈steps,0<b.1 ∧ b.1≤1 := fun b h => hm b (by simp [h])
    have hOrd := List.pairwise_cons.mp horder
    have hPHead : p≤s.1 := hpm s (by simp)
    have HG := gaussianLogSteps_lipschitz hG steps
    have HF := gaussianLogSteps_lipschitz hF steps
    have hI (y : Model.Vector M) := ih hTail hOrd.2 hSM.1.le hSM.2 hOrd.1 y
    have hGF (y : Model.Vector M) := steps_nonneg_mono steps hF hG hb (fun b h => (hTail b h).1) y
    have hRoot := steps_nonneg_mono (s::steps) hF hG hb (fun b h => (hm b h).1) z
    have hNonneg : 0≤Real.exp (p*gaussianLogSteps (s::steps) F z)-Real.exp (p*gaussianLogSteps (s::steps) G z) :=
      sub_nonneg.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hRoot.2 hp))
    refine ⟨hNonneg,?_⟩
    have hAG : 1≤gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z := by
      have H := integral_mono (integrable_const (1 : ℝ)) (shifted_exp_integrable HG s.2 s.1 z)
        (fun g => Real.one_le_exp_iff.mpr (mul_nonneg hSM.1.le (hGF _).1))
      simpa only [gaussianNormalizer,integral_const,probReal_univ,one_smul] using H
    have hAB : gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z≤gaussianNormalizer s.2 s.1 (gaussianLogSteps steps F) z :=
      integral_mono (shifted_exp_integrable HG s.2 s.1 z) (shifted_exp_integrable HF s.2 s.1 z)
        (fun g => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hGF _).2 hSM.1.le))
    have hRI := ordinary_steps_exp_sub_shifted_integrable steps hF hG s.2 z
    have hUpper := integral_mono ((shifted_exp_integrable HF s.2 s.1 z).sub (shifted_exp_integrable HG s.2 s.1 z))
      (hRI.const_mul s.1) (fun g => (hI (z+s.2 g)).2)
    simp only [Pi.sub_apply] at hUpper
    rw [integral_sub (shifted_exp_integrable HF s.2 s.1 z) (shifted_exp_integrable HG s.2 s.1 z),integral_const_mul] at hUpper
    have Hpow := abs_rpow_sub_le (div_nonneg hp hSM.1.le) ((div_le_one hSM.1).mpr hPHead) hAG (hAG.trans hAB)
    rw [abs_of_nonneg (sub_nonneg.mpr hAB)] at Hpow
    change Real.exp (p*gaussianLogStep s.2 s.1 (gaussianLogSteps steps F) z)-
      Real.exp (p*gaussianLogStep s.2 s.1 (gaussianLogSteps steps G) z)≤_
    rw [exp_mul_step HF s.2 hSM.1.ne' p z,exp_mul_step HG s.2 hSM.1.ne' p z,ordinary_cons_eq]
    calc
      _ ≤ (p/s.1)*(gaussianNormalizer s.2 s.1 (gaussianLogSteps steps F) z-gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z) := (le_abs_self _).trans Hpow
      _ ≤ (p/s.1)*(s.1*(∫g : Model.Vector M,gaussianLogSteps (steps.map (fun s => (0,s.2)))
          (fun y => Real.exp (F y)-Real.exp (G y)) (z+s.2 g) ∂stdGaussian (Model.Vector M))) :=
        mul_le_mul_of_nonneg_left hUpper (div_nonneg hp hSM.1.le)
      _ = _ := by field_simp [hSM.1.ne']

theorem root_contraction (steps : List (ℝ×(Model.Vector M→L[ℝ]Model.Vector M)))
    {L K : ℝ≥0} {F G : Model.Vector M→ℝ} (hF : LipschitzWith L F) (hG : LipschitzWith K G)
    (hb : ∀z,0≤G z ∧ G z≤F z) (hm : ∀s∈steps,0<s.1 ∧ s.1≤1)
    (horder : steps.Pairwise (fun s t => s.1≤t.1)) (z : Model.Vector M) :
    0≤gaussianLogSteps steps F z-gaussianLogSteps steps G z ∧
      gaussianLogSteps steps F z-gaussianLogSteps steps G z≤
        gaussianLogSteps (steps.map (fun s => (0,s.2))) (fun y => Real.exp (F y)-Real.exp (G y)) z := by
  have HR := steps_nonneg_mono steps hF hG hb (fun s h => (hm s h).1) z
  refine ⟨sub_nonneg.mpr HR.2,?_⟩
  cases steps with
  | nil =>
    have H := FiniteCavityLogEmpiricalMoments.abs_log_sub_le_abs_sub
      (Real.one_le_exp_iff.mpr ((hb z).1.trans (hb z).2)) (Real.one_le_exp_iff.mpr (hb z).1)
    simp only [Real.log_exp,abs_of_nonneg (sub_nonneg.mpr (hb z).2),
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (hb z).2))] at H
    exact H
  | cons s steps =>
    have hSM := hm s (by simp)
    have hTail : ∀b∈steps,0<b.1 ∧ b.1≤1 := fun b h => hm b (by simp [h])
    have hOrd := List.pairwise_cons.mp horder
    have HG := gaussianLogSteps_lipschitz hG steps
    have HF := gaussianLogSteps_lipschitz hF steps
    have hI (y : Model.Vector M) := power_contraction steps hF hG hb hTail hOrd.2 hSM.1.le hSM.2 hOrd.1 y
    have hGF (y : Model.Vector M) := steps_nonneg_mono steps hF hG hb (fun b h => (hTail b h).1) y
    have hAG : 1≤gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z := by
      have H := integral_mono (integrable_const (1 : ℝ)) (shifted_exp_integrable HG s.2 s.1 z)
        (fun g => Real.one_le_exp_iff.mpr (mul_nonneg hSM.1.le (hGF _).1))
      simpa only [gaussianNormalizer,integral_const,probReal_univ,one_smul] using H
    have hAB : gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z≤gaussianNormalizer s.2 s.1 (gaussianLogSteps steps F) z :=
      integral_mono (shifted_exp_integrable HG s.2 s.1 z) (shifted_exp_integrable HF s.2 s.1 z)
        (fun g => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hGF _).2 hSM.1.le))
    have hRI := ordinary_steps_exp_sub_shifted_integrable steps hF hG s.2 z
    have hUpper := integral_mono ((shifted_exp_integrable HF s.2 s.1 z).sub (shifted_exp_integrable HG s.2 s.1 z))
      (hRI.const_mul s.1) (fun g => (hI (z+s.2 g)).2)
    simp only [Pi.sub_apply] at hUpper
    rw [integral_sub (shifted_exp_integrable HF s.2 s.1 z) (shifted_exp_integrable HG s.2 s.1 z),integral_const_mul] at hUpper
    have Hlog := FiniteCavityLogEmpiricalMoments.abs_log_sub_le_abs_sub (hAG.trans hAB) hAG
    rw [abs_of_nonneg (sub_nonneg.mpr hAB)] at Hlog
    change gaussianLogStep s.2 s.1 (gaussianLogSteps steps F) z-
      gaussianLogStep s.2 s.1 (gaussianLogSteps steps G) z≤_
    rw [ordinary_cons_eq]
    simp only [gaussianLogStep,if_neg hSM.1.ne']
    calc
      _ = (Real.log (gaussianNormalizer s.2 s.1 (gaussianLogSteps steps F) z)-
          Real.log (gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z))/s.1 := by ring
      _ ≤ (gaussianNormalizer s.2 s.1 (gaussianLogSteps steps F) z-gaussianNormalizer s.2 s.1 (gaussianLogSteps steps G) z)/s.1 :=
        div_le_div_of_nonneg_right ((le_abs_self _).trans Hlog) hSM.1.le
      _ ≤ (s.1*(∫g : Model.Vector M,gaussianLogSteps (steps.map (fun s => (0,s.2)))
          (fun y => Real.exp (F y)-Real.exp (G y)) (z+s.2 g) ∂stdGaussian (Model.Vector M)))/s.1 :=
        div_le_div_of_nonneg_right hUpper hSM.1.le
      _ = _ := by field_simp [hSM.1.ne']

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianNumeratorTowerContraction
