-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityJointEmpiricalMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The logarithm is 1-Lipschitz on [1,infinity). Consequently a positive
random mark bounded below by one has the same iid logarithmic error bound. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityLogEmpiricalMoments
open MeasureTheory ProbabilityTheory Filter
open GGFiniteEmpiricalNormalizer FiniteCavityEmpiricalMoments FiniteCavityJointEmpiricalMoments
open scoped BigOperators
noncomputable section

 theorem abs_log_sub_le_abs_sub {x y : ℝ} (hx : 1≤x) (hy : 1≤y) :
    |Real.log x-Real.log y|≤|x-y| := by
  have hx0 : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0<y := lt_of_lt_of_le zero_lt_one hy
  have step {a b : ℝ} (hb : 1≤b) (hab : b≤a) : Real.log a-Real.log b≤a-b := by
    have hb0 : 0<b := lt_of_lt_of_le zero_lt_one hb
    have ha0 : 0<a := hb0.trans_le hab
    rw [←Real.log_div ha0.ne' hb0.ne']
    calc
      _≤a/b-1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _=(a-b)/b := by field_simp
      _≤a-b := div_le_self (sub_nonneg.mpr hab) hb
  rcases le_total y x with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy0 h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact step hy h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx0 h)),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [step hx h]

variable {G V : Type*} [MeasurableSpace G] [MeasurableSpace V]

 theorem log_error_measurable (K : ℕ) {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (nu : Measure V) [IsProbabilityMeasure nu] :
    Measurable (fun p : G×(Fin K→V) ↦ Real.log (empiricalMean K (F p.1) p.2)-Real.log (∫x,F p.1 x ∂nu)) := by
  have hs : Measurable (fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ ↦ hF.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))).div_const _
  have hm : Measurable (fun g : G ↦ ∫x,F g x ∂nu) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  exact hs.log.sub (hm.comp measurable_fst).log

 theorem log_error_pointwise_le {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {F : G→V→ℝ} (hSec : ∀g,MemLp (F g) 2 nu) (hOne : ∀g x,1≤F g x)
    (g : G) (s : Fin K→V) :
    |Real.log (empiricalMean K (F g) s)-Real.log (∫x,F g x ∂nu)|≤
      |empiricalMean K (F g) s-(∫x,F g x ∂nu)| := by
  have hKR : 0<(K : ℝ) := by exact_mod_cast hK
  have hEmp : 1≤empiricalMean K (F g) s := by
    unfold empiricalMean
    apply (le_div_iff₀ hKR).mpr
    calc
      1*(K : ℝ)=∑_i : Fin K,(1 : ℝ) := by simp
      _≤∑i : Fin K,F g (s i) := Finset.sum_le_sum (fun i _ ↦ hOne g (s i))
  have hPop : 1≤∫x,F g x ∂nu := by
    have H := integral_mono (integrable_const (1 : ℝ)) ((hSec g).integrable (by norm_num)) (hOne g)
    simpa only [integral_const,probReal_univ,one_smul] using H
  exact abs_log_sub_le_abs_sub hEmp hPop

 theorem log_error_integrable {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (hSec : ∀g,MemLp (F g) 2 nu)
    (hSq : Integrable (fun p : G×V ↦ (F p.1 p.2)^2) (mu.prod nu)) (hOne : ∀g x,1≤F g x) :
    Integrable (fun p : G×(Fin K→V) ↦ Real.log (empiricalMean K (F p.1) p.2)-Real.log (∫x,F p.1 x ∂nu))
      (mu.prod (Measure.pi (fun _ : Fin K ↦ nu))) := by
  have hX : MemLp (fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu)) 2
      (mu.prod (Measure.pi (fun _ : Fin K ↦ nu))) :=
    (memLp_two_iff_integrable_sq (error_measurable K hF nu).aestronglyMeasurable).mpr
      (error_sq_integrable hK mu nu hF hSec hSq)
  apply (hX.integrable (by norm_num)).norm.mono' (log_error_measurable K hF nu).aestronglyMeasurable
  exact .of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using log_error_pointwise_le hK nu hSec hOne p.1 p.2)

 theorem log_error_L1_integral_le {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (hSec : ∀g,MemLp (F g) 2 nu)
    (hSq : Integrable (fun p : G×V ↦ (F p.1 p.2)^2) (mu.prod nu)) (hOne : ∀g x,1≤F g x) :
    (∫p : G×(Fin K→V),|Real.log (empiricalMean K (F p.1) p.2)-Real.log (∫x,F p.1 x ∂nu)|
      ∂mu.prod (Measure.pi (fun _ : Fin K ↦ nu)))≤Real.sqrt (∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/Real.sqrt (K : ℝ) := by
  have hX : MemLp (fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu)) 2
      (mu.prod (Measure.pi (fun _ : Fin K ↦ nu))) :=
    (memLp_two_iff_integrable_sq (error_measurable K hF nu).aestronglyMeasurable).mpr
      (error_sq_integrable hK mu nu hF hSec hSq)
  have H := integral_mono (log_error_integrable hK mu nu hF hSec hSq hOne).abs
    (hX.integrable (by norm_num)).abs (fun p ↦ log_error_pointwise_le hK nu hSec hOne p.1 p.2)
  exact H.trans (error_L1_integral_le hK mu nu hF hSec hSq)

end
end TensorPCA.NonRSLowerProofs.FiniteCavityLogEmpiricalMoments
