-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityEmpiricalMoments
public import Mathlib.MeasureTheory.Integral.Prod

/-! Iid empirical errors for a random square-integrable mark. The random mark and the
iid sample are integrated under their product law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityJointEmpiricalMoments
open MeasureTheory ProbabilityTheory Filter
open GGFiniteEmpiricalNormalizer FiniteCavityEmpiricalMoments
open scoped BigOperators
noncomputable section
variable {G V : Type*} [MeasurableSpace G] [MeasurableSpace V]

 theorem error_measurable (K : ℕ) {F : G → V → ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (nu : Measure V) [IsProbabilityMeasure nu] :
    Measurable (fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu)) := by
  have hs : Measurable (fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2) := by
    unfold empiricalMean
    exact (Finset.measurable_sum _ (fun i _ ↦ hF.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))).div_const _
  have hm : Measurable (fun g : G ↦ ∫x,F g x ∂nu) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  exact hs.sub (hm.comp measurable_fst)

 theorem error_sq_integrable {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (hSec : ∀g,MemLp (F g) 2 nu)
    (hSq : Integrable (fun p : G×V ↦ (F p.1 p.2)^2) (mu.prod nu)) :
    Integrable (fun p : G×(Fin K→V) ↦ (empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu))^2)
      (mu.prod (Measure.pi (fun _ : Fin K ↦ nu))) := by
  have hm := ((error_measurable K hF nu).pow_const 2).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hSecErr (g : G) : Integrable (fun s : Fin K→V ↦
      (empiricalMean K (F g) s-(∫x,F g x ∂nu))^2) (Measure.pi (fun _ : Fin K ↦ nu)) :=
    ((empiricalMean_memLp K nu (hSec g)).sub
      (memLp_const (∫x,F g x ∂nu))).integrable_sq
  refine ⟨.of_forall hSecErr,?_⟩
  have hparam : AEStronglyMeasurable (fun g : G ↦ ∫s : Fin K→V,
      ‖(empiricalMean K (F g) s-(∫x,F g x ∂nu))^2‖ ∂Measure.pi (fun _ : Fin K ↦ nu)) mu :=
    hm.norm.integral_prod_right'.aestronglyMeasurable
  apply (hSq.integral_prod_left.div_const (K : ℝ)).mono' hparam
  filter_upwards [] with g
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  have he : (fun s : Fin K→V ↦ ‖(empiricalMean K (F g) s-(∫x,F g x ∂nu))^2‖)=
      (fun s : Fin K→V ↦ (empiricalMean K (F g) s-(∫x,F g x ∂nu))^2) := by
    funext s
    exact Real.norm_of_nonneg (sq_nonneg _)
  rw [he]
  exact empiricalMean_centered_sq_le hK nu (hSec g)

 theorem error_sq_integral_le {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (hSec : ∀g,MemLp (F g) 2 nu)
    (hSq : Integrable (fun p : G×V ↦ (F p.1 p.2)^2) (mu.prod nu)) :
    (∫p : G×(Fin K→V),(empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu))^2
      ∂mu.prod (Measure.pi (fun _ : Fin K ↦ nu)))≤(∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/(K : ℝ) := by
  have hI := error_sq_integrable hK mu nu hF hSec hSq
  rw [integral_prod _ hI]
  have H := integral_mono hI.integral_prod_left (hSq.integral_prod_left.div_const (K : ℝ))
    (fun g ↦ empiricalMean_centered_sq_le hK nu (hSec g))
  rw [integral_div,←integral_prod _ hSq] at H
  exact H

 theorem error_L1_integral_le {K : ℕ} (hK : 0<K) (mu : Measure G) [IsProbabilityMeasure mu]
    (nu : Measure V) [IsProbabilityMeasure nu] {F : G→V→ℝ}
    (hF : Measurable (fun p : G×V ↦ F p.1 p.2)) (hSec : ∀g,MemLp (F g) 2 nu)
    (hSq : Integrable (fun p : G×V ↦ (F p.1 p.2)^2) (mu.prod nu)) :
    (∫p : G×(Fin K→V),|empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu)|
      ∂mu.prod (Measure.pi (fun _ : Fin K ↦ nu)))≤Real.sqrt (∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/Real.sqrt (K : ℝ) := by
  let P := mu.prod (Measure.pi (fun _ : Fin K ↦ nu))
  let X := fun p : G×(Fin K→V) ↦ empiricalMean K (F p.1) p.2-(∫x,F p.1 x ∂nu)
  have hX : MemLp X 2 P := (memLp_two_iff_integrable_sq (error_measurable K hF nu).aestronglyMeasurable).mpr
    (error_sq_integrable hK mu nu hF hSec hSq)
  have hAbs : MemLp (fun p ↦ |X p|) 2 P := by simpa only [Real.norm_eq_abs] using hX.norm
  have hCS : (∫p,|X p| ∂P)^2≤∫p,(X p)^2 ∂P := by
    have H := variance_nonneg (fun p ↦ |X p|) P
    rw [variance_eq_sub hAbs] at H
    change 0≤(∫p,|X p|^2 ∂P)-(∫p,|X p| ∂P)^2 at H
    simp only [sq_abs] at H
    linarith
  have hKR : 0<(K : ℝ) := by exact_mod_cast hK
  have hRoot : (Real.sqrt (∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/Real.sqrt (K : ℝ))^2=
      (∫p : G×V,(F p.1 p.2)^2 ∂mu.prod nu)/(K : ℝ) := by
    rw [div_pow,Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _)),Real.sq_sqrt hKR.le]
  apply (sq_le_sq₀ (integral_nonneg (fun _ ↦ abs_nonneg _)) (by positivity)).mp
  exact (hCS.trans (error_sq_integral_le hK mu nu hF hSec hSq)).trans_eq hRoot.symm

end
end TensorPCA.NonRSLowerProofs.FiniteCavityJointEmpiricalMoments
