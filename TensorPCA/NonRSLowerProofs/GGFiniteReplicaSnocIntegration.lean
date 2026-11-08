-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.GaussianReplicaKernel
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-! Joint bounded-observable iid replica extension. The observable may depend
on the disorder and every old/fresh coordinate without any separability. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReplicaSnocIntegration
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

theorem snoc_measurable (n : ℕ) :
    Measurable (fun p : (Fin (n+1) → V)×V ↦ (Fin.snoc p.1 p.2 : Fin (n+2) → V)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.snoc_last] using measurable_snd
  · simpa only [Fin.snoc_castSucc,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

theorem integral_pi_snoc (nu : Measure V) [IsProbabilityMeasure nu] (n : ℕ)
    (f : (Fin (n+2) → V) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ s, |f s|≤C) :
    (∫ s, f s ∂Measure.pi (fun _ : Fin (n+2) ↦ nu))=
      ∫ old : Fin (n+1) → V, ∫ fresh : V, f (Fin.snoc old fresh) ∂nu
        ∂Measure.pi (fun _ : Fin (n+1) ↦ nu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+2) ↦ V) (Fin.last (n+1))
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+2) ↦ nu) (Fin.last (n+1))).symm
  have hi : Integrable f (Measure.pi (fun _ : Fin (n+2) ↦ nu)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hb s))
  have heq (p : V×(Fin (n+1) → V)) : e.symm p=Fin.snoc p.2 p.1 := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_last']
    rfl
  have hp : Integrable (fun p : V×(Fin (n+1) → V) ↦ f (Fin.snoc p.2 p.1))
      (nu.prod (Measure.pi (fun _ : Fin (n+1) ↦ nu))) := by
    have hp0 := hmp.integrable_comp_of_integrable hi
    change Integrable (fun p : V×(Fin (n+1) → V) ↦ f (e.symm p))
      (nu.prod (Measure.pi (fun _ : Fin (n+1) ↦ nu))) at hp0
    simpa only [heq] using hp0
  have H := hmp.integral_comp e.symm.measurableEmbedding f
  change (∫ p : V×(Fin (n+1) → V), f (e.symm p) ∂nu.prod (Measure.pi (fun _ : Fin (n+1) ↦ nu)))=
    ∫ s, f s ∂Measure.pi (fun _ : Fin (n+2) ↦ nu) at H
  have H' : (∫ s, f s ∂Measure.pi (fun _ : Fin (n+2) ↦ nu))=
      ∫ p : V×(Fin (n+1) → V), f (Fin.snoc p.2 p.1) ∂nu.prod (Measure.pi (fun _ : Fin (n+1) ↦ nu)) := by
    simpa only [heq] using H.symm
  exact H'.trans (integral_prod_symm _ hp)

theorem integral_joint_iid_snoc (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    (f : Ω×(Fin (n+2) → V) → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ p, |f p|≤C) :
    (∫ p, f p ∂(d ⊗ₘ iid G (n+2)))=
      ∫ p : Ω×(Fin (n+1) → V), (∫ fresh : V, f (p.1,Fin.snoc p.2 fresh) ∂G p.1)
        ∂(d ⊗ₘ iid G (n+1)) := by
  have hi : Integrable f (d ⊗ₘ iid G (n+2)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hb p))
  let kap : Kernel (Ω×(Fin (n+1) → V)) V := G.comap Prod.fst measurable_fst
  have hsnoc : Measurable (fun q : (Ω×(Fin (n+1) → V))×V ↦
      (q.1.1,(Fin.snoc q.1.2 q.2 : Fin (n+2) → V))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((snoc_measurable n).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hjm : Measurable (fun p : Ω×(Fin (n+1) → V) ↦ ∫ fresh, f (p.1,Fin.snoc p.2 fresh) ∂G p.1) := by
    simpa only [kap,Kernel.comap_apply,Function.comp_def] using
      ((hf.comp hsnoc).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hjb (p : Ω×(Fin (n+1) → V)) : |∫ fresh, f (p.1,Fin.snoc p.2 fresh) ∂G p.1|≤C := by
    have H := norm_integral_le_of_norm_le_const (μ := G p.1)
      (f := fun fresh ↦ f (p.1,Fin.snoc p.2 fresh)) (C := C)
      (Eventually.of_forall (fun fresh ↦ by simpa only [Real.norm_eq_abs] using hb (p.1,Fin.snoc p.2 fresh)))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hj : Integrable (fun p : Ω×(Fin (n+1) → V) ↦ ∫ fresh, f (p.1,Fin.snoc p.2 fresh) ∂G p.1)
      (d ⊗ₘ iid G (n+1)) :=
    Integrable.of_bound hjm.aestronglyMeasurable C
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hjb p))
  rw [Measure.integral_compProd hi,Measure.integral_compProd hj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w ↦ by
    simp only [iid_apply]
    exact integral_pi_snoc (G w) n (fun s ↦ f (w,s))
      (hf.comp (measurable_const.prodMk measurable_id)) (fun s ↦ hb (w,s)))

end
end TensorPCA.NonRSLowerProofs.GGFiniteReplicaSnocIntegration
