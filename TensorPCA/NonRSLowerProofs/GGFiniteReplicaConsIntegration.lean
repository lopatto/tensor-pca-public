-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GGFiniteReplicaSnocIntegration

/-! Conditional iid extension by prepending fresh replica zero. The arbitrary bounded
observable may depend jointly on disorder and all spins. This is distinct from the
existing fresh-last snoc convention.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GGFiniteReplicaConsIntegration
open MeasureTheory ProbabilityTheory Filter
open NonRSUpperProofs.GaussianReplicaKernel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

theorem cons_measurable (n : ℕ) :
    Measurable (fun p : (Fin n→V)×V ↦ (Fin.cons p.2 p.1 : Fin (n+1)→V)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using measurable_snd
  · simpa only [Fin.cons_succ,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

theorem integral_pi_cons (nu : Measure V) [IsProbabilityMeasure nu] (n : ℕ)
    (f : (Fin (n+1)→V)→ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀s,|f s|≤C) :
    (∫s,f s ∂Measure.pi (fun _ : Fin (n+1) ↦ nu))=
      ∫old : Fin n→V,∫fresh : V,f (Fin.cons fresh old) ∂nu
        ∂Measure.pi (fun _ : Fin n ↦ nu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ V) 0
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ nu) 0).symm
  have hi : Integrable f (Measure.pi (fun _ : Fin (n+1) ↦ nu)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using hb s))
  have heq (p : V×(Fin n→V)) : e.symm p=Fin.cons p.1 p.2 := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
    rfl
  have hp : Integrable (fun p : V×(Fin n→V) ↦ f (Fin.cons p.1 p.2))
      (nu.prod (Measure.pi (fun _ : Fin n ↦ nu))) := by
    have hp0 := hmp.integrable_comp_of_integrable hi
    change Integrable (fun p : V×(Fin n→V) ↦ f (e.symm p))
      (nu.prod (Measure.pi (fun _ : Fin n ↦ nu))) at hp0
    simpa only [heq] using hp0
  have H := hmp.integral_comp e.symm.measurableEmbedding f
  change (∫p : V×(Fin n→V),f (e.symm p) ∂nu.prod (Measure.pi (fun _ : Fin n ↦ nu)))=
    ∫s,f s ∂Measure.pi (fun _ : Fin (n+1) ↦ nu) at H
  have H' : (∫s,f s ∂Measure.pi (fun _ : Fin (n+1) ↦ nu))=
      ∫p : V×(Fin n→V),f (Fin.cons p.1 p.2) ∂nu.prod (Measure.pi (fun _ : Fin n ↦ nu)) := by
    simpa only [heq] using H.symm
  exact H'.trans (integral_prod_symm _ hp)

theorem integral_joint_iid_cons (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω V) [IsMarkovKernel G] (n : ℕ)
    (f : Ω×(Fin (n+1)→V)→ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀p,|f p|≤C) :
    (∫p,f p ∂(d ⊗ₘ iid G (n+1)))=
      ∫p : Ω×(Fin n→V),(∫fresh : V,f (p.1,Fin.cons fresh p.2) ∂G p.1)
        ∂(d ⊗ₘ iid G n) := by
  have hi : Integrable f (d ⊗ₘ iid G (n+1)) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hb p))
  let kap : Kernel (Ω×(Fin n→V)) V := G.comap Prod.fst measurable_fst
  have hcons : Measurable (fun q : (Ω×(Fin n→V))×V ↦
      (q.1.1,(Fin.cons q.2 q.1.2 : Fin (n+1)→V))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((cons_measurable n).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hjm : Measurable (fun p : Ω×(Fin n→V) ↦ ∫fresh,f (p.1,Fin.cons fresh p.2) ∂G p.1) := by
    simpa only [kap,Kernel.comap_apply,Function.comp_def] using
      ((hf.comp hcons).stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable
  have hjb (p : Ω×(Fin n→V)) : |∫fresh,f (p.1,Fin.cons fresh p.2) ∂G p.1|≤C := by
    have H := norm_integral_le_of_norm_le_const (μ := G p.1)
      (f := fun fresh ↦ f (p.1,Fin.cons fresh p.2)) (C := C)
      (Eventually.of_forall (fun fresh ↦ by simpa only [Real.norm_eq_abs] using hb (p.1,Fin.cons fresh p.2)))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H
  have hj : Integrable (fun p : Ω×(Fin n→V) ↦ ∫fresh,f (p.1,Fin.cons fresh p.2) ∂G p.1)
      (d ⊗ₘ iid G n) :=
    Integrable.of_bound hjm.aestronglyMeasurable C
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hjb p))
  rw [Measure.integral_compProd hi,Measure.integral_compProd hj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w ↦ by
    simp only [iid_apply]
    exact integral_pi_cons (G w) n (fun s ↦ f (w,s))
      (hf.comp (measurable_const.prodMk measurable_id)) (fun s ↦ hb (w,s)))

end
end TensorPCA.NonRSLowerProofs.GGFiniteReplicaConsIntegration
