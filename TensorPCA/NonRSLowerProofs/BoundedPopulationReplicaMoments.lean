-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSUpperProofs.GaussianReplicaKernel
public import Mathlib.MeasureTheory.Integral.Pi

/-! Exact bounded population moments as IID-replica product moments. Independent mark
noise is integrated before the old-spin test is formed.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedPopulationReplicaMoments
open MeasureTheory ProbabilityTheory
open NonRSUpperProofs.GaussianReplicaKernel
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω W V : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace V]

theorem population_power_eq_replica_product (nu : Measure V) [IsProbabilityMeasure nu]
    (j : ℕ) (Z : V→ℝ) :
    (∫v,Z v∂nu)^j=(∫s : Fin j→V,∏i : Fin j,Z (s i)∂Measure.pi (fun _ => nu)) := by
  simpa only [Fintype.card_fin] using (integral_fintype_prod_eq_pow (ι := Fin j) Z).symm

theorem product_mark_measurable (j : ℕ) {Z : W→V→ℝ}
    (hZ : Measurable (fun p : W×V => Z p.1 p.2)) :
    Measurable (fun p : W×(Fin j→V) => ∏i : Fin j,Z p.1 (p.2 i)) := by
  apply Finset.measurable_prod
  intro i _
  exact hZ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem product_mark_mem (j : ℕ) {Z : W→V→ℝ} {a : ℝ} (ha : 0≤a)
    (hb : ∀w v,0≤Z w v ∧ Z w v≤a) (w : W) (s : Fin j→V) :
    0≤(∏i : Fin j,Z w (s i)) ∧ (∏i : Fin j,Z w (s i))≤a^j := by
  refine ⟨Finset.prod_nonneg (fun i _ => (hb w (s i)).1),?_⟩
  calc
    _ ≤ ∏i : Fin j,a := Finset.prod_le_prod₀ (fun i _ => (hb w (s i)).1) (fun i _ => (hb w (s i)).2)
    _ = a^j := by simp

theorem product_mark_integrable {j : ℕ} (mu : Measure (W×(Fin j→V))) [IsProbabilityMeasure mu]
    {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2)) {a : ℝ} (ha : 0≤a)
    (hb : ∀w v,0≤Z w v ∧ Z w v≤a) :
    Integrable (fun p : W×(Fin j→V) => ∏i : Fin j,Z p.1 (p.2 i)) mu := by
  apply Integrable.of_bound (product_mark_measurable j hZ).aestronglyMeasurable (a^j)
  exact ae_of_all _ (fun p => by
    rw [Real.norm_of_nonneg (product_mark_mem j ha hb p.1 p.2).1]
    exact (product_mark_mem j ha hb p.1 p.2).2)

theorem cavity_product_mean_measurable (gamma : Measure W) [IsProbabilityMeasure gamma]
    (j : ℕ) {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2)) :
    Measurable (fun s : Fin j→V => ∫w,∏i : Fin j,Z w (s i)∂gamma) := by
  have HM := (product_mark_measurable j hZ).comp measurable_swap
  exact HM.stronglyMeasurable.integral_prod_right'.measurable

theorem cavity_product_mean_mem (gamma : Measure W) [IsProbabilityMeasure gamma]
    (j : ℕ) {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) (s : Fin j→V) :
    0≤(∫w,∏i : Fin j,Z w (s i)∂gamma) ∧ (∫w,∏i : Fin j,Z w (s i)∂gamma)≤a^j := by
  have hm : Measurable (fun w : W => ∏i : Fin j,Z w (s i)) :=
    (product_mark_measurable j hZ).comp (measurable_id.prodMk measurable_const)
  have hi : Integrable (fun w => ∏i : Fin j,Z w (s i)) gamma := by
    apply Integrable.of_bound hm.aestronglyMeasurable (a^j)
    exact ae_of_all _ (fun w => by
      rw [Real.norm_of_nonneg (product_mark_mem j ha hb w s).1]
      exact (product_mark_mem j ha hb w s).2)
  refine ⟨integral_nonneg (fun w => (product_mark_mem j ha hb w s).1),?_⟩
  have H := integral_mono hi (integrable_const (a^j)) (fun w => (product_mark_mem j ha hb w s).2)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem population_power_cavity_swap (nu : Measure V) [IsProbabilityMeasure nu]
    (gamma : Measure W) [IsProbabilityMeasure gamma] (j : ℕ)
    {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) :
    (∫w,(∫v,Z w v∂nu)^j∂gamma)=
      ∫s : Fin j→V,(∫w,∏i : Fin j,Z w (s i)∂gamma)∂Measure.pi (fun _ => nu) := by
  simp_rw [population_power_eq_replica_product nu j]
  exact integral_integral_swap (product_mark_integrable
    (gamma.prod (Measure.pi (fun _ : Fin j => nu))) hZ ha hb)

theorem population_mean_measurable (G : Kernel Ω V) [IsMarkovKernel G]
    {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2)) :
    Measurable (fun p : Ω×W => ∫v,Z p.2 v∂G p.1) := by
  let kap : Kernel (Ω×W) V := G.comap Prod.fst measurable_fst
  have HM : Measurable (fun p : (Ω×W)×V => Z p.1.2 p.2) :=
    hZ.comp (measurable_fst.snd.prodMk measurable_snd)
  simpa only [kap,Kernel.comap_apply] using
    (HM.stronglyMeasurable.integral_kernel_prod_right' (κ := kap)).measurable

theorem population_mean_mem (G : Kernel Ω V) [IsMarkovKernel G]
    {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) (omega : Ω) (w : W) :
    0≤(∫v,Z w v∂G omega) ∧ (∫v,Z w v∂G omega)≤a := by
  have HM := hZ.comp (measurable_const.prodMk measurable_id : Measurable (fun v : V => (w,v)))
  have hi : Integrable (Z w) (G omega) := by
    apply Integrable.of_bound HM.aestronglyMeasurable a
    exact ae_of_all _ (fun v => by change ‖Z w v‖≤a; rw [Real.norm_of_nonneg (hb w v).1]; exact (hb w v).2)
  refine ⟨integral_nonneg (fun v => (hb w v).1),?_⟩
  have H := integral_mono hi (integrable_const a) (fun v => (hb w v).2)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem population_power_joint_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (gamma : Measure W) [IsProbabilityMeasure gamma] (G : Kernel Ω V) [IsMarkovKernel G]
    (j : ℕ) {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) :
    Integrable (fun p : Ω×W => (∫v,Z p.2 v∂G p.1)^j) (d.prod gamma) := by
  apply Integrable.of_bound ((population_mean_measurable G hZ).pow_const j).aestronglyMeasurable (a^j)
  apply ae_of_all
  intro p
  have H := population_mean_mem G hZ ha hb p.1 p.2
  rw [Real.norm_of_nonneg (pow_nonneg H.1 j)]
  exact pow_le_pow_left₀ H.1 H.2 j

theorem cavity_product_joint_integrable (d : Measure Ω) [IsProbabilityMeasure d]
    (gamma : Measure W) [IsProbabilityMeasure gamma] (G : Kernel Ω V) [IsMarkovKernel G]
    (j : ℕ) {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) :
    Integrable (fun p : Ω×(Fin j→V) => ∫w,∏i : Fin j,Z w (p.2 i)∂gamma) (d ⊗ₘiid G j) := by
  apply Integrable.of_bound
    ((cavity_product_mean_measurable gamma j hZ).comp measurable_snd).aestronglyMeasurable (a^j)
  apply ae_of_all
  intro p
  change ‖∫w,∏i : Fin j,Z w (p.2 i)∂gamma‖≤a^j
  rw [Real.norm_of_nonneg (cavity_product_mean_mem gamma j hZ ha hb p.2).1]
  exact (cavity_product_mean_mem gamma j hZ ha hb p.2).2

/-- Conditional population moments under the replica kernel. Independent cavity
randomness is averaged before the replica test is formed.
-/
theorem population_power_eq_joint_replica_product (d : Measure Ω) [IsProbabilityMeasure d]
    (gamma : Measure W) [IsProbabilityMeasure gamma] (G : Kernel Ω V) [IsMarkovKernel G]
    (j : ℕ) {Z : W→V→ℝ} (hZ : Measurable (fun p : W×V => Z p.1 p.2))
    {a : ℝ} (ha : 0≤a) (hb : ∀w v,0≤Z w v ∧ Z w v≤a) :
    (∫omega,(∫w,(∫v,Z w v∂G omega)^j∂gamma)∂d)=
      ∫p : Ω×(Fin j→V),(∫w,∏i : Fin j,Z w (p.2 i)∂gamma)∂d ⊗ₘiid G j := by
  rw [Measure.integral_compProd (cavity_product_joint_integrable d gamma G j hZ ha hb)]
  apply integral_congr_ae
  apply ae_of_all
  intro omega
  dsimp only
  rw [iid_apply]
  exact population_power_cavity_swap (G omega) gamma j hZ ha hb

theorem deficit_mean_eq (nu : Measure V) [IsProbabilityMeasure nu]
    {Y : V→ℝ} (hY : Integrable Y nu) (cap : ℝ) :
    1-(∫v,Y v∂nu)/cap=(∫v,1-Y v/cap∂nu) := by
  rw [integral_sub (integrable_const 1) (hY.div_const cap),integral_const,probReal_univ,one_smul,integral_div]

end
end TensorPCA.NonRSLowerProofs.BoundedPopulationReplicaMoments
