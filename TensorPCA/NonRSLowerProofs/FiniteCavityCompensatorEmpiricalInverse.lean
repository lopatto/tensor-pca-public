-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
public import Mathlib.Analysis.Convex.Jensen

/-! Finite iid sample inverse moments. Jensen is applied to the whole
empirical mean, so no spurious factor of the sample size is introduced. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
open MeasureTheory ProbabilityTheory Filter Set
open GaussianGibbsChangeOfMeasureProofs GGFiniteEmpiricalNormalizer
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def sampleMeanFeature (K : ℕ) (F : V→E) (s : Fin K→V) : E := (K : ℝ)⁻¹ • ∑i : Fin K,F (s i)

 theorem sampleMeanFeature_measurable (K : ℕ) {F : V→E} (hF : Measurable F) :
    Measurable (sampleMeanFeature K F) :=
  (Finset.measurable_sum _ (fun i _ ↦ hF.comp (measurable_pi_apply i))).const_smul _

 theorem sampleMeanFeature_norm_le {K : ℕ} (hK : 0<K) (F : V→E) (s : Fin K→V)
    {L : ℝ} (hs : ∀i,‖F (s i)‖≤L) : ‖sampleMeanFeature K F s‖≤L := by
  have hKR : 0<(K : ℝ) := by exact_mod_cast hK
  unfold sampleMeanFeature
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hKR.le)]
  calc
    _≤(K : ℝ)⁻¹*(∑i : Fin K,‖F (s i)‖) := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hKR.le)
    _≤(K : ℝ)⁻¹*(∑_i : Fin K,L) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hs i)) (inv_nonneg.mpr hKR.le)
    _=L := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp

 theorem sampleMeanFeature_norm_ae {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} {L : ℝ} (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    ∀ᵐs : Fin K→V ∂Measure.pi (fun _ : Fin K ↦ nu),‖sampleMeanFeature K F s‖≤L := by
  have hi (i : Fin K) : ∀ᵐs : Fin K→V ∂Measure.pi (fun _ : Fin K ↦ nu),‖F (s i)‖≤L :=
    (measurePreserving_eval (fun _ : Fin K ↦ nu) i).quasiMeasurePreserving.ae hFL
  exact (ae_all_iff.mpr hi).mono (fun s hs ↦ sampleMeanFeature_norm_le hK F s hs)

 theorem empirical_exp_measurable (K : ℕ) {F : V→E} (hF : Measurable F) :
    Measurable (fun p : E×(Fin K→V) ↦ empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2) := by
  unfold empiricalMean
  exact (Finset.measurable_sum _ (fun i _ ↦ (expMark_joint_measurable hF).comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))).div_const _

 theorem empirical_exp_pos {K : ℕ} (hK : 0<K) (F : V→E) (g : E) (s : Fin K→V) :
    0<empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  unfold empiricalMean
  exact div_pos (Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty) (by exact_mod_cast hK)

 theorem empirical_exp_jensen {K : ℕ} (hK : 0<K) (F : V→E) (g : E) (s : Fin K→V) :
    Real.exp (inner ℝ (sampleMeanFeature K F s) g)≤
      empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s := by
  have hKR : (K : ℝ)≠0 := by exact_mod_cast hK.ne'
  have hWeights : (∑_i : Fin K,(K : ℝ)⁻¹)=1 := by simp [hKR]
  have H := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _i : Fin K ↦ (K : ℝ)⁻¹) (p := fun i ↦ inner ℝ (F (s i)) g)
    (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg K)) hWeights (fun _ _ ↦ mem_univ _)
  simp only [smul_eq_mul,←Finset.mul_sum] at H
  simpa only [sampleMeanFeature,real_inner_smul_left,sum_inner,empiricalMean,div_eq_mul_inv,mul_comm] using H

 theorem empirical_inv_sq_le {K : ℕ} (hK : 0<K) (F : V→E) (g : E) (s : Fin K→V) :
    ((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s)⁻¹)^2≤
      Real.exp (inner ℝ ((-2 : ℝ) • sampleMeanFeature K F s) g) := by
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) (empirical_exp_jensen hK F g s)
  simp only [one_div,←Real.exp_neg] at hi
  have H := pow_le_pow_left₀ (inv_nonneg.mpr (empirical_exp_pos hK F g s).le) hi 2
  apply H.trans_eq
  rw [pow_two,←Real.exp_add,real_inner_smul_left]
  congr 1
  ring

 theorem empirical_inv_sq_gaussian_integrable {K : ℕ} (hK : 0<K) (F : V→E) (s : Fin K→V) :
    Integrable (fun g : E ↦ ((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s)⁻¹)^2) (stdGaussian E) := by
  have hm : Measurable (fun g : E ↦ ((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s)⁻¹)^2) := by
    unfold empiricalMean
    exact ((Finset.measurable_sum _ (fun i _ ↦ (continuous_const.inner continuous_id : Continuous (fun g : E ↦ inner ℝ (F (s i)) g)).measurable.exp)).div_const _).inv.pow_const 2
  have hi := integrable_exp_inner_add ((-2 : ℝ) • sampleMeanFeature K F s) 0
  simp only [add_zero] at hi
  apply hi.mono' hm.aestronglyMeasurable
  exact .of_forall (fun g ↦ by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using empirical_inv_sq_le hK F g s)

 theorem empirical_inv_sq_gaussian_integral_le {K : ℕ} (hK : 0<K) (F : V→E) (s : Fin K→V)
    {L : ℝ} (hL : 0≤L) (hs : ∀i,‖F (s i)‖≤L) :
    (∫g : E,((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s)⁻¹)^2 ∂stdGaussian E)≤Real.exp (2*L^2) := by
  have hi := integrable_exp_inner_add ((-2 : ℝ) • sampleMeanFeature K F s) 0
  simp only [add_zero] at hi
  have H := integral_mono (empirical_inv_sq_gaussian_integrable hK F s) hi (fun g ↦ empirical_inv_sq_le hK F g s)
  have he := integral_exp_inner_add ((-2 : ℝ) • sampleMeanFeature K F s) 0
  simp only [add_zero] at he
  rw [he] at H
  apply H.trans
  apply Real.exp_le_exp.mpr
  rw [norm_smul,Real.norm_eq_abs]
  norm_num
  have hn := sampleMeanFeature_norm_le hK F s hs
  nlinarith [sq_le_sq₀ (norm_nonneg (sampleMeanFeature K F s)) hL |>.mpr hn]

 theorem empirical_inv_memLp {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    MemLp (fun p : E×(Fin K→V) ↦ (empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)⁻¹)
      2 ((stdGaussian E).prod (Measure.pi (fun _ : Fin K ↦ nu))) := by
  have hm := ((empirical_exp_measurable K hF).inv.pow_const 2).stronglyMeasurable
  apply (memLp_two_iff_integrable_sq (empirical_exp_measurable K hF).inv.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (empirical_inv_sq_gaussian_integrable hK F),?_⟩
  have hp : AEStronglyMeasurable (fun s : Fin K→V ↦ ∫g : E,
      ‖((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) g)) s)⁻¹)^2‖ ∂stdGaussian E)
      (Measure.pi (fun _ : Fin K ↦ nu)) := hm.norm.integral_prod_left'.aestronglyMeasurable
  apply (integrable_const (Real.exp (2*L^2))).mono' hp
  have hAll : ∀ᵐs : Fin K→V ∂Measure.pi (fun _ : Fin K ↦ nu),∀i,‖F (s i)‖≤L :=
    ae_all_iff.mpr (fun i ↦ (measurePreserving_eval (fun _ : Fin K ↦ nu) i).quasiMeasurePreserving.ae hFL)
  filter_upwards [hAll] with s hs
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  exact empirical_inv_sq_gaussian_integral_le hK F s hL hs

 theorem empirical_inv_sq_integral_le {K : ℕ} (hK : 0<K) (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    (∫p : E×(Fin K→V),((empiricalMean K (fun x ↦ Real.exp (inner ℝ (F x) p.1)) p.2)⁻¹)^2
      ∂(stdGaussian E).prod (Measure.pi (fun _ : Fin K ↦ nu)))≤Real.exp (2*L^2) := by
  have hi := (empirical_inv_memLp hK nu hF hL hFL).integrable_sq
  rw [integral_prod_symm _ hi]
  have hAll : ∀ᵐs : Fin K→V ∂Measure.pi (fun _ : Fin K ↦ nu),∀i,‖F (s i)‖≤L :=
    ae_all_iff.mpr (fun i ↦ (measurePreserving_eval (fun _ : Fin K ↦ nu) i).quasiMeasurePreserving.ae hFL)
  have H := integral_mono_ae hi.integral_prod_right (integrable_const (Real.exp (2*L^2)))
    (hAll.mono (fun s hs ↦ empirical_inv_sq_gaussian_integral_le hK F s hL hs))
  simpa only [integral_const,probReal_univ,one_smul] using H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
