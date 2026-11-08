-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments

/-! Dimension-free square, inverse, and absolute-log bounds for the Gaussian
compensation mark exp(<F(x),g>). The Gaussian parameter is shared; these are joint
Gaussian-prior integrals.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMoments
open MeasureTheory ProbabilityTheory Filter
open FiniteCavityCompensatorGaussianMoments
open GaussianGibbsChangeOfMeasureProofs
open scoped RealInnerProductSpace
noncomputable section
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem integral_inner_sq (u : E) :
    (∫g : E,(inner ℝ u g)^2 ∂stdGaussian E)=‖u‖^2 := by
  have hLp : MemLp (fun g : E => inner ℝ u g) 2 (stdGaussian E) :=
    IsGaussian.memLp_two_id.const_inner u
  have H := variance_eq_sub hLp
  have hmean : (∫g : E,inner ℝ u g ∂stdGaussian E)=0 :=
    integral_strongDual_stdGaussian (innerSL ℝ u)
  have hvar : variance (fun g : E => inner ℝ u g) (stdGaussian E)=‖u‖^2 := by
    simpa only [coe_innerSL_apply,innerSL_apply_norm] using variance_dual_stdGaussian (innerSL ℝ u)
  simpa only [Pi.pow_apply,hmean,zero_pow two_ne_zero,sub_zero,hvar] using H.symm

theorem integral_abs_inner_le (u : E) :
    (∫g : E,|inner ℝ u g| ∂stdGaussian E)≤‖u‖ := by
  have hInner : MemLp (fun g : E => inner ℝ u g) 2 (stdGaussian E) :=
    IsGaussian.memLp_two_id.const_inner u
  have hLp : MemLp (fun g : E => |inner ℝ u g|) 2 (stdGaussian E) := by
    simpa only [Real.norm_eq_abs] using hInner.norm
  have H := variance_eq_sub hLp
  have HN := variance_nonneg (fun g : E => |inner ℝ u g|) (stdGaussian E)
  simp only [Pi.pow_apply,sq_abs,integral_inner_sq] at H
  rw [H] at HN
  have hmean : 0≤∫g : E,|inner ℝ u g| ∂stdGaussian E := integral_nonneg (fun _ => abs_nonneg _)
  nlinarith [norm_nonneg u]

theorem log_mark_joint_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) :
    Integrable (fun p : E×V => Real.log (Real.exp (inner ℝ (F p.2) p.1))) ((stdGaussian E).prod nu) := by
  simp only [Real.log_exp]
  have hm : Measurable (fun p : E×V => inner ℝ (F p.2) p.1) :=
    continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun x => (IsGaussian.memLp_two_id.const_inner (F x)).integrable one_le_two),?_⟩
  have hp : AEStronglyMeasurable (fun x : V => ∫g : E,‖inner ℝ (F x) g‖ ∂stdGaussian E) nu :=
    hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  apply (integrable_const D).mono' hp
  filter_upwards [hFD] with x hx
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  simpa only [Real.norm_eq_abs] using (integral_abs_inner_le (F x)).trans hx

theorem abs_log_mark_joint_integral_le (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) :
    (∫p : E×V,|Real.log (Real.exp (inner ℝ (F p.2) p.1))| ∂(stdGaussian E).prod nu)≤D := by
  have hi := (log_mark_joint_integrable nu hF hD hFD).abs
  rw [integral_prod_symm _ hi]
  have H := integral_mono_ae hi.integral_prod_right (integrable_const D) (by
    filter_upwards [hFD] with x hx
    simpa only [Real.log_exp] using (integral_abs_inner_le (F x)).trans hx)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem inverse_mark_joint_integrable_and_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) :
    Integrable (fun p : E×V => (Real.exp (inner ℝ (F p.2) p.1))⁻¹) ((stdGaussian E).prod nu) ∧
      (∫p : E×V,(Real.exp (inner ℝ (F p.2) p.1))⁻¹ ∂(stdGaussian E).prod nu)≤Real.exp (D^2/2) := by
  have hn : ∀ᵐx∂nu,‖-F x‖≤D := hFD.mono (fun _ hx => by simpa only [norm_neg] using hx)
  have hi2 := expMark_joint_sq_integrable nu hF.neg hD hn
  have hi := (memLp_two_iff_integrable_sq (expMark_joint_measurable hF.neg).aestronglyMeasurable).mpr hi2
  change MemLp (fun p : E×V => Real.exp (inner ℝ (-F p.2) p.1)) 2 ((stdGaussian E).prod nu) at hi
  have heq : (fun p : E×V => (Real.exp (inner ℝ (F p.2) p.1))⁻¹)=
      (fun p : E×V => Real.exp (inner ℝ (-F p.2) p.1)) := by
    funext p
    rw [inner_neg_left,Real.exp_neg]
  rw [heq]
  refine ⟨hi.integrable one_le_two,?_⟩
  rw [integral_prod_symm _ (hi.integrable one_le_two)]
  have H := integral_mono_ae (hi.integrable one_le_two).integral_prod_right
      (integrable_const (Real.exp (D^2/2))) (by
    filter_upwards [hFD] with x hx
    have HE := integral_exp_inner_add (-F x) 0
    simp only [add_zero,norm_neg] at HE
    rw [HE]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_le_sq₀ (norm_nonneg (F x)) hD |>.mpr hx]))
  simpa only [integral_const,probReal_univ,one_smul] using H

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMoments
