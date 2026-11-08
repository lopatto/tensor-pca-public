-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMoments
public import Mathlib.Analysis.Convex.Integral

/-! Mixed Gaussian moments for SECTIONWISE compensation transforms.
Two independently sampled prior points share the same Gaussian parameter.
This controls the Jensen factor exp(E_x |log Y_gx|) without replacing the
conditional transform by a transform of the joint law. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMixed
open MeasureTheory ProbabilityTheory Filter Set
open FiniteCavityCompensatorGaussianMoments GaussianGibbsChangeOfMeasureProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem exp_joint_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) :
    Integrable (fun p : E×V => Real.exp (inner ℝ (F p.2) p.1)) ((stdGaussian E).prod nu) ∧
      (∫p : E×V,Real.exp (inner ℝ (F p.2) p.1) ∂(stdGaussian E).prod nu)≤Real.exp (D^2/2) := by
  have hi := (memLp_two_iff_integrable_sq (expMark_joint_measurable hF).aestronglyMeasurable).mpr
    (expMark_joint_sq_integrable nu hF hD hFD)
  refine ⟨hi.integrable one_le_two,?_⟩
  rw [integral_prod_symm _ (hi.integrable one_le_two)]
  have H := integral_mono_ae (hi.integrable one_le_two).integral_prod_right
      (integrable_const (Real.exp (D^2/2))) (by
    filter_upwards [hFD] with x hx
    have HE := integral_exp_inner_add (F x) 0
    simp only [add_zero] at HE
    rw [HE]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_le_sq₀ (norm_nonneg (F x)) hD |>.mpr hx]))
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem exponential_mean_product_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) (s t : ℝ) :
    let J := fun g : E => (∫x,Real.exp (s*inner ℝ (F x) g) ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)
    Integrable J (stdGaussian E) ∧ (∫g,J g ∂stdGaussian E)≤Real.exp (((|s|+|t|)*D)^2/2) := by
  dsimp only
  let H : V×V→E := fun xy => s • F xy.1+t • F xy.2
  have hH : Measurable H := (hF.comp measurable_fst).const_smul s |>.add ((hF.comp measurable_snd).const_smul t)
  have hHD : ∀ᵐxy∂nu.prod nu,‖H xy‖≤(|s|+|t|)*D := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hFD,Measure.quasiMeasurePreserving_snd.ae hFD] with xy hx hy
    calc
      _ ≤ ‖s • F xy.1‖+‖t • F xy.2‖ := norm_add_le _ _
      _ = |s| *‖F xy.1‖+|t| *‖F xy.2‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ |s| *D+|t| *D := add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
      _ = _ := by ring
  have hi := exp_joint_bound (nu.prod nu) hH (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hD) hHD
  have heq (g : E) : (∫x,Real.exp (s*inner ℝ (F x) g) ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)=
      ∫xy,Real.exp (inner ℝ (H xy) g) ∂nu.prod nu := by
    rw [← integral_prod_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun xy => by simp only [H,inner_add_left,real_inner_smul_left,Real.exp_add])
  refine ⟨hi.1.integral_prod_left.congr (ae_of_all _ (fun g => (heq g).symm)),?_⟩
  simp_rw [heq]
  rw [← integral_prod _ hi.1]
  exact hi.2

theorem jensen_factor_mixed_bound (nu : Measure V) [IsProbabilityMeasure nu]
    {F : V→E} (hF : Measurable F) {D : ℝ} (hD : 0≤D) (hFD : ∀ᵐx∂nu,‖F x‖≤D) (t : ℝ) :
    let J := fun g : E => Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)
    Integrable J (stdGaussian E) ∧ (∫g,J g ∂stdGaussian E)≤2*Real.exp (((1+|t|)*D)^2/2) := by
  dsimp only
  have h1 := exponential_mean_product_bound nu hF hD hFD 1 t
  have hn := exponential_mean_product_bound nu hF hD hFD (-1) t
  dsimp only at h1 hn
  have hmI : Measurable (fun p : E×V => inner ℝ (F p.2) p.1) :=
    continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)
  have hmAbs : Measurable (fun p : E×V => |inner ℝ (F p.2) p.1|) := by
    simpa only [Real.norm_eq_abs] using hmI.norm
  have hmA : Measurable (fun g : E => ∫x,|inner ℝ (F x) g| ∂nu) :=
    hmAbs.stronglyMeasurable.integral_prod_right'.measurable
  have hmB : Measurable (fun g : E => ∫x,Real.exp (t*inner ℝ (F x) g) ∂nu) :=
    (hmI.const_mul t).exp.stronglyMeasurable.integral_prod_right'.measurable
  have hb (g : E) : Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)≤
      (∫x,Real.exp (1*inner ℝ (F x) g) ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)+
      (∫x,Real.exp ((-1)*inner ℝ (F x) g) ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu) := by
    have hmInner : Measurable (fun x : V => inner ℝ (F x) g) :=
      continuous_inner.measurable.comp (hF.prodMk measurable_const)
    have hmInnerAbs : Measurable (fun x : V => |inner ℝ (F x) g|) := by
      simpa only [Real.norm_eq_abs] using hmInner.norm
    have hAbs : Integrable (fun x => |inner ℝ (F x) g|) nu := by
      apply Integrable.of_bound hmInnerAbs.aestronglyMeasurable (D*‖g‖)
      filter_upwards [hFD] with x hx
      rw [Real.norm_eq_abs,abs_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    have hEAbs : Integrable (fun x => Real.exp |inner ℝ (F x) g|) nu := by
      apply Integrable.of_bound hmInnerAbs.exp.aestronglyMeasurable (Real.exp (D*‖g‖))
      filter_upwards [hFD] with x hx
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
    have hEP := (expMark_memLp nu hF hFD g).integrable one_le_two
    have hnFD : ∀ᵐx∂nu,‖(-F) x‖≤D := hFD.mono (fun _ hx => by simpa only [Pi.neg_apply,norm_neg] using hx)
    have hEN := (expMark_memLp nu hF.neg hnFD g).integrable one_le_two
    change Integrable (fun x => Real.exp (inner ℝ (-F x) g)) nu at hEN
    have he : Real.exp (∫x,|inner ℝ (F x) g| ∂nu)≤
        (∫x,Real.exp (1*inner ℝ (F x) g) ∂nu)+(∫x,Real.exp ((-1)*inner ℝ (F x) g) ∂nu) := by
      have HJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
        (ae_of_all nu (fun _ => mem_univ _)) hAbs hEAbs
      have H : (∫x,Real.exp |inner ℝ (F x) g| ∂nu)≤
          (∫x,Real.exp (inner ℝ (F x) g) ∂nu)+(∫x,Real.exp (inner ℝ (-F x) g) ∂nu) := by
        rw [← integral_add hEP hEN]
        apply integral_mono hEAbs (hEP.add hEN)
        intro x
        simp only [Pi.add_apply,inner_neg_left]
        by_cases hx : 0 ≤ inner ℝ (F x) g
        · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-inner ℝ (F x) g)]
        · rw [abs_of_nonpos (le_of_not_ge hx)]; linarith [Real.exp_pos (inner ℝ (F x) g)]
      simpa only [one_mul,neg_one_mul,inner_neg_left] using HJ.trans H
    simpa only [add_mul] using mul_le_mul_of_nonneg_right he (integral_nonneg (fun _ => (Real.exp_pos _).le))
  have hi : Integrable (fun g : E => Real.exp (∫x,|inner ℝ (F x) g| ∂nu)*(∫y,Real.exp (t*inner ℝ (F y) g) ∂nu)) (stdGaussian E) := by
    apply (h1.1.add hn.1).mono' (hmA.exp.mul hmB).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      simp only [Pi.mul_apply,Pi.add_apply]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le)))]
      exact hb g)
  refine ⟨hi,?_⟩
  have H := integral_mono hi (h1.1.add hn.1) hb
  simp only [Pi.add_apply] at H
  rw [integral_add h1.1 hn.1] at H
  have HB := add_le_add h1.2 hn.2
  norm_num only [abs_one,abs_neg,abs_one] at HB
  exact H.trans (by simpa only [two_mul] using HB)

end
end TensorPCA.NonRSLowerProofs.CompensationMarkClippingGaussianMixed
