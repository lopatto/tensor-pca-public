-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityJointEmpiricalMoments
public import TensorPCA.GaussianGibbsChangeOfMeasureProofs

/-! Gaussian exponential marks and inverse partition moments. Jensen retains the mean
feature; the final constants depend only on its norm bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
open MeasureTheory ProbabilityTheory Filter Set
open GaussianGibbsChangeOfMeasureProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {V E : Type*} [MeasurableSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

 theorem expMark_joint_measurable {F : V→E} (hF : Measurable F) :
    Measurable (fun p : E×V ↦ Real.exp (inner ℝ (F p.2) p.1)) :=
  (continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).exp

 theorem expMark_memLp (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hFL : ∀ᵐx ∂nu,‖F x‖≤L) (g : E) :
    MemLp (fun x ↦ Real.exp (inner ℝ (F x) g)) 2 nu := by
  have hm : Measurable (fun x ↦ Real.exp (inner ℝ (F x) g)) :=
    (continuous_inner.measurable.comp (hF.prodMk measurable_const)).exp
  apply MemLp.of_bound hm.aestronglyMeasurable (Real.exp (L*‖g‖))
  filter_upwards [hFL] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hx (norm_nonneg _))))

 theorem expMark_gaussian_sq_integrable (F : V→E) (x : V) :
    Integrable (fun g : E ↦ (Real.exp (inner ℝ (F x) g))^2) (stdGaussian E) := by
  have hi := integrable_exp_inner_add ((2 : ℝ) • F x) 0
  convert hi using 1
  funext g
  rw [real_inner_smul_left,add_zero,two_mul,Real.exp_add,pow_two]

 theorem expMark_gaussian_sq_integral (F : V→E) (x : V) :
    (∫g : E,(Real.exp (inner ℝ (F x) g))^2 ∂stdGaussian E)=Real.exp (2*‖F x‖^2) := by
  have H := integral_exp_inner_add ((2 : ℝ) • F x) 0
  have he : (fun g : E ↦ Real.exp (inner ℝ ((2 : ℝ) • F x) g+0))=
      (fun g : E ↦ (Real.exp (inner ℝ (F x) g))^2) := by
    funext g
    rw [real_inner_smul_left,add_zero,two_mul,Real.exp_add,pow_two]
  rw [he,norm_smul,Real.norm_eq_abs] at H
  norm_num at H
  convert H using 1
  congr 1
  ring

 theorem expMark_joint_sq_integrable (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    Integrable (fun p : E×V ↦ (Real.exp (inner ℝ (F p.2) p.1))^2) ((stdGaussian E).prod nu) := by
  have hm := ((expMark_joint_measurable hF).pow_const 2).stronglyMeasurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (expMark_gaussian_sq_integrable F),?_⟩
  have hp : AEStronglyMeasurable (fun x : V ↦ ∫g : E,‖(Real.exp (inner ℝ (F x) g))^2‖ ∂stdGaussian E) nu :=
    hm.norm.integral_prod_left'.aestronglyMeasurable
  apply (integrable_const (Real.exp (2*L^2))).mono' hp
  filter_upwards [hFL] with x hx
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  simp only [Real.norm_of_nonneg (sq_nonneg _)]
  rw [expMark_gaussian_sq_integral]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_le_sq₀ (norm_nonneg (F x)) hL |>.mpr hx]

 theorem expMark_joint_sq_integral_le (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    (∫p : E×V,(Real.exp (inner ℝ (F p.2) p.1))^2 ∂(stdGaussian E).prod nu)≤Real.exp (2*L^2) := by
  have hi := expMark_joint_sq_integrable nu hF hL hFL
  rw [integral_prod_symm _ hi]
  have H := integral_mono_ae hi.integral_prod_right (integrable_const (Real.exp (2*L^2))) (by
    filter_upwards [hFL] with x hx
    rw [expMark_gaussian_sq_integral]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_le_sq₀ (norm_nonneg (F x)) hL |>.mpr hx]))
  simpa only [integral_const,probReal_univ,one_smul] using H

 theorem population_pos (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hFL : ∀ᵐx ∂nu,‖F x‖≤L) (g : E) :
    0<(∫x,Real.exp (inner ℝ (F x) g) ∂nu) := by
  exact integral_exp_pos ((expMark_memLp nu hF hFL g).integrable (by norm_num))

 theorem population_measurable (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) : Measurable (fun g : E ↦ ∫x,Real.exp (inner ℝ (F x) g) ∂nu) :=
  (expMark_joint_measurable hF).stronglyMeasurable.integral_prod_right'.measurable

 theorem population_inv_sq_le (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hFL : ∀ᵐx ∂nu,‖F x‖≤L) (g : E) :
    ((∫x,Real.exp (inner ℝ (F x) g) ∂nu)⁻¹)^2≤
      Real.exp (inner ℝ ((-2 : ℝ) • (∫x,F x ∂nu)) g) := by
  have hj := normalizer_jensen_lower nu F (fun _ ↦ 0) hF measurable_const hFL
    (.of_forall (fun _ ↦ by simp : ∀x : V, |(0 : ℝ)|≤0)) g
  simp only [normalizer,exponent,add_zero,integral_zero] at hj
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) hj
  simp only [one_div,←Real.exp_neg] at hi
  have H := pow_le_pow_left₀ (inv_nonneg.mpr (population_pos nu hF hFL g).le) hi 2
  apply H.trans_eq
  rw [pow_two,←Real.exp_add,real_inner_smul_left]
  congr 1
  ring

 theorem population_inv_memLp (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    MemLp (fun g : E ↦ (∫x,Real.exp (inner ℝ (F x) g) ∂nu)⁻¹) 2 (stdGaussian E) := by
  apply (memLp_two_iff_integrable_sq (population_measurable nu hF).inv.aestronglyMeasurable).mpr
  have hi := integrable_exp_inner_add ((-2 : ℝ) • (∫x,F x ∂nu)) 0
  simp only [add_zero] at hi
  apply hi.mono' ((population_measurable nu hF).inv.pow_const 2).aestronglyMeasurable
  exact .of_forall (fun g ↦ by simpa only [Real.norm_of_nonneg (sq_nonneg _),Pi.inv_apply] using population_inv_sq_le nu hF hFL g)

 theorem population_inv_sq_integral_le (nu : Measure V) [IsProbabilityMeasure nu] {F : V→E}
    (hF : Measurable F) {L : ℝ} (hL : 0≤L) (hFL : ∀ᵐx ∂nu,‖F x‖≤L) :
    (∫g : E,((∫x,Real.exp (inner ℝ (F x) g) ∂nu)⁻¹)^2 ∂stdGaussian E)≤Real.exp (2*L^2) := by
  have hi := integrable_exp_inner_add ((-2 : ℝ) • (∫x,F x ∂nu)) 0
  simp only [add_zero] at hi
  have H := integral_mono (population_inv_memLp nu hF hFL).integrable_sq hi (population_inv_sq_le nu hF hFL)
  have hnorm : ‖∫x,F x ∂nu‖≤L := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hFL
  have he := integral_exp_inner_add ((-2 : ℝ) • (∫x,F x ∂nu)) 0
  simp only [add_zero] at he
  rw [he] at H
  apply H.trans
  apply Real.exp_le_exp.mpr
  rw [norm_smul,Real.norm_eq_abs]
  norm_num
  nlinarith [sq_le_sq₀ (norm_nonneg (∫x,F x ∂nu)) hL |>.mpr hnorm]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensatorGaussianMoments
