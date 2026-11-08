-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments

/-! Section integrability and the joint Gaussian second moment of the literal
cavity numerator mark for any probability law supported on unit spins. The
section bound is used only for integrability, never as the final error constant. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
open MeasureTheory ProbabilityTheory Set
open FiniteCavityIdealField
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem numeratorMark_le_exp_of_unit {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (g : CavityDisorder N M k)
    {x : Model.Vector N} (hx : x∈Model.unitSphere N) :
    numeratorMark k mu beta g x≤Real.exp
      ((Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖g‖) := by
  have hIn : Continuous (fun u : Model.Vector M ↦ (x,Real.sqrt (M : ℝ) • u)) :=
    continuous_const.prodMk (continuous_id.const_smul (Real.sqrt (M : ℝ)))
  have hScore : Continuous (fun u : Model.Vector M ↦
      inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g) :=
    ((cavityFeature_joint_continuous N M k mu beta).comp hIn).inner continuous_const
  have hI := Geometry.spherePrior_continuous_integrable hM _ (Real.continuous_exp.comp hScore)
  unfold numeratorMark
  have H := integral_mono_ae hI (integrable_const (Real.exp
      ((Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖g‖))) (by
    filter_upwards [Geometry.spherePrior_norm_ae hM] with u hu
    apply Real.exp_le_exp.mpr
    have h := (le_abs_self _).trans (abs_real_inner_le_norm
      (cavityFeature k mu beta (Real.sqrt (M : ℝ) • u) x) g)
    rw [cavityFeature_norm k hmu beta _ hx,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one] at h
    exact h)
  simpa only [integral_const,probReal_univ,one_smul,Function.comp_def] using H

 theorem numeratorMark_memLp_spin {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx ∂nu,x∈Model.unitSphere N) (g : CavityDisorder N M k) :
    MemLp (numeratorMark k mu beta g) 2 nu := by
  have hInput : Measurable (fun x : Model.Vector N ↦ (g,x)) := measurable_const.prodMk measurable_id
  have hComp := (numeratorMark_joint_measurable N M k mu beta).comp hInput
  have hm : Measurable (numeratorMark k mu beta g) := by
    simpa only [Function.comp_def] using hComp
  apply MemLp.of_bound hm.aestronglyMeasurable (Real.exp
    ((Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖g‖))
  filter_upwards [hnu] with x hx
  rw [Real.norm_of_nonneg (le_trans (by norm_num : (0 : ℝ)≤1) (numeratorMark_one_le hM k mu beta g x))]
  exact numeratorMark_le_exp_of_unit hM k hmu beta g hx

 theorem numeratorMark_joint_sq_integrable {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx ∂nu,x∈Model.unitSphere N) :
    Integrable (fun p : CavityDisorder N M k×Model.Vector N ↦ (numeratorMark k mu beta p.1 p.2)^2)
      ((stdGaussian (CavityDisorder N M k)).prod nu) := by
  have hm := ((numeratorMark_joint_measurable N M k mu beta).pow_const 2).stronglyMeasurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨hnu.mono (fun x hx ↦ numeratorMark_sq_integrable hM k hmu beta hx),?_⟩
  have hparam : AEStronglyMeasurable (fun x : Model.Vector N ↦
      ∫g : CavityDisorder N M k,‖(numeratorMark k mu beta g x)^2‖ ∂stdGaussian (CavityDisorder N M k)) nu :=
    hm.norm.integral_prod_left'.aestronglyMeasurable
  apply (integrable_const (Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1))).mono' hparam
  filter_upwards [hnu] with x hx
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using numeratorMark_gaussian_second_moment hM k hmu beta hx

 theorem numeratorMark_joint_second_moment {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx ∂nu,x∈Model.unitSphere N) :
    (∫p : CavityDisorder N M k×Model.Vector N,(numeratorMark k mu beta p.1 p.2)^2
      ∂(stdGaussian (CavityDisorder N M k)).prod nu)≤
      Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1) := by
  have hi := numeratorMark_joint_sq_integrable hM k hmu beta nu hnu
  rw [integral_prod_symm _ hi]
  have H := integral_mono_ae hi.integral_prod_right
    (integrable_const (Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)))
    (hnu.mono (fun x hx ↦ numeratorMark_gaussian_second_moment hM k hmu beta hx))
  simpa only [integral_const,probReal_univ,one_smul,Function.comp_def] using H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
