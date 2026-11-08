-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLaw
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.Module

/-! The spin marginal of the tilted Gaussian endpoint, with both independent Gaussian
noises retained until their law is identified.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTilt OneStepGaussianTiltLaw GaussianMomentProofs GaussianDensityProofs
open scoped RealInnerProductSpace Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem linear_exp_integrable (u : E) (a : ℝ) :
    Integrable (fun x => Real.exp (a*inner ℝ u x)) (stdGaussian E) := by
  simpa only [real_inner_smul_left,sub_self,zero_div,zero_mul,sub_zero] using
    integrable_exp_quadratic (by norm_num : (0 : ℝ) < 1) (a • u)

private theorem sum_exp_pointwise (d u : E) (a b : ℝ) :
    (fun p : E×E => Real.exp (inner ℝ u (d+a • p.1+b • p.2))) =
      (fun p => Real.exp (inner ℝ u d)*
        (Real.exp (a*inner ℝ u p.1)*Real.exp (b*inner ℝ u p.2))) := by
  funext p
  rw [inner_add_right,inner_add_right,inner_smul_right,inner_smul_right,
    Real.exp_add,Real.exp_add]
  ring

theorem sum_gaussian_exp_integrable (d u : E) (a b : ℝ) :
    Integrable (fun p : E×E => Real.exp (inner ℝ u (d+a • p.1+b • p.2)))
      ((stdGaussian E).prod (stdGaussian E)) := by
  rw [sum_exp_pointwise]
  exact ((linear_exp_integrable u a).mul_prod (linear_exp_integrable u b)).const_mul _

theorem sum_gaussian_laplace (d u : E) (a b : ℝ) :
    (∫ p : E×E, Real.exp (inner ℝ u (d+a • p.1+b • p.2))
      ∂(stdGaussian E).prod (stdGaussian E)) =
        Real.exp (inner ℝ u d+(a^2+b^2)*‖u‖^2/2) := by
  rw [sum_exp_pointwise,integral_const_mul,integral_prod_mul
    (fun g : E => Real.exp (a*inner ℝ u g)) (fun g : E => Real.exp (b*inner ℝ u g)),
    integral_exp_inner_stdGaussian,integral_exp_inner_stdGaussian,
    ← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem affine_stdGaussian_laplace (d u : E) (s : ℝ) :
    (∫ x, Real.exp (inner ℝ u x)
      ∂(stdGaussian E).map (fun g => d+s • g)) =
        Real.exp (inner ℝ u d+s^2*‖u‖^2/2) := by
  rw [integral_map (by fun_prop : Measurable (fun g : E => d+s • g)).aemeasurable
    (by fun_prop : Measurable (fun x : E => Real.exp (inner ℝ u x))).aestronglyMeasurable]
  have hfun : (fun g : E => Real.exp (inner ℝ u (d+s • g))) =
      (fun g => Real.exp (inner ℝ u d)*Real.exp (s*inner ℝ u g)) := by
    funext g
    rw [inner_add_right,inner_smul_right,Real.exp_add]
  rw [hfun,integral_const_mul,integral_exp_inner_stdGaussian,← Real.exp_add]

/-- Sum of two genuinely independent standard Gaussian vectors, including
its exact mean and scalar variance. -/
theorem sum_gaussian_law (d : E) (a b : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun p : E×E => d+a • p.1+b • p.2) =
        (stdGaussian E).map (fun g => d+Real.sqrt (a^2+b^2) • g) := by
  let mu := ((stdGaussian E).prod (stdGaussian E)).map
    (fun p : E×E => d+a • p.1+b • p.2)
  let nu := (stdGaussian E).map (fun g => d+Real.sqrt (a^2+b^2) • g)
  have hF : Measurable (fun p : E×E => d+a • p.1+b • p.2) := by fun_prop
  have hG : Measurable (fun g : E => d+Real.sqrt (a^2+b^2) • g) := by fun_prop
  haveI : IsProbabilityMeasure mu := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr
    inferInstance
  haveI : IsProbabilityMeasure nu := (Measure.isProbabilityMeasure_map_iff hG.aemeasurable).mpr
    inferInstance
  change mu = nu
  apply Measure.ext_of_charFun
  funext u
  have hm : mgf (fun x => inner ℝ u x) mu = mgf (fun x => inner ℝ u x) nu := by
    funext t
    have hM : Measurable (fun x : E => Real.exp (inner ℝ (t • u) x)) := by fun_prop
    have hLeft : (∫ x, Real.exp (inner ℝ (t • u) x) ∂mu) =
        Real.exp (inner ℝ (t • u) d+(a^2+b^2)*‖t • u‖^2/2) := by
      rw [show mu = _ from rfl,integral_map hF.aemeasurable hM.aestronglyMeasurable]
      exact sum_gaussian_laplace d (t • u) a b
    have hRight := affine_stdGaussian_laplace d (t • u) (Real.sqrt (a^2+b^2))
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))] at hRight
    simpa only [mgf,real_inner_smul_left] using hLeft.trans hRight.symm
  have hs : integrableExpSet (fun x => inner ℝ u x) mu = univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t*inner ℝ u x)) mu
    have hM : Measurable (fun x : E => Real.exp (inner ℝ (t • u) x)) := by fun_prop
    have H : Integrable (fun x => Real.exp (inner ℝ (t • u) x)) mu :=
      (integrable_map_measure hM.aestronglyMeasurable hF.aemeasurable).mpr
        (sum_gaussian_exp_integrable d (t • u) a b)
    simpa only [real_inner_smul_left] using H
  have H := eqOn_complexMGF_of_mgf hm (show (Complex.I : ℂ) ∈
      {s | s.re ∈ interior (integrableExpSet (fun x => inner ℝ u x) mu)} by simp [hs])
  simpa only [complexMGF,charFun_apply,real_inner_comm u,mul_comm Complex.I] using H

/-- The spin marginal under the tilted first Gaussian and the independent conditional-
spin Gaussian.
-/
theorem tilted_joint_spin_law {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    (((stdGaussian E).tilted (tiltExponent B v m y)).prod (stdGaussian E)).map
      (fun p : E×E => (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2) =
        (stdGaussian E).map (fun g => (B-m*v)⁻¹ • y+
          Real.sqrt (1/B+v/(B*(B-m*v))) • g) := by
  let T : E → E := fun g => (m*Real.sqrt v/(B-m*v)) • y+Real.sqrt (B/(B-m*v)) • g
  let F : E×E → E := fun p => (1/B) • (y+Real.sqrt v • p.1)+(Real.sqrt B)⁻¹ • p.2
  rw [tilted_endpoint_eq_affine_gaussian hB hv hD]
  have hProd : ((stdGaussian E).map T).prod (stdGaussian E) =
      ((stdGaussian E).prod (stdGaussian E)).map (Prod.map T id) := by
    simpa only [Measure.map_id] using (Measure.map_prod_map (stdGaussian E)
      (stdGaussian E) (by fun_prop : Measurable T) measurable_id)
  change (((stdGaussian E).map T).prod (stdGaussian E)).map F = _
  rw [hProd,Measure.map_map (by fun_prop : Measurable F)
    (by fun_prop : Measurable (Prod.map T id))]
  have hMean : 1/B+(Real.sqrt v/B)*(m*Real.sqrt v/(B-m*v)) = (B-m*v)⁻¹ := by
    field_simp [hB.ne',hD.ne']
    rw [Real.sq_sqrt hv]
    ring
  have hFun : F ∘ Prod.map T id = fun p : E×E =>
      (B-m*v)⁻¹ • y+((Real.sqrt v/B)*Real.sqrt (B/(B-m*v))) • p.1+
        (Real.sqrt B)⁻¹ • p.2 := by
    funext p
    simp only [Function.comp_apply,F,Prod.map_fst,Prod.map_snd,T,id_eq]
    calc
      _ = (1/B+(Real.sqrt v/B)*(m*Real.sqrt v/(B-m*v))) • y+
          ((Real.sqrt v/B)*Real.sqrt (B/(B-m*v))) • p.1+(Real.sqrt B)⁻¹ • p.2 := by module
      _ = _ := by rw [hMean]
  rw [hFun,sum_gaussian_law]
  have hVar : ((Real.sqrt v/B)*Real.sqrt (B/(B-m*v)))^2+((Real.sqrt B)⁻¹)^2 =
      1/B+v/(B*(B-m*v)) := by
    rw [mul_pow,div_pow,Real.sq_sqrt hv,Real.sq_sqrt (div_pos hB hD).le,
      inv_pow,Real.sq_sqrt hB.le]
    field_simp [hB.ne',hD.ne']
    ring
  rw [hVar]

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltJoint
