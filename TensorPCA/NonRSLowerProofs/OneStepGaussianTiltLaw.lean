-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTilt

/-! Identification of the normalized quadratic tilt with its affine Gaussian law. Exact
Laplace transforms determine the finite-dimensional law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLaw
open MeasureTheory ProbabilityTheory Set Filter
open OneStepGaussianTilt GaussianMomentProofs GaussianDensityProofs
open scoped RealInnerProductSpace Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem quadratic_tilt_exp_inner_integrable {z : ℝ} (hz : 0 < z) (w u : E) :
    Integrable (fun x => Real.exp (inner ℝ u x))
      ((stdGaussian E).tilted (fun x => inner ℝ w x-(z-1)/2*‖x‖^2)) := by
  apply (integrable_tilted_iff (integrable_exp_quadratic hz w) _).mpr
  convert integrable_exp_quadratic hz (w+u) using 1
  funext x
  simp only [smul_eq_mul,← Real.exp_add,inner_add_left]
  congr 1
  ring

theorem quadratic_tilt_laplace {z : ℝ} (hz : 0 < z) (w u : E) :
    (∫ x, Real.exp (inner ℝ u x)
      ∂(stdGaussian E).tilted (fun x => inner ℝ w x-(z-1)/2*‖x‖^2)) =
        Real.exp (inner ℝ (z⁻¹ • w) u+‖u‖^2/(2*z)) := by
  rw [integral_exp_tilted]
  change (∫ x : E, Real.exp ((inner ℝ w x-(z-1)/2*‖x‖^2)+inner ℝ u x)
      ∂stdGaussian E)/(∫ x : E, Real.exp (inner ℝ w x-(z-1)/2*‖x‖^2)
        ∂stdGaussian E) = _
  have hFun : (fun x : E => Real.exp
      ((inner ℝ w x-(z-1)/2*‖x‖^2)+inner ℝ u x)) =
      (fun x => Real.exp (inner ℝ (w+u) x-(z-1)/2*‖x‖^2)) := by
    funext x
    simp only [Pi.add_apply,inner_add_left]
    congr 1
    ring
  rw [hFun,integral_exp_quadratic hz,integral_exp_quadratic hz,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos hz _).ne',← Real.exp_sub]
  congr 1
  rw [norm_add_sq_real,real_inner_smul_left]
  field_simp [hz.ne']
  ring

theorem affine_gaussian_laplace {z : ℝ} (hz : 0 < z) (w u : E) :
    (∫ x, Real.exp (inner ℝ u x)
      ∂(stdGaussian E).map (fun g => z⁻¹ • w+Real.sqrt (z⁻¹) • g)) =
        Real.exp (inner ℝ (z⁻¹ • w) u+‖u‖^2/(2*z)) := by
  rw [integral_map (by fun_prop : Measurable (fun g : E =>
      z⁻¹ • w+Real.sqrt (z⁻¹) • g)).aemeasurable
    (by fun_prop : Measurable (fun x : E => Real.exp (inner ℝ u x))).aestronglyMeasurable]
  simp_rw [inner_add_right,inner_smul_right,Real.exp_add]
  rw [integral_const_mul,integral_exp_inner_stdGaussian,
    Real.sq_sqrt (inv_nonneg.mpr hz.le),← Real.exp_add]
  rw [← Real.exp_add]
  congr 1
  rw [real_inner_smul_left,real_inner_comm u w]
  field_simp

/-- The normalized quadratic tilt is a shifted and rescaled standard Gaussian measure.
-/
theorem tilted_quadratic_eq_affine_gaussian {z : ℝ} (hz : 0 < z) (w : E) :
    (stdGaussian E).tilted (fun x => inner ℝ w x-(z-1)/2*‖x‖^2) =
      (stdGaussian E).map (fun g => z⁻¹ • w+Real.sqrt (z⁻¹) • g) := by
  let mu := (stdGaussian E).tilted (fun x => inner ℝ w x-(z-1)/2*‖x‖^2)
  let nu := (stdGaussian E).map (fun g => z⁻¹ • w+Real.sqrt (z⁻¹) • g)
  haveI : IsProbabilityMeasure mu := isProbabilityMeasure_tilted (integrable_exp_quadratic hz w)
  haveI : IsProbabilityMeasure nu := (Measure.isProbabilityMeasure_map_iff
    (by fun_prop : Measurable (fun g : E => z⁻¹ • w+Real.sqrt (z⁻¹) • g)).aemeasurable).mpr
      inferInstance
  change mu = nu
  apply Measure.ext_of_charFun
  funext u
  have hm : mgf (fun x => inner ℝ u x) mu = mgf (fun x => inner ℝ u x) nu := by
    funext t
    have H := quadratic_tilt_laplace hz w (t • u)
    have K := affine_gaussian_laplace hz w (t • u)
    simpa only [mgf,real_inner_smul_left] using H.trans K.symm
  have hs : integrableExpSet (fun x => inner ℝ u x) mu = univ := by
    apply eq_univ_of_forall
    intro t
    change Integrable (fun x => Real.exp (t*inner ℝ u x)) mu
    simpa only [real_inner_smul_left] using quadratic_tilt_exp_inner_integrable hz w (t • u)
  have H := eqOn_complexMGF_of_mgf hm (show (Complex.I : ℂ) ∈
      {s | s.re ∈ interior (integrableExpSet (fun x => inner ℝ u x) mu)} by simp [hs])
  simpa only [complexMGF,charFun_apply,real_inner_comm u,mul_comm Complex.I] using H

/-- Exact shifted-Gaussian law for the finite one-step endpoint. -/
theorem tilted_endpoint_eq_affine_gaussian {B v m : ℝ} (hB : 0 < B) (hv : 0 ≤ v)
    (hD : 0 < B-m*v) (y : E) :
    (stdGaussian E).tilted (tiltExponent B v m y) =
      (stdGaussian E).map (fun g => (m*Real.sqrt v/(B-m*v)) • y+
        Real.sqrt (B/(B-m*v)) • g) := by
  let C := m*‖y‖^2/(2*B)
  let Q : E → ℝ := fun x => inner ℝ ((m*Real.sqrt v/B) • y) x-
    ((B-m*v)/B-1)/2*‖x‖^2
  have hfun : tiltExponent B v m y = (fun _ => C)+Q := by
    funext x
    exact tiltExponent_eq_quadratic hB hv y x
  have hCancel := tilted_tilted (μ := stdGaussian E)
    (integrable_const (Real.exp C)) Q
  rw [tilted_const] at hCancel
  rw [hfun,← hCancel]
  rw [tilted_quadratic_eq_affine_gaussian (div_pos hD hB)]
  apply congrArg (fun f : E → E => (stdGaussian E).map f)
  funext g
  rw [inv_div,smul_smul]
  congr 2
  field_simp [hB.ne',hD.ne']

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltLaw
