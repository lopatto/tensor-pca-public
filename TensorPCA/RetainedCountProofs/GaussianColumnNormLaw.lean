-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
/- Narrow attributed law/scaling definitions from immutable
pmaronow/slowequilibration-palomar a28aaa336343c4caf43791ababd8ed0ee5c7b58e,
SlowEquilibration/Upstream/OAI/MathematicalPhysics/CriticalSK/GaussianMatrices.lean
and GOESpectrum.lean (credited upstream openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). Product-Gaussian columns are transported
to the actual canonical Gaussian radius; finite error bounds reuse the checked
GaussianChiMeanCoupling moments. No Householder or tridiagonal law is assumed. -/
module
public import TensorPCA.RetainedCountProofs.GaussianMatrixLaw
public import TensorPCA.GaussianChiMeanCoupling
@[expose] public section
namespace TensorPCA.RetainedCountProofs.OAI.CriticalSK
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def columnNormLaw (m : ℕ) (s : ℝ) : Measure ℝ :=
  (Measure.pi fun _ : Fin m => gaussianReal 0 (2*s^2).toNNReal).map
    (fun v : Fin m → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖)

lemma columnNorm_preserving (m : ℕ) (s : ℝ) :
    MeasurePreserving (fun v : Fin m → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖)
      (Measure.pi fun _ : Fin m => gaussianReal 0 (2*s^2).toNNReal) (columnNormLaw m s) :=
  ⟨(WithLp.measurable_toLp _ _).norm,rfl⟩

instance columnNormLaw_probability (m : ℕ) (s : ℝ) : IsProbabilityMeasure (columnNormLaw m s) :=
  (Measure.isProbabilityMeasure_map_iff
    (columnNorm_preserving m s).measurable.aemeasurable).2 inferInstance

/-- The symmetrized iid Gaussian matrix has offdiagonal variance1/(n+1). -/
def goeScale (n : ℕ) : ℝ := (Real.sqrt (2*(n+1:ℝ)))⁻¹

lemma goeScale_square (n : ℕ) : 2*(goeScale n)^2 = (n+1:ℝ)⁻¹ := by
  have hn : (0:ℝ) < n+1 := by positivity
  unfold goeScale
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  field_simp

lemma goeScale_diagonal (n : ℕ) : 4*(goeScale n)^2 = 2/(n+1:ℝ) := by
  have := goeScale_square n
  rw [div_eq_mul_inv]
  nlinarith

lemma gaussian_div_sqrt_preserving (n : ℕ) :
    MeasurePreserving (fun x : ℝ => x/Real.sqrt (n+1:ℝ)) (gaussianReal 0 1)
      (gaussianReal 0 (2*(goeScale n)^2).toNNReal) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianReal_map_div_const,zero_div,goeScale_square]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_mk,
    Real.coe_toNNReal _ (by positivity : 0 ≤ (n+1:ℝ)⁻¹)]
  rw [Real.sq_sqrt (by positivity),one_div]

/-- Exact product-column norm law, including the empty-column case m=0. -/
lemma columnNormLaw_scale (n m : ℕ) :
    columnNormLaw m (goeScale n) =
      (stdGaussian (EuclideanSpace ℝ (Fin m))).map
        (fun g => ‖g‖/Real.sqrt (n+1:ℝ)) := by
  have hp := measurePreserving_pi (fun _ : Fin m => gaussianReal 0 1)
    (fun _ : Fin m => gaussianReal 0 (2*(goeScale n)^2).toNNReal)
    (fun _ => gaussian_div_sqrt_preserving n)
  have hh := (columnNorm_preserving m (goeScale n)).comp hp
  have he : (fun x : Fin m → ℝ =>
      ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m))‖) =
      (fun x => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖/Real.sqrt (n+1:ℝ)) := by
    funext x
    have hv : (WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m)) =
        (Real.sqrt (n+1:ℝ))⁻¹ • WithLp.toLp 2 x := by
      ext i
      simp [div_eq_mul_inv,mul_comm]
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    ring
  have hmap := hh.map_eq
  change (Measure.pi fun _ : Fin m => gaussianReal 0 1).map
    (fun x => ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) :
      EuclideanSpace ℝ (Fin m))‖) = _ at hmap
  rw [he] at hmap
  rw [← hmap,← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (WithLp.measurable_toLp _ _)]
  rfl

private lemma scaled_radius_error (n m : ℕ) (g : EuclideanSpace ℝ (Fin m)) :
    (‖g‖/Real.sqrt (n+1:ℝ)-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2 =
      (‖g‖-Real.sqrt (m:ℝ))^2/(n+1:ℝ) := by
  rw [Real.sqrt_div (Nat.cast_nonneg m),← sub_div,div_pow,Real.sq_sqrt (by positivity)]

lemma columnNorm_error_integrable (n m : ℕ) :
    Integrable (fun r : ℝ => (r-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2)
      (columnNormLaw m (goeScale n)) := by
  rw [columnNormLaw_scale]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def,scaled_radius_error] using
    (GaussianChiMeanCoupling.norm_sub_sqrt_dimension_sq_integrable m).div_const (n+1:ℝ)

/-- The exact actual scaled-column law has mean-square distance at most2/N
from its deterministic Jacobi entry sqrt(m/N), with N=n+1. -/
theorem columnNorm_mean_square_error (n m : ℕ) :
    (∫ r : ℝ, (r-Real.sqrt ((m:ℝ)/(n+1:ℝ)))^2
      ∂columnNormLaw m (goeScale n)) ≤ 2/(n+1:ℝ) := by
  rw [columnNormLaw_scale,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [scaled_radius_error]
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (GaussianChiMeanCoupling.integral_norm_sub_sqrt_dimension_sq_le_two m) (by positivity)

lemma diagonal_sq_integrable (n : ℕ) :
    Integrable (fun r : ℝ => r^2) (gaussianReal 0 (4*(goeScale n)^2).toNNReal) := by
  simpa only [id_eq] using
    (memLp_id_gaussianReal (μ := 0) (v := (4*(goeScale n)^2).toNNReal) 2).integrable_sq

/-- The actual diagonal Gaussian has its exact second moment2/N. -/
theorem diagonal_integral_sq (n : ℕ) :
    (∫ r : ℝ, r^2 ∂gaussianReal 0 (4*(goeScale n)^2).toNNReal) = 2/(n+1:ℝ) := by
  have H := variance_fun_id_gaussianReal (μ := 0) (v := (4*(goeScale n)^2).toNNReal)
  rw [variance_eq_integral (by fun_prop)] at H
  simp only [integral_id_gaussianReal,sub_zero] at H
  rw [Real.coe_toNNReal (4*(goeScale n)^2) (by positivity)] at H
  exact H.trans (goeScale_diagonal n)

end
end TensorPCA.RetainedCountProofs.OAI.CriticalSK
