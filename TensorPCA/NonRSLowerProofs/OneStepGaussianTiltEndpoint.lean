-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltFractional

/-! Spherical linear partitions and their one-step fractional Gaussian endpoint, using
the spherical angular law.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianTiltEndpoint
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
noncomputable section

def sphericalLaplace (N : ℕ) (w : Model.Vector N) : ℝ :=
  ∫ u, Real.exp (inner ℝ w (Real.sqrt (N : ℝ) • u)) ∂Model.spherePrior N

def fractionalSphereMoment (N : ℕ) (m v : ℝ) (y : Model.Vector N) : ℝ :=
  ∫ g, (sphericalLaplace N (y+Real.sqrt v • g))^m ∂stdGaussian (Model.Vector N)

theorem sphericalLaplace_measurable (N : ℕ) : Measurable (sphericalLaplace N) := by
  have H : Measurable (fun p : Model.Vector N×Model.Vector N =>
      Real.exp (inner ℝ p.1 (Real.sqrt (N : ℝ) • p.2))) := by fun_prop
  exact H.stronglyMeasurable.integral_prod_right'.measurable

theorem sphericalLaplace_pos {N : ℕ} (hN : 0 < N) (w : Model.Vector N) :
    0 < sphericalLaplace N w := by
  apply integral_exp_pos
  exact Geometry.spherePrior_continuous_integrable hN _ (by fun_prop)

theorem sphericalLaplace_le_exp_norm {N : ℕ} (hN : 0 < N) (w : Model.Vector N) :
    sphericalLaplace N w ≤ Real.exp (Real.sqrt (N : ℝ)*‖w‖) := by
  have hI := Geometry.spherePrior_continuous_integrable hN
    (fun u => Real.exp (inner ℝ w (Real.sqrt (N : ℝ) • u))) (by fun_prop)
  have H := integral_mono_ae hI (integrable_const (Real.exp (Real.sqrt (N : ℝ)*‖w‖))) (by
    filter_upwards [Geometry.spherePrior_norm_ae hN] with u hu
    apply Real.exp_le_exp.mpr
    have h := (le_abs_self _).trans (abs_real_inner_le_norm w (Real.sqrt (N : ℝ) • u))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one] at h
    simpa only [mul_comm] using h)
  simpa only [sphericalLaplace,integral_const,probReal_univ,one_smul] using H

theorem fractionalSphereMoment_integrable {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : 0 ≤ m)
    (v : ℝ) (y : Model.Vector N) :
    Integrable (fun g => (sphericalLaplace N (y+Real.sqrt v • g))^m)
      (stdGaussian (Model.Vector N)) := by
  have hI := (SYK.integrable_exp_mul_norm (ι := Fin N)
    (m*Real.sqrt (N : ℝ)*Real.sqrt v)).const_mul
      (Real.exp (m*Real.sqrt (N : ℝ)*‖y‖))
  have hMu : SYK.standardGaussianMeasureOnEuclidean (Fin N) = stdGaussian (Model.Vector N) := by
    simp only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian]
  rw [hMu] at hI
  have hM : Measurable (fun g : Model.Vector N =>
      (sphericalLaplace N (y+Real.sqrt v • g))^m) :=
    ((sphericalLaplace_measurable N).comp (by fun_prop)).pow_const m
  apply hI.mono' hM.aestronglyMeasurable
  filter_upwards [] with g
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (sphericalLaplace_pos hN _).le _)]
  calc
    _ ≤ (Real.exp (Real.sqrt (N : ℝ)*‖y+Real.sqrt v • g‖))^m :=
      Real.rpow_le_rpow (sphericalLaplace_pos hN _).le (sphericalLaplace_le_exp_norm hN _) hm
    _ = Real.exp (m*Real.sqrt (N : ℝ)*‖y+Real.sqrt v • g‖) := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ Real.exp (m*Real.sqrt (N : ℝ)*(‖y‖+Real.sqrt v*‖g‖)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hm (Real.sqrt_nonneg _))
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg v)] using
        norm_add_le y (Real.sqrt v • g)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem fractionalSphereMoment_pos {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : 0 ≤ m)
    (v : ℝ) (y : Model.Vector N) : 0 < fractionalSphereMoment N m v y := by
  have hEq : (fun g : Model.Vector N => (sphericalLaplace N (y+Real.sqrt v • g))^m) =
      (fun g => Real.exp (m*Real.log (sphericalLaplace N (y+Real.sqrt v • g)))) := by
    funext g
    rw [Real.rpow_def_of_pos (sphericalLaplace_pos hN _)]
    congr 1
    ring
  unfold fractionalSphereMoment
  rw [hEq]
  apply integral_exp_pos
  rw [← hEq]
  exact fractionalSphereMoment_integrable hN hm v y

end
end TensorPCA.NonRSLowerProofs.OneStepGaussianTiltEndpoint
