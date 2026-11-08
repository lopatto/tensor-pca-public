-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianSpinInterpolationProofs
public import TensorPCA.Geometry

/-!
# Gaussian integration by parts for affine Gibbs inputs

The Gibbs parameter space may include a squared-signal normalizer coordinate.
Only the observed Gaussian coefficient space must be Euclidean. This avoids
assuming a constant norm when specializing the nonunit-prior channel.
-/
@[expose] public section

namespace TensorPCA.GaussianAffineGibbsProofs

open MeasureTheory ProbabilityTheory GaussianSpinInterpolation
open scoped RealInnerProductSpace

theorem affine_expectation_ibp {Omega H iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] [FiniteDimensional ℝ H]
    (mu : Measure Omega) [IsFiniteMeasure mu] [NeZero mu]
    (rho : Omega → ℝ) (L : Omega → H →L[ℝ] ℝ) (hrho : Measurable rho) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ x ∂mu, |rho x| ≤ C ∧ ‖L x‖ ≤ K)
    (B : EuclideanSpace ℝ iota →L[ℝ] H) (b : H) (d : EuclideanSpace ℝ iota) :
    (∫ w, inner ℝ d w * expectation mu rho L (b+B w) ∂stdGaussian (EuclideanSpace ℝ iota)) =
      ∫ w, expectationDerivative mu rho L (b+B w) (B d) ∂stdGaussian (EuclideanSpace ℝ iota) := by
  let g : EuclideanSpace ℝ iota → ℝ := fun w ↦ expectation mu rho L (b+B w)
  have hg : ContDiff ℝ 1 g := (expectation_contDiff mu rho L hrho hL hC hK hb).comp
    (contDiff_const.add B.contDiff)
  have hd (w : EuclideanSpace ℝ iota) : HasFDerivAt g
      ((expectationDerivative mu rho L (b+B w)).comp B) w := by
    have h := (expectation_hasFDerivAt mu rho L hrho hL hC hK hb (b+B w)).comp w
      (B.hasFDerivAt.const_add b)
    convert h using 1
    rfl
  have hgrad (w : EuclideanSpace ℝ iota) : ‖gradient g w‖ ≤ (2*C*K)*‖B‖ := by
    rw [gradient, (hd w).fderiv, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ iota)).symm.norm_map]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_expectationDerivative_le mu rho L hrho hL hC hK hb (b+B w))
        (norm_nonneg B))
  have hi := SYK.gaussian_ibp g d hg (max C ((2*C*K)*‖B‖)) 0
    (fun w ↦ by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (norm_expectation_le mu rho L hrho hL hC hb (b+B w)).trans (le_max_left _ _))
    (fun w ↦ by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (hgrad w).trans (le_max_right _ _))
  rw [GaussianConcentrationBridge.standardGaussianMeasure_bridge] at hi
  change (∫ w, inner ℝ d w * g w ∂stdGaussian (EuclideanSpace ℝ iota)) = _
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun w ↦ by
    change inner ℝ d (gradient g w) = _
    rw [real_inner_comm, gradient, (hd w).fderiv, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.comp_apply]


end TensorPCA.GaussianAffineGibbsProofs
