-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianChiMeanCoupling
public import Mathlib.Probability.Moments.Variance

/-! Affine standard-Gaussian squared-radius moments. The centered radius moment follows
from the Gaussian second and fourth moments; affine decomposition gives a dimension-
linear error bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem integral_inner_sq (u : Model.Vector N) :
    (∫ g, (inner ℝ u g) ^ 2 ∂stdGaussian (Model.Vector N)) = ‖u‖ ^ 2 := by
  have hLp : MemLp (fun g : Model.Vector N => inner ℝ u g) 2
      (stdGaussian (Model.Vector N)) := IsGaussian.memLp_two_id.const_inner u
  have h := variance_eq_sub hLp
  have hmean : (∫ g, inner ℝ u g ∂stdGaussian (Model.Vector N)) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ u)
  have hvar : variance (fun g : Model.Vector N => inner ℝ u g)
      (stdGaussian (Model.Vector N)) = ‖u‖ ^ 2 := by
    simpa only [coe_innerSL_apply, innerSL_apply_norm] using
      variance_dual_stdGaussian (innerSL ℝ u)
  simpa only [Pi.pow_apply, hmean, zero_pow two_ne_zero, sub_zero, hvar] using h.symm

theorem integral_norm_shift_sq (u : Model.Vector N) (s : ℝ) :
    (∫ g, ‖u + s • g‖ ^ 2 ∂stdGaussian (Model.Vector N)) =
      ‖u‖ ^ 2 + s ^ 2 * (N : ℝ) := by
  have hinner : Integrable (fun g : Model.Vector N => (2*s)*inner ℝ u g)
      (stdGaussian (Model.Vector N)) :=
    ((IsGaussian.memLp_two_id.const_inner u).integrable one_le_two).const_mul _
  have hnorm : Integrable (fun g : Model.Vector N => s^2*‖g‖^2)
      (stdGaussian (Model.Vector N)) :=
    IsGaussian.memLp_two_id.norm.integrable_sq.const_mul _
  have heq (g : Model.Vector N) : ‖u+s • g‖^2 = ‖u‖^2+(2*s)*inner ℝ u g+s^2*‖g‖^2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have htwo : (∫ g : Model.Vector N, ‖g‖^2 ∂stdGaussian (Model.Vector N)) = (N : ℝ) := by
    simpa [GaussianMomentProofs.radialMomentProduct] using
      GaussianMomentProofs.gaussian_radius_even_moment (E := Model.Vector N) 1
  simp_rw [heq]
  have hsum : Integrable (fun g : Model.Vector N => ‖u‖^2+(2*s)*inner ℝ u g)
      (stdGaussian (Model.Vector N)) := (integrable_const (‖u‖^2)).add hinner
  rw [integral_add hsum hnorm,
    integral_add (integrable_const (‖u‖^2)) hinner, integral_const_mul, integral_const_mul, htwo]
  have hmean : (∫ g, inner ℝ u g ∂stdGaussian (Model.Vector N)) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ u)
  rw [hmean, integral_const, probReal_univ, one_smul]
  ring

theorem norm_shift_sq_memLp_two (u : Model.Vector N) (s : ℝ) :
    MemLp (fun g : Model.Vector N => ‖u+s • g‖^2) 2
      (stdGaussian (Model.Vector N)) := by
  have h4 : MemLp (fun g : Model.Vector N => u+s • g) 4
      (stdGaussian (Model.Vector N)) :=
    (memLp_const u).add ((IsGaussian.memLp_id _ 4 (by norm_num)).const_smul s)
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using h4.integrable_norm_pow'

/-- A sufficient affine squared-radius variance bound, retaining its exact
linear dimension scale. The larger constants avoid a separate odd-moment API. -/
theorem integral_centered_norm_shift_sq_le (u : Model.Vector N) (s : ℝ) :
    (∫ g, (‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ)))^2
      ∂stdGaussian (Model.Vector N)) ≤ 8*s^2*‖u‖^2+4*s^4*(N : ℝ) := by
  have hleft : Integrable (fun g : Model.Vector N =>
      (‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ)))^2) (stdGaussian (Model.Vector N)) :=
    ((norm_shift_sq_memLp_two u s).sub (memLp_const _)).integrable_sq
  have hinner : Integrable (fun g : Model.Vector N => (inner ℝ u g)^2)
      (stdGaussian (Model.Vector N)) := IsGaussian.memLp_two_id.const_inner u |>.integrable_sq
  have hradius := GaussianChiMeanCoupling.norm_sq_sub_dimension_sq_integrable N
  have hright := (hinner.const_mul (8*s^2)).add (hradius.const_mul (2*s^4))
  have hpoint (g : Model.Vector N) :
      (‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ)))^2 ≤
        (8*s^2)*(inner ℝ u g)^2+(2*s^4)*(‖g‖^2-(N : ℝ))^2 := by
    have heq : ‖u+s • g‖^2-(‖u‖^2+s^2*(N : ℝ)) =
        (2*s*inner ℝ u g)+s^2*(‖g‖^2-(N : ℝ)) := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    rw [heq]
    have hsum (a b : ℝ) : (a+b)^2 ≤ 2*a^2+2*b^2 := by nlinarith [sq_nonneg (a-b)]
    calc
      _ ≤ 2*(2*s*inner ℝ u g)^2+2*(s^2*(‖g‖^2-(N : ℝ)))^2 := hsum _ _
      _ = _ := by ring
  calc
    _ ≤ ∫ g : Model.Vector N,
        (8*s^2)*(inner ℝ u g)^2+(2*s^4)*(‖g‖^2-(N : ℝ))^2
          ∂stdGaussian (Model.Vector N) := integral_mono hleft hright hpoint
    _ = 8*s^2*‖u‖^2+4*s^4*(N : ℝ) := by
      rw [integral_add (hinner.const_mul _) (hradius.const_mul _),
        integral_const_mul, integral_const_mul, integral_inner_sq,
        GaussianChiMeanCoupling.integral_norm_sq_sub_dimension_sq]
      ring


end
end TensorPCA.NonRSLowerProofs.OneStepGaussianShellMoments
