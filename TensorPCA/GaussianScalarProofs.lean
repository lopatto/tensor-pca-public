-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianMomentProofs

/-!
# The scalar Gaussian prior channel

Both the signal and the noise are independent canonical real standard
Gaussians. The scalar spin in the normalizer has that same Gaussian prior.
-/
@[expose] public section

namespace TensorPCA.GaussianScalarProofs

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable def scalarNormalizer (a r : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (r * x - a * x ^ 2 / 2) ∂stdGaussian ℝ

noncomputable def scalarField (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sqrt a * z.2 + a * z.1

noncomputable def scalarLogPartition (a : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.log (scalarNormalizer a (scalarField a z))

theorem scalarNormalizer_eq {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    scalarNormalizer a r = (1 + a) ^ (-(1 / 2 : ℝ)) * Real.exp (r ^ 2 / (2 * (1 + a))) := by
  have h := GaussianMomentProofs.integral_exp_quadratic (E := ℝ) (z := 1 + a)
    (by linarith) r
  simpa only [scalarNormalizer, Real.inner_apply, Real.norm_eq_abs, sq_abs,
    Module.finrank_self, Nat.cast_one, add_sub_cancel_left, div_mul_eq_mul_div] using h

theorem log_scalarNormalizer {a : ℝ} (ha : 0 ≤ a) (r : ℝ) :
    Real.log (scalarNormalizer a r) = -(1 / 2 : ℝ) * Real.log (1 + a) +
      r ^ 2 / (2 * (1 + a)) := by
  have hpos : 0 < 1 + a := by linarith
  rw [scalarNormalizer_eq ha, Real.log_mul (Real.rpow_pos_of_pos hpos _).ne'
    (Real.exp_ne_zero _), Real.log_rpow hpos, Real.log_exp]

theorem integrable_gaussian_sq : Integrable (fun x : ℝ ↦ x ^ 2) (stdGaussian ℝ) := by
  have h := (IsGaussian.memLp_id (stdGaussian ℝ) 2 (by simp)).integrable_norm_pow (by decide : 2 ≠ 0)
  simpa only [id_eq, Real.norm_eq_abs, sq_abs] using h

theorem integral_gaussian_sq : (∫ x : ℝ, x ^ 2 ∂stdGaussian ℝ) = 1 := by
  simpa [GaussianMomentProofs.radialMomentProduct, Real.norm_eq_abs, sq_abs] using
    GaussianMomentProofs.gaussian_radius_even_moment (E := ℝ) 1

theorem scalarField_sq {a : ℝ} (ha : 0 ≤ a) (z : ℝ × ℝ) :
    scalarField a z ^ 2 = a ^ 2 * z.1 ^ 2 + (2 * a * Real.sqrt a) * (z.1 * z.2) + a * z.2 ^ 2 := by
  unfold scalarField
  nlinarith [Real.sq_sqrt ha]

theorem integrable_scalarField_sq {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun z ↦ scalarField a z ^ 2) ((stdGaussian ℝ).prod (stdGaussian ℝ)) := by
  simp_rw [scalarField_sq ha]
  exact (((integrable_gaussian_sq.comp_fst (stdGaussian ℝ)).const_mul (a ^ 2)).fun_add
    ((IsGaussian.integrable_fun_id (μ := stdGaussian ℝ)).mul_prod
      (IsGaussian.integrable_fun_id (μ := stdGaussian ℝ)) |>.const_mul (2 * a * Real.sqrt a))).fun_add
    ((integrable_gaussian_sq.comp_snd (stdGaussian ℝ)).const_mul a)

theorem integral_scalarField_sq {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, scalarField a z ^ 2 ∂(stdGaussian ℝ).prod (stdGaussian ℝ)) = a * (1 + a) := by
  simp_rw [scalarField_sq ha]
  have hfirst := (integrable_gaussian_sq.comp_fst (stdGaussian ℝ)).const_mul (a ^ 2)
  have hcross := (IsGaussian.integrable_fun_id (μ := stdGaussian ℝ)).mul_prod
    (IsGaussian.integrable_fun_id (μ := stdGaussian ℝ)) |>.const_mul (2 * a * Real.sqrt a)
  have hlast := (integrable_gaussian_sq.comp_snd (stdGaussian ℝ)).const_mul a
  rw [integral_add (hfirst.fun_add hcross) hlast, integral_add hfirst hcross,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_fun_fst (fun x : ℝ ↦ x ^ 2), integral_fun_snd (fun x : ℝ ↦ x ^ 2),
    integral_prod_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x)]
  simp only [integral_gaussian_sq, integral_id_stdGaussian, probReal_univ, one_smul,
    mul_zero, add_zero, mul_one]
  ring

theorem integrable_scalarLogPartition {a : ℝ} (ha : 0 ≤ a) :
    Integrable (scalarLogPartition a) ((stdGaussian ℝ).prod (stdGaussian ℝ)) := by
  unfold scalarLogPartition
  simp_rw [log_scalarNormalizer ha]
  exact (integrable_const _).fun_add ((integrable_scalarField_sq ha).div_const _)

/-- The scalar term in the Gaussian-prior variational formula, with the
actual independent signal and noise integration and its exact factor one-half. -/
theorem integral_scalarLogPartition {a : ℝ} (ha : 0 ≤ a) :
    (∫ z, scalarLogPartition a z ∂(stdGaussian ℝ).prod (stdGaussian ℝ)) =
      (1 / 2 : ℝ) * (a - Real.log (1 + a)) := by
  unfold scalarLogPartition
  simp_rw [log_scalarNormalizer ha]
  rw [integral_add (integrable_const _) ((integrable_scalarField_sq ha).div_const _),
    integral_div, integral_scalarField_sq ha]
  simp only [integral_const, probReal_univ, one_smul]
  have hne : 1 + a ≠ 0 := by linarith
  field_simp [hne]
  ring


end TensorPCA.GaussianScalarProofs
