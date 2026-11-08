-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianMomentProofs

/-! Gaussian radius versus its deterministic square-root dimension.
The existing exact second and fourth Gaussian radius moments supply the
centered squared-radius variance; no independence or chi-law premise is used. -/
@[expose] public section
namespace TensorPCA.GaussianChiMeanCoupling
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma norm_sq_sub_dimension_sq_integrable (m : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦ (‖g‖^2-(m : ℝ))^2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  have h4 : Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦ ‖g‖^4)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    simpa using (IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin m))) 4
      (by norm_num)).integrable_norm_pow'
  have hsquare : MemLp (fun g : EuclideanSpace ℝ (Fin m) ↦ ‖g‖^2) 2
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (by
      simpa only [← pow_mul] using h4)
  exact (hsquare.sub (memLp_const (m : ℝ))).integrable_sq

/-- This is exactly the variance 2m of the actual squared Gaussian radius,
obtained solely by specializing the checked even-radius moments. -/
theorem integral_norm_sq_sub_dimension_sq (m : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin m), (‖g‖^2-(m : ℝ))^2
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) = 2*(m : ℝ) := by
  let mu := stdGaussian (EuclideanSpace ℝ (Fin m))
  have h2 : Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦ ‖g‖^2) mu :=
    IsGaussian.memLp_two_id.norm.integrable_sq
  have h4 : Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦ ‖g‖^4) mu := by
    simpa using (IsGaussian.memLp_id mu 4 (by norm_num)).integrable_norm_pow'
  have htwo : (∫ g : EuclideanSpace ℝ (Fin m), ‖g‖^2 ∂mu) = (m : ℝ) := by
    simpa [mu,GaussianMomentProofs.radialMomentProduct] using
      GaussianMomentProofs.gaussian_radius_even_moment (E := EuclideanSpace ℝ (Fin m)) 1
  have hfour : (∫ g : EuclideanSpace ℝ (Fin m), ‖g‖^4 ∂mu) = (m : ℝ)*((m : ℝ)+2) := by
    simpa [mu,GaussianMomentProofs.radialMomentProduct,Finset.prod_range_succ] using
      GaussianMomentProofs.gaussian_radius_even_moment (E := EuclideanSpace ℝ (Fin m)) 2
  have hpoly (g : EuclideanSpace ℝ (Fin m)) :
      (‖g‖^2-(m : ℝ))^2 = ‖g‖^4-(2*(m : ℝ))*‖g‖^2+(m : ℝ)^2 := by ring
  change (∫ g : EuclideanSpace ℝ (Fin m), (‖g‖^2-(m : ℝ))^2 ∂mu) = _
  simp_rw [hpoly]
  have hsub : Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦
      ‖g‖^4-(2*(m : ℝ))*‖g‖^2) mu := h4.sub (h2.const_mul (2*(m : ℝ)))
  rw [integral_add hsub (integrable_const ((m : ℝ)^2))]
  have hsplit := integral_sub h4 (h2.const_mul (2*(m : ℝ)))
  simp only [integral_const_mul] at hsplit
  rw [hsplit,htwo,hfour,integral_const,probReal_univ,one_smul]
  ring

lemma norm_sub_sqrt_dimension_sq_integrable (m : ℕ) :
    Integrable (fun g : EuclideanSpace ℝ (Fin m) ↦ (‖g‖-Real.sqrt (m : ℝ))^2)
      (stdGaussian (EuclideanSpace ℝ (Fin m))) :=
  (IsGaussian.memLp_two_id.norm.sub (memLp_const (Real.sqrt (m : ℝ)))).integrable_sq

private lemma sq_sub_sqrt_le {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    (x-Real.sqrt t)^2 ≤ (x^2-t)^2/t := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht.le
  have hfactor : x^2-t = (x-Real.sqrt t)*(x+Real.sqrt t) := by nlinarith
  apply (le_div_iff₀ ht).mpr
  calc
    (x-Real.sqrt t)^2*t = (x-Real.sqrt t)^2*(Real.sqrt t)^2 := by rw [hsq]
    _ ≤ (x-Real.sqrt t)^2*(x+Real.sqrt t)^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (sq_le_sq₀ hs (by positivity)).mpr (by linarith)
    _ = (x^2-t)^2 := by rw [hfactor,mul_pow]

/-- The actual chi radius has dimension-uniform squared error at sqrt(m).
The zero-dimensional canonical Gaussian is included, with error zero. -/
theorem integral_norm_sub_sqrt_dimension_sq_le_two (m : ℕ) :
    (∫ g : EuclideanSpace ℝ (Fin m), (‖g‖-Real.sqrt (m : ℝ))^2
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))) ≤ 2 := by
  by_cases hm : m = 0
  · subst m
    have H := GaussianMomentProofs.gaussian_radius_even_moment
      (E := EuclideanSpace ℝ (Fin 0)) 1
    have H0 : (∫ g : EuclideanSpace ℝ (Fin 0), ‖g‖^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin 0))) = 0 := by
      simpa [GaussianMomentProofs.radialMomentProduct] using H
    simpa using H0.le.trans (by norm_num : (0 : ℝ) ≤ 2)
  · have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    calc
      _ ≤ ∫ g : EuclideanSpace ℝ (Fin m), (‖g‖^2-(m : ℝ))^2/(m : ℝ)
          ∂stdGaussian (EuclideanSpace ℝ (Fin m)) :=
        integral_mono (norm_sub_sqrt_dimension_sq_integrable m)
          ((norm_sq_sub_dimension_sq_integrable m).div_const _)
          (fun g ↦ sq_sub_sqrt_le (norm_nonneg g) hmpos)
      _ = 2 := by
        rw [integral_div,integral_norm_sq_sub_dimension_sq]
        field_simp

end
end TensorPCA.GaussianChiMeanCoupling
