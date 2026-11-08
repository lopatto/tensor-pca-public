-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.GaussianFinitePriorApproximationProofs

/-! Gaussian clip/round errors vanish even after multiplying by every fixed
power of the clipping radius. This supplies the bounded-reference stability
cost without asserting a false global tensor-power Lipschitz bound. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationMomentProofs
open MeasureTheory ProbabilityTheory Set Filter GaussianFinitePriorApproximationProofs
open scoped Topology ENNReal
noncomputable section

theorem weighted_error_le_reciprocal (r j : ℕ) (hr : r ≤ j) {x : ℝ}
    (hx : |x| ≤ ((j+1 : ℕ) : ℝ)) :
    ((j : ℝ)+1)^r*|gaussianQuantizer j x-x| ≤ 1/((j : ℝ)+1) := by
  have hD : 0 < (j+1)^(j+1) := pow_pos (Nat.succ_pos j) _
  have hm := clipRound_error_le_mesh (j+1) hD hx
  have hB : 0 < ((j+1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos j)
  have hBD : ((j+1 : ℕ) : ℝ)^(r+1) ≤ (((j+1)^(j+1) : ℕ) : ℝ) := by
    exact_mod_cast pow_le_pow_right₀ (by omega : 1 ≤ j+1) (by omega : r+1 ≤ j+1)
  have hdiv : ((j+1 : ℕ) : ℝ)^r/(((j+1)^(j+1) : ℕ) : ℝ) ≤ 1/((j+1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr hD) hB).mpr
    simpa only [← pow_succ,one_mul] using hBD
  have H := (mul_le_mul_of_nonneg_left hm (pow_nonneg hB.le r)).trans
    (show ((j+1 : ℕ) : ℝ)^r*(1/(((j+1)^(j+1) : ℕ) : ℝ)) ≤ 1/((j+1 : ℕ) : ℝ) by
      simpa only [mul_one_div] using hdiv)
  simpa only [gaussianQuantizer,Nat.cast_add,Nat.cast_one] using H

theorem gaussianQuantizer_weighted_error_tendsto (r : ℕ) (x : ℝ) :
    Tendsto (fun j : ℕ ↦ ((j : ℝ)+1)^r*|gaussianQuantizer j x-x|) atTop (𝓝 (0 : ℝ)) := by
  have hnear : ∀ᶠ j : ℕ in atTop,
      ((j : ℝ)+1)^r*|gaussianQuantizer j x-x| ≤ 1/((j : ℝ)+1) := by
    obtain ⟨J,hJ⟩ := exists_nat_gt |x|
    filter_upwards [eventually_ge_atTop J,eventually_ge_atTop r] with j hj hr
    apply weighted_error_le_reciprocal r j hr
    have hc : (J : ℝ) ≤ j := Nat.cast_le.mpr hj
    simp only [Nat.cast_add,Nat.cast_one]
    linarith
  exact squeeze_zero' (Eventually.of_forall (fun j ↦ by positivity)) hnear
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem weighted_error_le_polynomial (r j : ℕ) (hr : r ≤ j) (x : ℝ) :
    ((j : ℝ)+1)^r*|gaussianQuantizer j x-x| ≤ |x|^(r+1)+1 := by
  have hB : 0 ≤ (j : ℝ)+1 := by positivity
  by_cases hx : |x| ≤ ((j+1 : ℕ) : ℝ)
  · have h := weighted_error_le_reciprocal r j hr hx
    have hi : (1 : ℝ)/((j : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j])
    exact h.trans (hi.trans (by linarith [pow_nonneg (abs_nonneg x) (r+1)]))
  · have hxB : (j : ℝ)+1 ≤ |x| := by
      have H := (lt_of_not_ge hx).le
      simpa only [Nat.cast_add,Nat.cast_one] using H
    calc
      _ ≤ ((j : ℝ)+1)^r*|x| := mul_le_mul_of_nonneg_left
        (clipRound_error_le_abs (j+1) (pow_pos (Nat.succ_pos j) _) x) (pow_nonneg hB r)
      _ ≤ |x|^r*|x| := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hxB r) (abs_nonneg x)
      _ = |x|^(r+1) := (pow_succ _ _).symm
      _ ≤ _ := le_add_of_nonneg_right zero_le_one

theorem gaussian_abs_pow_integrable (r : ℕ) : Integrable (fun x : ℝ ↦ |x|^r) (stdGaussian ℝ) := by
  simpa only [id_eq,Real.norm_eq_abs] using
    (IsGaussian.memLp_id (stdGaussian ℝ) (r : ℕ) (ENNReal.natCast_ne_top r)).integrable_norm_pow'

theorem gaussian_polynomial_fourth_integrable (r : ℕ) :
    Integrable (fun x : ℝ ↦ (|x|^(r+1)+1)^4) (stdGaussian ℝ) := by
  have H := ((((gaussian_abs_pow_integrable ((r+1)*4)).add
    ((gaussian_abs_pow_integrable ((r+1)*3)).const_mul 4)).add
      ((gaussian_abs_pow_integrable ((r+1)*2)).const_mul 6)).add
        ((gaussian_abs_pow_integrable (r+1)).const_mul 4)).add (integrable_const (1 : ℝ))
  apply H.congr
  exact Eventually.of_forall (fun x ↦ by
    simp only [Pi.add_apply]
    simp only [pow_mul]
    ring)

/-- The actual fourth Gaussian error, weighted by a fixed clipping-radius
power, tends to zero; it absorbs bounded reference channel constants. -/
theorem weighted_fourth_error_integral_tendsto (r : ℕ) :
    Tendsto (fun j : ℕ ↦ ∫ x : ℝ,
      (((j : ℝ)+1)^r*|gaussianQuantizer j x-x|)^4 ∂stdGaussian ℝ) atTop (𝓝 (0 : ℝ)) := by
  have hm (j : ℕ) : Measurable (fun x : ℝ ↦
      (((j : ℝ)+1)^r*|gaussianQuantizer j x-x|)^4) :=
    ((continuous_abs.measurable.comp ((gaussianQuantizer_measurable j).sub measurable_id)).const_mul _).pow_const 4
  have hbound (j : ℕ) : ∀ᵐ x : ℝ ∂stdGaussian ℝ,
      ‖((((j+r : ℕ) : ℝ)+1)^r*|gaussianQuantizer (j+r) x-x|)^4‖ ≤ (|x|^(r+1)+1)^4 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (weighted_error_le_polynomial r (j+r) (by omega) x) 4
  have hpoint : ∀ᵐ x : ℝ ∂stdGaussian ℝ, Tendsto (fun j : ℕ ↦
      ((((j+r : ℕ) : ℝ)+1)^r*|gaussianQuantizer (j+r) x-x|)^4) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    have H := ((tendsto_add_atTop_iff_nat r).mpr (gaussianQuantizer_weighted_error_tendsto r x)).pow 4
    simpa only [zero_pow (by norm_num : 4 ≠ 0)] using H
  have H := tendsto_integral_of_dominated_convergence (fun x : ℝ ↦ (|x|^(r+1)+1)^4)
    (fun j ↦ (hm (j+r)).aestronglyMeasurable) (gaussian_polynomial_fourth_integrable r) hbound hpoint
  apply (tendsto_add_atTop_iff_nat r).mp
  simpa only [integral_zero] using H

/-- Actual scalar L4 coupling error, expressed through ordinary square roots. -/
def gaussianFourthRootError (j : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (∫ x : ℝ, |gaussianQuantizer j x-x|^4 ∂stdGaussian ℝ))

theorem weighted_gaussianFourthRootError_tendsto (r : ℕ) :
    Tendsto (fun j : ℕ ↦ ((j : ℝ)+1)^r*gaussianFourthRootError j) atTop (𝓝 (0 : ℝ)) := by
  have heq (j : ℕ) :
      Real.sqrt (Real.sqrt (∫ x : ℝ, (((j : ℝ)+1)^r*|gaussianQuantizer j x-x|)^4 ∂stdGaussian ℝ)) =
        ((j : ℝ)+1)^r*gaussianFourthRootError j := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hp : 0 ≤ ((j : ℝ)+1)^r := by positivity
    rw [show (((j : ℝ)+1)^r)^4 = ((((j : ℝ)+1)^r)^2)^2 by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
    rfl
  have H := (weighted_fourth_error_integral_tendsto r).sqrt.sqrt
  simpa only [heq,Real.sqrt_zero] using H

end
end TensorPCA.GaussianFinitePriorApproximationMomentProofs
