-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.Geometry
public import TensorPCA.GaussianFinitePriorApproximationMomentProofs
public import Mathlib.Algebra.Order.Ring.Abs

/-! Radius-dependent tensor-power control for the ordered feature.
No global Lipschitz bound is asserted for the unbounded Gaussian prior. -/
@[expose] public section
namespace TensorPCA.GaussianFinitePriorApproximationTensorProofs
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

/-- The genuine ordered tensor-power difference bound, valid at arbitrary
radii and in every dimension. -/
theorem feature_sub_norm_le {N k : ℕ} (hk : 1 ≤ k) (x y : Model.Vector N) :
    ‖Model.feature k x-Model.feature k y‖ ≤
      (k : ℝ)*(max ‖x‖ ‖y‖)^(k-1)*‖x-y‖ := by
  let a := ‖x‖
  let b := ‖y‖
  let c := inner ℝ x y
  let R := max a b
  let T := R^(k-1)
  have ha : 0 ≤ a := norm_nonneg x
  have hb : 0 ≤ b := norm_nonneg y
  have hR : 0 ≤ R := ha.trans (le_max_left _ _)
  have hT : 0 ≤ T := pow_nonneg hR _
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkk : (k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  have hab0 : 0 ≤ a*b := mul_nonneg ha hb
  have hc : |c| ≤ a*b := abs_real_inner_le_norm x y
  have hgap : 0 ≤ a*b-c := by linarith [le_abs_self c]
  have habR : a*b ≤ R*R := mul_le_mul (le_max_left a b) (le_max_right a b) hb hR
  have hpow : (a*b)^(k-1) ≤ T^2 := by
    have H := pow_le_pow_left₀ hab0 habR (k-1)
    simpa only [mul_pow,pow_two] using H
  have hp1 : |a^k-b^k| ≤ |a-b| *(k : ℝ)*T := by
    have H := abs_pow_sub_pow_le (a := a) (b := b) (n := k)
    simpa only [abs_of_nonneg ha,abs_of_nonneg hb] using H
  have hs1 : (a^k-b^k)^2 ≤ ((k : ℝ)*T)^2*(a-b)^2 := by
    calc
      _ = |a^k-b^k|^2 := (sq_abs _).symm
      _ ≤ (|a-b| *(k : ℝ)*T)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hp1
      _ = _ := by rw [mul_pow,mul_pow,sq_abs]; ring
  have hp2 : (a*b)^k-c^k ≤ (a*b-c)*(k : ℝ)*(a*b)^(k-1) := by
    apply (le_abs_self _).trans
    have H := abs_pow_sub_pow_le (a := a*b) (b := c) (n := k)
    rw [abs_of_nonneg hab0,max_eq_left hc,abs_of_nonneg hgap] at H
    exact H
  have hs2 : (a*b)^k-c^k ≤ (k : ℝ)*T^2*(a*b-c) := by
    apply hp2.trans
    have H := mul_le_mul_of_nonneg_left hpow (mul_nonneg hgap hk0)
    convert H using 1; ring
  have hcoef : 2*(k : ℝ)*T^2*(a*b-c) ≤ 2*((k : ℝ)*T)^2*(a*b-c) := by
    have H := mul_le_mul_of_nonneg_left hkk (show 0 ≤ 2*T^2*(a*b-c) by positivity)
    convert H using 1 <;> ring
  have hF : ‖Model.feature k x-Model.feature k y‖^2 = (a^k-b^k)^2+2*((a*b)^k-c^k) := by
    rw [norm_sub_sq_real,Geometry.feature_norm,Geometry.feature_norm,Geometry.feature_inner]
    dsimp [a,b,c]
    rw [mul_pow]
    ring
  have hD : ‖x-y‖^2 = (a-b)^2+2*(a*b-c) := by
    dsimp [a,b,c]
    rw [norm_sub_sq_real]
    ring
  have hs : ‖Model.feature k x-Model.feature k y‖^2 ≤ ((k : ℝ)*T*‖x-y‖)^2 := by
    calc
      _ = (a^k-b^k)^2+2*((a*b)^k-c^k) := hF
      _ ≤ ((k : ℝ)*T)^2*(a-b)^2+2*(k : ℝ)*T^2*(a*b-c) := by nlinarith only [hs1,hs2]
      _ ≤ ((k : ℝ)*T)^2*((a-b)^2+2*(a*b-c)) := by nlinarith only [hcoef]
      _ = _ := by rw [← hD]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

end
end TensorPCA.GaussianFinitePriorApproximationTensorProofs
