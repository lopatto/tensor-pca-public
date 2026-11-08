-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.VariationalProofs
public import Mathlib.Analysis.Calculus.MeanValue

/-! Signed-overlap derivative bounds for the slice covariance. The second derivative
need not be nonnegative on the negative part of the interval; its absolute value is
bounded by its value at the positive endpoint.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.OneStepSliceSignedDerivative
open Set
open VariationalProofs
noncomputable section

theorem abs_base_le {m q u : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-q) q) :
    |m^2+(1-m^2)*u| ≤ m^2+(1-m^2)*q := by
  have hs := one_sub_sq_nonneg hm
  have Hl := mul_le_mul_of_nonneg_left hu.1 hs
  have Hr := mul_le_mul_of_nonneg_left hu.2 hs
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg m]

theorem abs_deriv_le (k : ℕ) {m q u : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-q) q) :
    |deriv (Scalar.xiSlice k m) u| ≤ deriv (Scalar.xiSlice k m) q := by
  have hs := one_sub_sq_nonneg hm
  rw [deriv_xiSlice k m u, deriv_xiSlice k m q, abs_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k), abs_of_nonneg hs, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (abs_base_le hm hq hu) (k-1))
    (mul_nonneg (Nat.cast_nonneg k) hs)

theorem abs_secondDeriv_le (k : ℕ) (hk : 3 ≤ k) {m q u : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-q) q) :
    |deriv (deriv (Scalar.xiSlice k m)) u| ≤ deriv (deriv (Scalar.xiSlice k m)) q := by
  let C := (k : ℝ)*((k : ℝ)-1)*(1-m^2)^2
  have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [(hasDerivAt_deriv_xiSlice (by omega : 1 ≤ k) m u).deriv,
    (hasDerivAt_deriv_xiSlice (by omega : 1 ≤ k) m q).deriv]
  change |C*(m^2+(1-m^2)*u)^(k-2)| ≤ C*(m^2+(1-m^2)*q)^(k-2)
  rw [abs_mul, abs_of_nonneg hC, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (abs_base_le hm hq hu) (k-2)) hC

theorem deriv_sub_bounds (k : ℕ) (hk : 3 ≤ k) {m q u : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-q) q) :
    0 ≤ deriv (Scalar.xiSlice k m) q-deriv (Scalar.xiSlice k m) u ∧
      deriv (Scalar.xiSlice k m) q-deriv (Scalar.xiSlice k m) u ≤
        deriv (deriv (Scalar.xiSlice k m)) q*(q-u) := by
  have hfirst : deriv (Scalar.xiSlice k m) u ≤ deriv (Scalar.xiSlice k m) q :=
    (le_abs_self _).trans (abs_deriv_le k hm hq hu)
  refine ⟨sub_nonneg.mpr hfirst, ?_⟩
  have hqmem : q ∈ Icc (-q) q := ⟨by linarith [hq.1], le_rfl⟩
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r (_ : r ∈ Icc (-q) q) =>
      (hasDerivAt_deriv_xiSlice (by omega : 1 ≤ k) m r).differentiableAt)
    (fun r hr => by simpa only [Real.norm_eq_abs] using abs_secondDeriv_le k hk hm hq hr)
    (convex_Icc (-q) q) hu hqmem
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hu.2)] at H
  exact (le_abs_self _).trans H

/-- A nonnegative scale covers the finite-temperature factor beta squared.
The bounds feed the signed paired scalar endpoint; no physical interpolation
comparison is asserted here. -/
theorem scaled_slope_window (k : ℕ) (hk : 3 ≤ k) {m q u rho D a t t0 : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (-q) q)
    (hrho : 0 ≤ rho) (hD : 0 < D) (ha : a=q*D^2)
    (hcurv : rho*deriv (deriv (Scalar.xiSlice k m)) q ≤ D^2)
    (ht : t ∈ Icc (0 : ℝ) t0) (ht0 : t0 < 1) :
    let d := t*rho*(deriv (Scalar.xiSlice k m) q-deriv (Scalar.xiSlice k m) u)
    0 ≤ d ∧ d ≤ 2*a ∧
      (1-t0)*(q-u) ≤ (a-d)/D^2-u ∧ (a-d)/D^2-u ≤ 2 := by
  dsimp only
  let d := t*rho*(deriv (Scalar.xiSlice k m) q-deriv (Scalar.xiSlice k m) u)
  have hder := deriv_sub_bounds k hk hm hq hu
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg ht.1 hrho) hder.1
  have hgap : 0 ≤ q-u := sub_nonneg.mpr hu.2
  have hD2 : 0 < D^2 := sq_pos_of_pos hD
  have H1 := mul_le_mul_of_nonneg_left hder.2 (mul_nonneg ht.1 hrho)
  have H2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcurv hgap) ht.1
  have H3 := mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hD2.le hgap)
  have hbound : d ≤ t0*D^2*(q-u) := by dsimp [d]; nlinarith [H1, H2, H3]
  have hdiv : d/D^2 ≤ t0*(q-u) := (div_le_iff₀ hD2).mpr (by nlinarith [hbound])
  have hdiv0 : 0 ≤ d/D^2 := div_nonneg hd hD2.le
  have heq : (a-d)/D^2-u = q-u-d/D^2 := by
    rw [ha]
    field_simp [hD.ne']
    ring
  have htotal : d ≤ D^2*(q-u) := by
    have H := mul_le_mul_of_nonneg_right ht0.le (mul_nonneg hD2.le hgap)
    nlinarith [hbound, H]
  have htwogap : q-u ≤ 2*q := by linarith [hu.1]
  have hda : d ≤ 2*a := by
    rw [ha]
    nlinarith [mul_le_mul_of_nonneg_left htwogap hD2.le, htotal]
  refine ⟨hd, hda, ?_, ?_⟩
  · rw [heq]
    nlinarith [hdiv]
  · rw [heq]
    linarith [hq.2, htwogap, hdiv0]


end
end TensorPCA.NonRSLowerProofs.OneStepSliceSignedDerivative
