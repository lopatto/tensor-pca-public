-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GroundState
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Nat.Choose.Sum

/-! Elementary variational-profile and slice-polynomial facts. These establish prerequisites of the variational conclusions; they do not
assume the ground-state or replica-symmetric variational formula. -/
@[expose] public section
namespace TensorPCA.VariationalProofs
open Set
open scoped BigOperators

/-- Every profile in the manuscript's four-parameter family belongs to the
actual continuous positive nonincreasing concave variational class. -/
theorem fourParameterProfile_admissible (delta a b q : ℝ)
    (hp : Scalar.FourParameterAdmissible delta a b q) :
    Scalar.AdmissibleProfile (Scalar.fourParameterProfile delta a b q) := by
  obtain ⟨hd, ha, hb, hq⟩ := hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Scalar.fourParameterProfile
    fun_prop
  · intro x hx y hy hxy
    have hmax : max x q ≤ max y q := max_le_max hxy le_rfl
    have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_left hxy 1) ha
    have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_left hmax 1) hb
    unfold Scalar.fourParameterProfile
    linarith
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy alpha beta halpha hbeta hsum
    have hmax : max (alpha*x+beta*y) q ≤ alpha*max x q+beta*max y q := by
      apply max_le
      · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left x q) halpha)
          (mul_le_mul_of_nonneg_left (le_max_left y q) hbeta)
      · calc
          q = alpha*q+beta*q := by rw [← add_mul, hsum, one_mul]
          _ ≤ alpha*max x q+beta*max y q :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_right x q) halpha)
              (mul_le_mul_of_nonneg_left (le_max_right y q) hbeta)
    have hbeta' : beta = 1-alpha := by linarith
    have hnonneg := mul_nonneg hb (sub_nonneg.mpr hmax)
    change alpha * Scalar.fourParameterProfile delta a b q x +
      beta * Scalar.fourParameterProfile delta a b q y ≤
      Scalar.fourParameterProfile delta a b q (alpha*x+beta*y)
    have hid : Scalar.fourParameterProfile delta a b q (alpha*x+beta*y) -
        (alpha * Scalar.fourParameterProfile delta a b q x +
          beta * Scalar.fourParameterProfile delta a b q y) =
        b * (alpha*max x q+beta*max y q-max (alpha*x+beta*y) q) := by
      unfold Scalar.fourParameterProfile
      rw [hbeta']
      ring
    linarith
  · intro t ht
    have h1 : 0 ≤ a*(1-t) := mul_nonneg ha (sub_nonneg.mpr ht.2)
    have h2 : 0 ≤ b*(1-max t q) :=
      mul_nonneg hb (sub_nonneg.mpr (max_le ht.2 hq.2))
    unfold Scalar.fourParameterProfile
    linarith

/-- The first derivative of the exact slice covariance polynomial. -/
theorem hasDerivAt_xiSlice (k : ℕ) (m t : ℝ) :
    HasDerivAt (Scalar.xiSlice k m)
      ((k : ℝ)*(1-m^2)*(m^2+(1-m^2)*t)^(k-1)) t := by
  have hbase : HasDerivAt (fun u : ℝ => m^2+(1-m^2)*u) (1-m^2) t := by
    simpa using ((hasDerivAt_id t).const_mul (1-m^2)).const_add (m^2)
  convert (hbase.pow k).sub_const (m^(2*k)) using 1
  · funext u
    simp [Scalar.xiSlice]
  · ring

theorem deriv_xiSlice (k : ℕ) (m t : ℝ) :
    deriv (Scalar.xiSlice k m) t =
      (k : ℝ)*(1-m^2)*(m^2+(1-m^2)*t)^(k-1) :=
  (hasDerivAt_xiSlice k m t).deriv

/-- Nonnegative coefficient of degree `p+1` in the actual slice covariance. -/
noncomputable def sliceCoefficient (k : ℕ) (m : ℝ) (p : Fin k) : ℝ :=
  (Nat.choose k (p.val+1) : ℝ) * (m^2)^(k-(p.val+1)) * (1-m^2)^(p.val+1)

theorem one_sub_sq_nonneg {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1) : 0 ≤ 1-m^2 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hm.2) (by linarith [hm.1] : 0 ≤ 1+m)
  nlinarith

theorem sliceCoefficient_nonneg (k : ℕ) {m : ℝ} (hm : m ∈ Icc (-1 : ℝ) 1)
    (p : Fin k) : 0 ≤ sliceCoefficient k m p := by
  unfold sliceCoefficient
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg m) _))
    (pow_nonneg (one_sub_sq_nonneg hm) _)

/-- Exact finite binomial expansion, with the constant covariance subtracted. -/
theorem xiSlice_eq_sum (k : ℕ) (m t : ℝ) :
    Scalar.xiSlice k m t = ∑ p : Fin k, sliceCoefficient k m p * t^(p.val+1) := by
  unfold Scalar.xiSlice
  rw [pow_mul, add_comm (m^2), add_pow, Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
  rw [add_sub_cancel_right]
  unfold sliceCoefficient
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (Nat.choose k (i+1) : ℝ) *
    (m^2)^(k-(i+1)) * (1-m^2)^(i+1) * t^(i+1)) k]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

/-- The slice is a finite covariance with nonnegative coefficients. -/
theorem xiSlice_finiteNonnegativeCovariance (k : ℕ) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1) :
    GroundState.FiniteNonnegativeCovariance (Scalar.xiSlice k m) :=
  ⟨k, sliceCoefficient k m, sliceCoefficient_nonneg k hm, xiSlice_eq_sum k m⟩

theorem deriv_xiSlice_one (k : ℕ) (m : ℝ) :
    deriv (Scalar.xiSlice k m) 1 = (k : ℝ)*(1-m^2) := by
  rw [deriv_xiSlice]
  have hbase : m^2+(1-m^2)*(1 : ℝ) = 1 := by ring
  rw [hbase, one_pow, mul_one]

/-- The second derivative of the exact polynomial; the guard only resolves
natural subtraction into the ordinary real factor k−1. -/
theorem hasDerivAt_deriv_xiSlice {k : ℕ} (hk : 1 ≤ k) (m t : ℝ) :
    HasDerivAt (deriv (Scalar.xiSlice k m))
      ((k : ℝ)*((k : ℝ)-1)*(1-m^2)^2*(m^2+(1-m^2)*t)^(k-2)) t := by
  have hfun : deriv (Scalar.xiSlice k m) =
      fun u : ℝ => (k : ℝ)*(1-m^2)*(m^2+(1-m^2)*u)^(k-1) := by
    funext u
    exact deriv_xiSlice k m u
  have hbase : HasDerivAt (fun u : ℝ => m^2+(1-m^2)*u) (1-m^2) t := by
    simpa using ((hasDerivAt_id t).const_mul (1-m^2)).const_add (m^2)
  rw [hfun]
  convert (hbase.pow (k-1)).const_mul ((k : ℝ)*(1-m^2)) using 1
  simp only [Nat.cast_sub hk, Nat.cast_one, Nat.sub_sub]
  ring

theorem secondDeriv_xiSlice_one {k : ℕ} (hk : 1 ≤ k) (m : ℝ) :
    deriv (deriv (Scalar.xiSlice k m)) 1 = (k : ℝ)*((k : ℝ)-1)*(1-m^2)^2 := by
  rw [(hasDerivAt_deriv_xiSlice hk m 1).deriv]
  have hbase : m^2+(1-m^2)*(1 : ℝ) = 1 := by ring
  rw [hbase, one_pow, mul_one]

/-- The manuscript's large-overlap cutoff implies the exact RS derivative
criterion. This is only polynomial/square-root algebra, not the RS theorem. -/
theorem xiSlice_rs_criterion {k : ℕ} (hk : 3 ≤ k) {m : ℝ}
    (hm : m ∈ Icc (-1 : ℝ) 1)
    (hlarge : Real.sqrt (1-1/((k : ℝ)-1)) ≤ |m|) :
    deriv (deriv (Scalar.xiSlice k m)) 1 ≤ deriv (Scalar.xiSlice k m) 1 := by
  have hkr : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ)-1 := by linarith
  have hinv : 1/((k : ℝ)-1) ≤ 1 := (div_le_one hkpos).2 (by linarith)
  have harg : 0 ≤ 1-1/((k : ℝ)-1) := by linarith
  have hsq := Real.sq_sqrt harg
  have hlower : 1-1/((k : ℝ)-1) ≤ m^2 := by
    nlinarith [Real.sqrt_nonneg (1-1/((k : ℝ)-1)), sq_abs m]
  have hmul := mul_le_mul_of_nonneg_left hlower hkpos.le
  have hid : ((k : ℝ)-1)*(1-1/((k : ℝ)-1)) = (k : ℝ)-2 := by
    rw [mul_sub, mul_one, mul_one_div_cancel (ne_of_gt hkpos)]
    ring
  rw [hid] at hmul
  have hcriterion : ((k : ℝ)-1)*(1-m^2) ≤ 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hcriterion
    (mul_nonneg (by linarith : 0 ≤ (k : ℝ)) (one_sub_sq_nonneg hm))
  rw [secondDeriv_xiSlice_one (by omega : 1 ≤ k), deriv_xiSlice_one]
  convert hprod using 1 <;> ring

/-- The complete algebraic slice prerequisite in the reviewed reduction. -/
theorem slicePolynomialFacts : GroundState.SlicePolynomialFacts := by
  intro k hk m hm
  exact ⟨xiSlice_finiteNonnegativeCovariance k hm, deriv_xiSlice_one k m,
    xiSlice_rs_criterion hk hm⟩

end TensorPCA.VariationalProofs
