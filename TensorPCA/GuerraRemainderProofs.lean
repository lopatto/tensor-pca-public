-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.BayesianPinningVarianceProofs
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Order.Ring.Abs

/-! Odd-order-safe power response bounds around the nonnegative posterior overlap mean, controlled only by thermal replica variance. -/
@[expose] public section
namespace TensorPCA.GuerraRemainderProofs
open MeasureTheory ProbabilityTheory Set Real PosteriorPairProofs BayesianPinningVarianceProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The power tangent inequality is used at the nonnegative center, never
at an overlap that may be negative for odd tensor order. -/
theorem power_tangent_lower_bound {k : ℕ} (hk : 0 < k) {Q m : ℝ}
    (hQ : 0 ≤ Q) (hm : 0 ≤ m) :
    (1-(k : ℝ))*m^k ≤ Q^k-(k : ℝ)*m^(k-1)*Q := by
  have H := pow_add_mul_le_add_pow hm (show 0 ≤ 2*m+(Q-m) by linarith) k
  rw [show m+(Q-m) = Q by ring] at H
  have hp : m^(k-1)*m = m^k := by
    rw [← pow_succ]
    congr 1
    omega
  nlinarith

theorem abs_power_difference_le {k : ℕ} {R Q B : ℝ}
    (hR : |R| ≤ B) (hQ0 : 0 ≤ Q) (hQ : Q ≤ B) :
    |R^k-Q^k| ≤ (k : ℝ)*B^(k-1)*|R-Q| := by
  have hmax : max |R| |Q| ≤ B := max_le hR (by simpa only [abs_of_nonneg hQ0] using hQ)
  have hpow := pow_le_pow_left₀ (le_trans (abs_nonneg R) (le_max_left _ _)) hmax (k-1)
  calc
    _ ≤ |R-Q| * (k : ℝ)*(max |R| |Q|)^(k-1) := abs_pow_sub_pow_le R Q k
    _ ≤ |R-Q| * (k : ℝ)*B^(k-1) := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The overlap R may have either sign. Only the actual center Q and
the scalar comparison parameter m are required to be nonnegative. -/
theorem power_response_lower_bound {k : ℕ} (hk : 0 < k) {R Q B m : ℝ}
    (hR : |R| ≤ B) (hQ0 : 0 ≤ Q) (hQ : Q ≤ B) (hm : 0 ≤ m) :
    (1-(k : ℝ))*m^k-(k : ℝ)*(B^(k-1)+m^(k-1))*|R-Q| ≤
      R^k-(k : ℝ)*m^(k-1)*R := by
  have hc : 0 ≤ (k : ℝ)*m^(k-1) := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hm _)
  have hd : |(R^k-(k : ℝ)*m^(k-1)*R)-(Q^k-(k : ℝ)*m^(k-1)*Q)| ≤
      (k : ℝ)*(B^(k-1)+m^(k-1))*|R-Q| := by
    calc
      _ = |(R^k-Q^k)-((k : ℝ)*m^(k-1))*(R-Q)| := by congr 1; ring
      _ ≤ |R^k-Q^k|+|((k : ℝ)*m^(k-1))*(R-Q)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (R^k-Q^k) (-(((k : ℝ)*m^(k-1))*(R-Q)))
      _ = |R^k-Q^k|+((k : ℝ)*m^(k-1))*|R-Q| := by rw [abs_mul, abs_of_nonneg hc]
      _ ≤ ((k : ℝ)*B^(k-1))*|R-Q|+((k : ℝ)*m^(k-1))*|R-Q| :=
        add_le_add (abs_power_difference_le hR hQ0 hQ) le_rfl
      _ = _ := by ring
  have ht := power_tangent_lower_bound hk hQ0 hm
  have hn := neg_abs_le ((R^k-(k : ℝ)*m^(k-1)*R)-(Q^k-(k : ℝ)*m^(k-1)*Q))
  linarith

section Posterior
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem overlap_abs_le (a : S → ℝ) (hN : 0 < N) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (z : Configuration S N × Configuration S N) :
    |overlap a z| ≤ K^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold overlap
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i : Fin N, |a (z.1 i)*a (z.2 i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, K^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hK
    _ = _ := by simp; ring

omit [Fintype S] [MeasurableSingletonClass S] in
theorem meanOverlap_le (a : S → ℝ) (hN : 0 < N) {K : ℝ}
    (hb : ∀ s, |a s| ≤ K) : meanOverlap q a ≤ K^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold meanOverlap
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ i : Fin N, K^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := coordinateMean_abs_le q a hb i
      have hsq := mul_self_le_mul_self (abs_nonneg (coordinateMean q a i)) hi
      simpa only [← pow_two, sq_abs] using hsq
    _ = _ := by simp; ring

theorem integral_overlap_deviation_le (a : S → ℝ) :
    (∫ z, |overlap a z-meanOverlap q a| ∂q.prod q) ≤ Real.sqrt (replicaVariance q a) := by
  have H := integral_sqrt_le_sqrt_integral (q.prod q)
    (f := fun z ↦ (overlap a z-meanOverlap q a)^2)
    (Filter.Eventually.of_forall (fun z ↦ sq_nonneg _)) MemLp.of_discrete
  simpa only [Real.sqrt_sq_eq_abs, replicaVariance] using H

/-- The actual posterior-replica power response has a nonnegative-center
tangent lower bound, with an error controlled by the actual thermal variance.
This remains valid for odd order and requires no outer-data concentration. -/
theorem posterior_power_response_lower_bound (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) {k : ℕ} (hk : 0 < k)
    {m : ℝ} (hm : 0 ≤ m) :
    (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*Real.sqrt (replicaVariance q a) ≤
      ∫ z, (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z ∂q.prod q := by
  have hc : 0 ≤ (k : ℝ)*((K^2)^(k-1)+m^(k-1)) := by positivity
  have H := integral_mono_ae (μ := q.prod q)
    (f := fun z ↦ (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*|overlap a z-meanOverlap q a|)
    (g := fun z ↦ (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z)
    Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall (fun z ↦
      power_response_lower_bound hk (overlap_abs_le a hN hK hb z)
        (meanOverlap_nonneg q a) (meanOverlap_le q a hN hb) hm))
  rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const,
    probReal_univ, one_smul, integral_const_mul] at H
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left (integral_overlap_deviation_le q a) hc) _).trans H

end Posterior
end
end TensorPCA.GuerraRemainderProofs
