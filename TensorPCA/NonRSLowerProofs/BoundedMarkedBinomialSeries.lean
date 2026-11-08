-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialCoefficients
public import Mathlib.Analysis.Analytic.Binomial

/-! The standard real binomial series with uniform geometric tails for
fractional masses. Coefficients use the same Pochhammer values as the
checked discounted-partition derivative identities. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialSeries
open BoundedMarkedBinomialCoefficients
open scoped BigOperators ENNReal
noncomputable section

theorem choose_eq_falling_div_factorial (p : ℝ) (n : ℕ) :
    Ring.choose p n=(descPochhammer ℝ n).eval p/(n.factorial : ℝ) := by
  rw [Ring.choose_eq_smul,smul_eq_mul,Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,← descPochhammer_eval_eq_ascPochhammer]
  ring

theorem signed_binomial_hasSum (p : ℝ) {z : ℝ} (hz : |z|<1) :
    HasSum (fun n : ℕ => (((-1 : ℝ)^n*(descPochhammer ℝ n).eval p)/(n.factorial : ℝ))*z^n)
      ((1-z)^p) := by
  have hball : -z∈Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal,Metric.mem_ball,Real.dist_eq,sub_zero,abs_neg]
    exact hz
  have H := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := p)).hasSum hball
  have hc (n : ℕ) : binomialSeries ℝ p n (fun _ => -z)=
      (((-1 : ℝ)^n*(descPochhammer ℝ n).eval p)/(n.factorial : ℝ))*z^n := by
    rw [binomialSeries_apply,Fin.prod_ofFn]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    rw [choose_eq_falling_div_factorial,
      show (-z)^n=(-1 : ℝ)^n*z^n by rw [← mul_pow,neg_one_mul]]
    ring
  simp only [hc,zero_add,sub_eq_add_neg] at H ⊢
  exact H

theorem binomial_polynomial_error_le {a z p : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hz0 : 0≤z) (hza : z≤a) (hp0 : 0≤p) (hp1 : p≤1) (n : ℕ) :
    |(∑j∈Finset.range n,(((-1 : ℝ)^j*(descPochhammer ℝ j).eval p)/(j.factorial : ℝ))*z^j)-
      (1-z)^p|≤a^n/(1-a) := by
  have hz1 : |z|<1 := by rw [abs_of_nonneg hz0]; exact hza.trans_lt ha1
  have HB (j : ℕ) :
      ‖(((-1 : ℝ)^j*(descPochhammer ℝ j).eval p)/(j.factorial : ℝ))*z^j‖≤1*a^j := by
    rw [norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs,abs_of_nonneg hz0]
    exact mul_le_mul (signed_falling_coefficient_abs_le_one hp0 hp1 j)
      (pow_le_pow_left₀ hz0 hza j) (pow_nonneg hz0 j) zero_le_one
  have H := norm_sub_le_of_geometric_bound_of_hasSum ha1 HB (signed_binomial_hasSum p hz1) n
  simpa only [Real.norm_eq_abs,one_mul] using H

theorem positive_order_binomial_hasSum (p : ℝ) {z : ℝ} (hz : |z|<1) :
    HasSum (fun n : ℕ => (((-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval p)/((n+1).factorial : ℝ))*z^(n+1))
      ((1-z)^p-1) := by
  have H := (hasSum_nat_add_iff' 1).mpr (signed_binomial_hasSum p hz)
  simpa only [Finset.sum_range_one,pow_zero,descPochhammer_zero,Polynomial.eval_one,
    Nat.factorial_zero,Nat.cast_one,div_one,one_mul] using H

theorem positive_order_binomial_polynomial_error_le {a z p : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hz0 : 0≤z) (hza : z≤a) (hp0 : 0≤p) (hp1 : p≤1) (n : ℕ) :
    |1+(∑j∈Finset.range n,
      (((-1 : ℝ)^(j+1)*(descPochhammer ℝ (j+1)).eval p)/((j+1).factorial : ℝ))*z^(j+1))-
      (1-z)^p|≤p*(a^(n+1)/(1-a)) := by
  have hz1 : |z|<1 := by rw [abs_of_nonneg hz0]; exact hza.trans_lt ha1
  have HB (j : ℕ) :
      ‖(((-1 : ℝ)^(j+1)*(descPochhammer ℝ (j+1)).eval p)/((j+1).factorial : ℝ))*z^(j+1)‖≤
        (p*a)*a^j := by
    rw [norm_mul,Real.norm_eq_abs,norm_pow,Real.norm_eq_abs,abs_of_nonneg hz0]
    have HC := (signed_falling_coefficient_abs_le hp0 hp1 j).trans
      (div_le_self hp0 (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)))
    calc
      _ ≤ p*a^(j+1) := mul_le_mul HC (pow_le_pow_left₀ hz0 hza _) (pow_nonneg hz0 _) hp0
      _ = _ := by rw [pow_succ]; ring
  have H := norm_sub_le_of_geometric_bound_of_hasSum ha1 HB (positive_order_binomial_hasSum p hz1) n
  rw [Real.norm_eq_abs] at H
  convert H using 1
  · congr 1
    ring
  · rw [pow_succ]
    ring

theorem normalized_positive_order_binomial_error_le {a z p : ℝ} (ha0 : 0≤a) (ha1 : a<1)
    (hz0 : 0≤z) (hza : z≤a) (hp0 : 0<p) (hp1 : p≤1) (n : ℕ) :
    |(1+(∑j∈Finset.range n,
      (((-1 : ℝ)^(j+1)*(descPochhammer ℝ (j+1)).eval p)/((j+1).factorial : ℝ))*z^(j+1))-
      (1-z)^p)/p|≤a^(n+1)/(1-a) := by
  rw [abs_div,abs_of_pos hp0,div_le_iff₀ hp0]
  simpa only [mul_comm] using positive_order_binomial_polynomial_error_le ha0 ha1 hz0 hza hp0.le hp1 n

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialSeries
