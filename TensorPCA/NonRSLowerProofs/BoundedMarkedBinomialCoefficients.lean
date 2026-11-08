-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteDiscountedPartitionCoefficients

/-! Uniform falling-factorial coefficient bounds for masses in[0,1].
The positive-order estimate retains its factor p, including the endpoint0. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialCoefficients
open FiniteDiscountedPartitionProofs FiniteDiscountedPartitionCoefficients
open scoped BigOperators
noncomputable section

theorem normalizer_nonneg_of_le_one {p : ℝ} (hp : p≤1) (n : ℕ) : 0≤normalizer p n := by
  apply Finset.prod_nonneg
  intro j hj
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  linarith only [hj1,hp]

theorem normalizer_le_factorial {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (n : ℕ) :
    normalizer p (n+1)≤(n.factorial : ℝ) := by
  rw [← normalizer_zero_eq_factorial n]
  unfold normalizer
  apply Finset.prod_le_prod₀
  · intro j hj
    have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    linarith only [hj1,hp1]
  · intro j _
    linarith only [hp0]

theorem signed_falling_coefficient_abs_le {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (n : ℕ) :
    |((-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval p)/((n+1).factorial : ℝ)|≤
      p/((n+1 : ℕ) : ℝ) := by
  have H : (-1 : ℝ)^(n+1)*(descPochhammer ℝ (n+1)).eval p =
      -p*normalizer p (n+1) := by
    simpa only [blockFactor,normalizer] using signed_desc_eq_blockFactor p n
  have hfac : (0 : ℝ)<(n+1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [H,abs_div,abs_of_pos hfac,abs_mul,abs_neg,abs_of_nonneg hp0,
    abs_of_nonneg (normalizer_nonneg_of_le_one hp1 _)]
  calc
    p*normalizer p (n+1)/((n+1).factorial : ℝ) ≤ p*(n.factorial : ℝ)/((n+1).factorial : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (normalizer_le_factorial hp0 hp1 n) hp0) hfac.le
    _ = p/((n+1 : ℕ) : ℝ) := by
      rw [Nat.factorial_succ,Nat.cast_mul]
      field_simp

theorem signed_falling_coefficient_abs_le_one {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (n : ℕ) :
    |((-1 : ℝ)^n*(descPochhammer ℝ n).eval p)/(n.factorial : ℝ)|≤1 := by
  cases n with
  | zero => simp
  | succ n =>
    exact (signed_falling_coefficient_abs_le hp0 hp1 n).trans
      ((div_le_self hp0 (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans hp1)

end
end TensorPCA.NonRSLowerProofs.BoundedMarkedBinomialCoefficients
