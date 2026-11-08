-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityNormalizationProofs
public import TensorPCA.TensorOverlapKernelProofs

/-! Dimension-uniform bounds for the finite cavity Gaussian features. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityBoundProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityNormalizationProofs TensorOrbitCountProofs TensorOrbitAggregationProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S]

theorem subset_card_le_pow (N k : ℕ) : Fintype.card (KSubset N k) ≤ N^k := by
  rw [Fintype.card_finset_len,Fintype.card_fin]
  exact Nat.choose_le_pow N k

theorem abs_monomial_le {N k : ℕ} (a : S → ℝ) (x : Fin N → S) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (T : KSubset N k) : |∏ i ∈ T.1, a (x i)| ≤ K^k := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i ∈ T.1, K := Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i _ ↦ hb (x i))
    _ = _ := by rw [Finset.prod_const,T.2]

theorem monomialSignal_norm_sq_le (a : S → ℝ) (N k : ℕ) (x : Fin N → S) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ‖monomialSignal a N k x‖^2 ≤ (N : ℝ)^k*K^(2*k) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ T : KSubset N k, (∏ i ∈ T.1, a (x i))^2) ≤ _
  calc
    _ ≤ ∑ _T : KSubset N k, (K^k)^2 := Finset.sum_le_sum (fun T _ ↦ by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_monomial_le a x hK hb T) 2)
    _ = (Fintype.card (KSubset N k) : ℝ)*K^(2*k) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← pow_mul]; congr 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast subset_card_le_pow N k) (pow_nonneg hK _)

theorem inv_pow_sub_succ_le {x : ℝ} (hx : 0 < x) {r : ℕ} (hr : 0 < r) :
    (x⁻¹)^r-((x+1)⁻¹)^r ≤ (r : ℝ)/x^(r+1) := by
  have hx1 : 0 < x+1 := by linarith
  have hi : (x+1)⁻¹ ≤ x⁻¹ := inv_anti₀ hx (by linarith)
  have hd : |x⁻¹-(x+1)⁻¹| ≤ (x⁻¹)^2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hi)]
    have heq : x⁻¹-(x+1)⁻¹ = (x*(x+1))⁻¹ := by field_simp; ring
    rw [heq,inv_pow]
    exact inv_anti₀ (pow_pos hx 2) (by nlinarith only [hx])
  have H := abs_pow_sub_pow_le (a := x⁻¹) (b := (x+1)⁻¹) (n := r)
  simp only [abs_of_pos (inv_pos.mpr hx),abs_of_pos (inv_pos.mpr hx1),max_eq_left hi] at H
  calc
    _ ≤ |(x⁻¹)^r-((x+1)⁻¹)^r| := le_abs_self _
    _ ≤ |x⁻¹-(x+1)⁻¹| *(r : ℝ)*(x⁻¹)^(r-1) := H
    _ ≤ (x⁻¹)^2*(r : ℝ)*(x⁻¹)^(r-1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg r)) (pow_nonneg (inv_nonneg.mpr hx.le) _)
    _ = (r : ℝ)*(x⁻¹)^(2+(r-1)) := by rw [pow_add]; ring
    _ = (r : ℝ)*(x⁻¹)^(r+1) := by congr 2; omega
    _ = _ := by rw [inv_pow,div_eq_mul_inv]

theorem correctionCoefficient_sq_le {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    (correctionCoefficient N k gamma)^2 ≤ (Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)/(N : ℝ)^k := by
  rw [correctionCoefficient_variance hN (by omega : 0 < k) hgamma]
  have H := inv_pow_sub_succ_le (Nat.cast_pos.mpr hN) (show 0 < k-1 by omega)
  simp only [inv_pow] at H
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at H
  have H' := mul_le_mul_of_nonneg_left H (mul_nonneg (Nat.cast_nonneg (Nat.factorial k)) hgamma)
  simpa only [Nat.cast_add,Nat.cast_one,mul_sub,mul_div_assoc] using H'

theorem cavitySignal_norm_sq_le (a : S → ℝ) (N k : ℕ) {gamma K : ℝ}
    (hk : 0 < k) (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (x : Fin N → S) :
    ‖cavitySignal a N k gamma x‖^2 ≤ (Nat.factorial k : ℝ)*gamma*K^(2*(k-1)) := by
  have heq : cavitySignal a N k gamma x = aggregateCoefficient (N+1) k gamma • monomialSignal a N (k-1) x := by ext T; rfl
  rw [heq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hC : (aggregateCoefficient (N+1) k gamma)^2*(N : ℝ)^(k-1) ≤ (Nat.factorial k : ℝ)*gamma := by
    rw [aggregateCoefficient_sq (Nat.succ_pos N) hk hgamma,div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos (by positivity : 0 < ((N+1 : ℕ) : ℝ)) (k-1))).mpr
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast Nat.le_succ N) (k-1)) (by positivity)
  calc
    _ ≤ (aggregateCoefficient (N+1) k gamma)^2*((N : ℝ)^(k-1)*K^(2*(k-1))) :=
      mul_le_mul_of_nonneg_left (monomialSignal_norm_sq_le a N (k-1) x hK hb) (sq_nonneg _)
    _ = ((aggregateCoefficient (N+1) k gamma)^2*(N : ℝ)^(k-1))*K^(2*(k-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (pow_nonneg hK _)

theorem correctionSignal_norm_sq_le (a : S → ℝ) {N k : ℕ} {gamma K : ℝ}
    (hN : 0 < N) (hk : 2 ≤ k) (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (x : Fin N → S) :
    ‖correctionSignal a N k gamma x‖^2 ≤ (Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k) := by
  rw [correctionSignal,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  have hC := (le_div_iff₀ (pow_pos (Nat.cast_pos.mpr hN : (0 : ℝ) < N) k)).mp (correctionCoefficient_sq_le hN hk hgamma)
  calc
    _ ≤ (correctionCoefficient N k gamma)^2*((N : ℝ)^k*K^(2*k)) :=
      mul_le_mul_of_nonneg_left (monomialSignal_norm_sq_le a N k x hK hb) (sq_nonneg _)
    _ = ((correctionCoefficient N k gamma)^2*(N : ℝ)^k)*K^(2*k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (pow_nonneg hK _)

theorem cavitySignal_norm_le (a : S → ℝ) (N k : ℕ) {gamma K : ℝ}
    (hk : 0 < k) (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (x : Fin N → S) :
    ‖cavitySignal a N k gamma x‖ ≤ Real.sqrt ((Nat.factorial k : ℝ)*gamma*K^(2*(k-1))) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (cavitySignal_norm_sq_le a N k hk hgamma hK hb x)

theorem correctionSignal_norm_le (a : S → ℝ) {N k : ℕ} {gamma K : ℝ}
    (hN : 0 < N) (hk : 2 ≤ k) (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (x : Fin N → S) :
    ‖correctionSignal a N k gamma x‖ ≤ Real.sqrt ((Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k)) :=
  (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (correctionSignal_norm_sq_le a hN hk hgamma hK hb x)

end
end TensorPCA.FinitePriorCavityBoundProofs
