-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityFreeEnergyComparisonProofs
public import TensorPCA.FinitePriorCavityBoundProofs
public import TensorPCA.FinitePriorCavityScalarEndpointProofs
public import TensorPCA.GuerraRemainderProofs

/-! Fresh-spin and correction channels compared with their scalar
RS endpoints at the random background posterior mean overlap. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityScalarizationProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityBoundProofs FinitePriorCavityFreeEnergyComparisonProofs
open FinitePriorCavityScalarEndpointProofs GaussianPriorTransferProofs PosteriorPairProofs GuerraRemainderProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem lifted_pair_sq_integral_le {N : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K)
    (h : (Fin N → S) × (Fin N → S) → ℝ) :
    (∫ z : ((Fin N → S) × S) × ((Fin N → S) × S),
      (a z.1.2*a z.2.2*h (z.1.1,z.2.1))^2 ∂(q.prod p).prod (q.prod p)) ≤
      K^4*(∫ xy, (h xy)^2 ∂q.prod q) := by
  have hMap : ((q.prod p).prod (q.prod p)).map (fun z ↦ (z.1.1,z.2.1)) = q.prod q := by
    change ((q.prod p).prod (q.prod p)).map (Prod.map Prod.fst Prod.fst) = _
    rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst]
    simp
  have hI : (∫ z : ((Fin N → S) × S) × ((Fin N → S) × S), (h (z.1.1,z.2.1))^2 ∂(q.prod p).prod (q.prod p)) =
      ∫ xy, (h xy)^2 ∂q.prod q := by
    have H := integral_map (μ := (q.prod p).prod (q.prod p))
      (measurable_fst.fst.prodMk measurable_snd.fst).aemeasurable
      (measurable_of_finite (fun xy ↦ (h xy)^2)).aestronglyMeasurable
    rw [hMap] at H
    exact H.symm
  calc
    _ ≤ ∫ z : ((Fin N → S) × S) × ((Fin N → S) × S), K^4*(h (z.1.1,z.2.1))^2 ∂(q.prod p).prod (q.prod p) := by
      apply integral_mono_ae Integrable.of_finite Integrable.of_finite
      apply Filter.Eventually.of_forall
      intro z
      change (a z.1.2*a z.2.2*h (z.1.1,z.2.1))^2 ≤ K^4*(h (z.1.1,z.2.1))^2
      rw [mul_pow]
      have hA : |a z.1.2*a z.2.2| ≤ K^2 := by
        rw [abs_mul,pow_two]
        exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hK
      have hA2 : (a z.1.2*a z.2.2)^2 ≤ K^4 := by
        simpa only [sq_abs,← pow_mul] using pow_le_pow_left₀ (abs_nonneg _) hA 2
      exact mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
    _ = _ := by rw [integral_const_mul,hI]

theorem fresh_kernel_sq_integral_le {N k : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (gamma : ℝ) {K c : ℝ}
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (hc : 0 ≤ c) :
    (∫ z : ((Fin N → S) × S) × ((Fin N → S) × S),
      (inner ℝ (a z.1.2 • cavitySignal a N k gamma z.1.1) (a z.2.2 • cavitySignal a N k gamma z.2.1)-
        (Real.sqrt c*a z.1.2)*(Real.sqrt c*a z.2.2))^2 ∂(q.prod p).prod (q.prod p)) ≤
      K^4*(∫ xy, (inner ℝ (cavitySignal a N k gamma xy.1) (cavitySignal a N k gamma xy.2)-c)^2 ∂q.prod q) := by
  have hEq : (fun z : ((Fin N → S) × S) × ((Fin N → S) × S) ↦
      (inner ℝ (a z.1.2 • cavitySignal a N k gamma z.1.1) (a z.2.2 • cavitySignal a N k gamma z.2.1)-
        (Real.sqrt c*a z.1.2)*(Real.sqrt c*a z.2.2))^2) =
    (fun z ↦ (a z.1.2*a z.2.2*(inner ℝ (cavitySignal a N k gamma z.1.1) (cavitySignal a N k gamma z.2.1)-c))^2) := by
    funext z
    rw [real_inner_smul_left,real_inner_smul_right]
    have hs : (Real.sqrt c*a z.1.2)*(Real.sqrt c*a z.2.2) = c*(a z.1.2*a z.2.2) := by
      calc
        _ = (Real.sqrt c)^2*(a z.1.2*a z.2.2) := by ring
        _ = _ := by rw [Real.sq_sqrt hc]
    rw [hs]
    ring
  rw [hEq]
  exact lifted_pair_sq_integral_le q p a hK hb
    (fun xy ↦ inner ℝ (cavitySignal a N k gamma xy.1) (cavitySignal a N k gamma xy.2)-c)

theorem scalar_cavity_strength_le {N k : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    (k : ℝ)*gamma*(meanOverlap q a)^(k-1) ≤ (Nat.factorial k : ℝ)*gamma*K^(2*(k-1)) := by
  have hQ := meanOverlap_nonneg q a
  have hQb := meanOverlap_le q a hN hb
  have hFact : (k : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.self_le_factorial k
  calc
    _ ≤ (k : ℝ)*gamma*(K^2)^(k-1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hQ hQb (k-1)) (mul_nonneg (Nat.cast_nonneg k) hgamma)
    _ ≤ (Nat.factorial k : ℝ)*gamma*(K^2)^(k-1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFact hgamma) (pow_nonneg (sq_nonneg K) _)
    _ = _ := by rw [← pow_mul]

theorem scalar_correction_strength_le {N k : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    (k-1 : ℕ)*gamma*(meanOverlap q a)^k ≤ (Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k) := by
  have hQ := meanOverlap_nonneg q a
  have hQb := meanOverlap_le q a hN hb
  have hFact : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  calc
    _ ≤ (k-1 : ℕ)*gamma*(K^2)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hQ hQb k) (mul_nonneg (Nat.cast_nonneg _) hgamma)
    _ = gamma*(k-1 : ℕ)*K^(2*k) := by rw [← pow_mul]; ring
    _ ≤ _ := by
      have H := mul_le_mul_of_nonneg_right hFact
        (mul_nonneg (mul_nonneg hgamma (Nat.cast_nonneg (k-1))) (pow_nonneg hK (2*k)))
      nlinarith

/-- The fresh spin is compared with its scalar channel, uniformly in
its possibly revealed last-coordinate prior. -/
theorem fresh_freeEnergy_scalar_error_le {N k : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (hN : 0 < N) (hk : 0 < k)
    {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    |mixtureFreeEnergy (q.prod p) (fun z ↦ a z.2 • cavitySignal a N k gamma z.1)-
      mixtureFreeEnergy p (fun s ↦ Real.sqrt ((k : ℝ)*gamma*(meanOverlap q a)^(k-1))*a s)| ≤
      (1/2 : ℝ)*Real.exp (22*(2*(K*Real.sqrt ((Nat.factorial k : ℝ)*gamma*K^(2*(k-1)))))^2)*
        Real.sqrt (K^4*∫ xy, (inner ℝ (cavitySignal a N k gamma xy.1)
          (cavitySignal a N k gamma xy.2)-(k : ℝ)*gamma*(meanOverlap q a)^(k-1))^2 ∂q.prod q) := by
  let c := (k : ℝ)*gamma*(meanOverlap q a)^(k-1)
  let C := K*Real.sqrt ((Nat.factorial k : ℝ)*gamma*K^(2*(k-1)))
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hgamma)
    (pow_nonneg (meanOverlap_nonneg q a) _)
  have hC : 0 ≤ C := mul_nonneg hK (Real.sqrt_nonneg _)
  have hCA (z : (Fin N → S) × S) : ‖a z.2 • cavitySignal a N k gamma z.1‖ ≤ C := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hb _) (cavitySignal_norm_le a N k hk hgamma hK hb _) (norm_nonneg _) hK
  have hCB (z : (Fin N → S) × S) : |Real.sqrt c*a z.2| ≤ C := by
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sqrt_le_sqrt (scalar_cavity_strength_le (k := k) q a hN hgamma hK hb)
    exact (mul_le_mul hs (hb _) (abs_nonneg _) (Real.sqrt_nonneg _)).trans_eq (by dsimp [C]; ring)
  have H := abs_freeEnergy_sub_le_kernel_l2_real (q.prod p)
    (fun z ↦ a z.2 • cavitySignal a N k gamma z.1) (fun z ↦ Real.sqrt c*a z.2)
    (measurable_of_finite _) (measurable_of_finite _) hC hC hCA hCB
  rw [scalar_product_endpoint q p a c] at H
  have HL := fresh_kernel_sq_integral_le (k := k) (c := c) q p a gamma hK hb hc
  have HS := Real.sqrt_le_sqrt HL
  have HC : (1/2 : ℝ)*Real.exp (22*(C+C)^2) ≥ 0 := by positivity
  have HT := H.trans (mul_le_mul_of_nonneg_left HS HC)
  simpa only [C,c,two_mul] using HT

/-- The Gaussian correction channel has the literal constant-signal scalar
endpoint, whose free energy equals half the covariance center. -/
theorem correction_freeEnergy_scalar_error_le {N k : ℕ} (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) (hk : 2 ≤ k) {gamma K : ℝ}
    (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    |mixtureFreeEnergy q (correctionSignal a N k gamma)-
      (k-1 : ℕ)*gamma*(meanOverlap q a)^k/2| ≤
      (1/2 : ℝ)*Real.exp (22*(2*Real.sqrt ((Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k)))^2)*
        Real.sqrt (∫ xy, (inner ℝ (correctionSignal a N k gamma xy.1)
          (correctionSignal a N k gamma xy.2)-(k-1 : ℕ)*gamma*(meanOverlap q a)^k)^2 ∂q.prod q) := by
  let c := (k-1 : ℕ)*gamma*(meanOverlap q a)^k
  let C := Real.sqrt ((Nat.factorial k : ℝ)*gamma*(k-1 : ℕ)*K^(2*k))
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hgamma)
    (pow_nonneg (meanOverlap_nonneg q a) _)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCA := correctionSignal_norm_le a hN hk hgamma hK hb
  have hCB (x : Fin N → S) : |Real.sqrt c| ≤ C := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (scalar_correction_strength_le q a hN hgamma hK hb)
  have H := abs_freeEnergy_sub_le_kernel_l2_real q (correctionSignal a N k gamma)
    (fun _ ↦ Real.sqrt c) (measurable_of_finite _) measurable_const hC hC hCA hCB
  rw [mixtureFreeEnergy_const] at H
  have hs : ‖Real.sqrt c‖^2/2 = c/2 := by rw [Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc]
  rw [hs] at H
  have hs2 : Real.sqrt c*Real.sqrt c = c := Real.mul_self_sqrt hc
  simp only [hs2] at H
  simpa only [C,c,two_mul] using H

end
end TensorPCA.FinitePriorCavityScalarizationProofs
