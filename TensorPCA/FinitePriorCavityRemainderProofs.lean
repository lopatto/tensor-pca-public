-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityKernelProofs
public import TensorPCA.GuerraRemainderProofs

/-! Signed cavity cross-kernel errors around the base posterior center.
The center is nonnegative and bounded by K squared; its thermal replica
variance remains the explicit error term. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityRemainderProofs
open MeasureTheory ProbabilityTheory Set
open FinitePriorCavityFieldProofs FinitePriorCavityNormalizationProofs
open FinitePriorCavityKernelProofs PosteriorPairProofs
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ}

theorem kernel_centered_sq_integral_le (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K)
    (r : ℕ) {c epsilon : ℝ} (hc : 0 ≤ c) (hepsilon : 0 ≤ epsilon)
    (kernel : ((Fin N → S) × (Fin N → S)) → ℝ)
    (hkernel : ∀ z, |kernel z-c*(overlap a z)^r| ≤ epsilon) :
    (∫ z, (kernel z-c*(meanOverlap q a)^r)^2 ∂q.prod q) ≤
      2*epsilon^2+2*(c*(r : ℝ)*(K^2)^(r-1))^2*replicaVariance q a := by
  let Q := meanOverlap q a
  let L := c*(r : ℝ)*(K^2)^(r-1)
  have hQ0 : 0 ≤ Q := meanOverlap_nonneg q a
  have hQ : Q ≤ K^2 := GuerraRemainderProofs.meanOverlap_le q a hN hb
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpoint (z : (Fin N → S) × (Fin N → S)) :
      (kernel z-c*Q^r)^2 ≤ 2*epsilon^2+2*L^2*(overlap a z-Q)^2 := by
    have hp := GuerraRemainderProofs.abs_power_difference_le (k := r)
      (GuerraRemainderProofs.overlap_abs_le a hN hK hb z) hQ0 hQ
    have he : |c*(overlap a z)^r-c*Q^r| ≤ L*|overlap a z-Q| := by
      rw [← mul_sub,abs_mul,abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left hp hc).trans_eq (by dsimp [L]; ring)
    have hdsq : (kernel z-c*(overlap a z)^r)^2 ≤ epsilon^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hepsilon).mpr (hkernel z)
    have hesq : (c*(overlap a z)^r-c*Q^r)^2 ≤ L^2*(overlap a z-Q)^2 := by
      have H := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hL (abs_nonneg _))).mpr he
      simpa only [mul_pow,sq_abs] using H
    nlinarith only [hdsq,hesq,sq_nonneg ((kernel z-c*(overlap a z)^r)-(c*(overlap a z)^r-c*Q^r))]
  have H := integral_mono_ae (μ := q.prod q) (f := fun z => (kernel z-c*Q^r)^2)
    (g := fun z => 2*epsilon^2+2*L^2*(overlap a z-Q)^2)
    Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall hpoint)
  rw [integral_add (integrable_const _) (Integrable.of_finite),integral_const,
    probReal_univ,one_smul,integral_const_mul] at H
  exact H

theorem cavitySignal_centered_sq_integral_le (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ}
    (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    (∫ z, (inner ℝ (cavitySignal a N k gamma z.1) (cavitySignal a N k gamma z.2)-
      (k : ℝ)*gamma*(meanOverlap q a)^(k-1))^2 ∂q.prod q) ≤
      2*(gamma*(k : ℝ)*(((k-1 : ℕ) : ℝ)^2+((k-1 : ℕ) : ℝ))*K^(2*(k-1))/(N : ℝ))^2+
        2*((k : ℝ)*gamma*((k-1 : ℕ) : ℝ)*(K^2)^(k-2))^2*replicaVariance q a := by
  have H := kernel_centered_sq_integral_le q a hN hK hb (k-1)
    (c := (k : ℝ)*gamma)
    (epsilon := gamma*(k : ℝ)*(((k-1 : ℕ) : ℝ)^2+((k-1 : ℕ) : ℝ))*K^(2*(k-1))/(N : ℝ))
    (by positivity) (by positivity)
    (fun z => inner ℝ (cavitySignal a N k gamma z.1) (cavitySignal a N k gamma z.2))
    (fun z => cavitySignal_covariance_error_le hN hk hgamma hK a z.1 z.2
      (fun i => hb (z.1 i)) (fun i => hb (z.2 i)))
  simpa only [show k-1-1 = k-2 by omega] using H

theorem correctionSignal_centered_sq_integral_le (q : Measure (Fin N → S)) [IsProbabilityMeasure q]
    (a : S → ℝ) (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ}
    (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    (∫ z, (inner ℝ (correctionSignal a N k gamma z.1) (correctionSignal a N k gamma z.2)-
      ((k-1 : ℕ) : ℝ)*gamma*(meanOverlap q a)^k)^2 ∂q.prod q) ≤
      2*(gamma*(((k-1 : ℕ) : ℝ)*(k : ℝ)^2+((k-1 : ℕ) : ℝ)^2)*K^(2*k)/(N : ℝ))^2+
        2*(((k-1 : ℕ) : ℝ)*gamma*(k : ℝ)*(K^2)^(k-1))^2*replicaVariance q a := by
  exact kernel_centered_sq_integral_le q a hN hK hb k
    (c := ((k-1 : ℕ) : ℝ)*gamma)
    (epsilon := gamma*(((k-1 : ℕ) : ℝ)*(k : ℝ)^2+((k-1 : ℕ) : ℝ)^2)*K^(2*k)/(N : ℝ))
    (by positivity) (by positivity)
    (fun z => inner ℝ (correctionSignal a N k gamma z.1) (correctionSignal a N k gamma z.2))
    (fun z => correctionSignal_covariance_error_le hN hk hgamma hK a z.1 z.2
      (fun i => hb (z.1 i)) (fun i => hb (z.2 i)))


end
end TensorPCA.FinitePriorCavityRemainderProofs
