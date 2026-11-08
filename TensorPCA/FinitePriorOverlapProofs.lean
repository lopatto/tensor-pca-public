-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorChannelProofs
public import TensorPCA.GaussianReplicaMomentProofs
public import TensorPCA.TensorOverlapKernelProofs
public import TensorPCA.PosteriorPairProofs

/-! # The finite-prior tensor and scalar replica kernels -/
@[expose] public section

namespace TensorPCA.FinitePriorOverlapProofs

open MeasureTheory ProbabilityTheory FinitePriorChannelProofs TensorOrbitCountProofs
open TensorOrbitAggregationProofs GaussianReplicaTransportProofs GaussianReplicaMomentProofs
open scoped RealInnerProductSpace

variable {S : Type*}

theorem configurationVector_inner {N : ℕ} (a : S → ℝ) (x y : Fin N → S) :
    inner ℝ (configurationVector a x) (configurationVector a y) =
      ∑ i, a (x i)*a (y i) := by
  simp [configurationVector, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]

theorem tensorSignal_inner (a : S → ℝ) (N k : ℕ) (gamma : ℝ) (x y : Fin N → S) :
    inner ℝ (tensorSignal a N k gamma x) (tensorSignal a N k gamma y) =
      (aggregateCoefficient N k gamma)^2 * ∑ T : KSubset N k, ∏ n ∈ T.1, a (x n)*a (y n) := by
  classical
  rw [tensorSignal, tensorSignal, unorderedSignal, unorderedSignal, EuclideanSpace.inner_toLp_toLp]
  change (∑ T : KSubset N k, (aggregateCoefficient N k gamma * ∏ n ∈ T.1, a (y n)) *
      (aggregateCoefficient N k gamma * ∏ n ∈ T.1, a (x n))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib]
  ring

theorem normalized_tensorSignal_inner {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (a : S → ℝ) {gamma : ℝ} (hgamma : 0 ≤ gamma) (x y : Fin N → S) :
    inner ℝ (tensorSignal a N k gamma x) (tensorSignal a N k gamma y) / (N:ℝ) =
      gamma * ((Nat.factorial k : ℝ) * (∑ T : KSubset N k, ∏ n ∈ T.1, a (x n)*a (y n)) / (N:ℝ)^k) := by
  rw [tensorSignal_inner, aggregateCoefficient_eq_sqrt hN hk hgamma,
    Real.sq_sqrt (by positivity)]
  have hp : (N:ℝ)^k = (N:ℝ)^(k-1)*(N:ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  field_simp [(Nat.cast_pos.mpr hN : (0:ℝ)<N).ne']

theorem normalized_scalarSignal_inner {N k : ℕ} (a : S → ℝ) {gamma q : ℝ}
    (hgamma : 0 ≤ gamma) (hq : 0 ≤ q) (x y : Fin N → S) :
    inner ℝ (scalarSignal a N k gamma q x) (scalarSignal a N k gamma q y) / (N:ℝ) =
      ((k:ℝ)*gamma*q^(k-1)) * PosteriorPairProofs.overlap a (x,y) := by
  rw [scalarSignal, scalarSignal, real_inner_smul_left, real_inner_smul_right,
    configurationVector_inner]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]
  unfold PosteriorPairProofs.overlap
  ring

theorem normalized_tensorSignal_inner_error {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (a : S → ℝ) {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K)
    (x y : Fin N → S) :
    |inner ℝ (tensorSignal a N k gamma x) (tensorSignal a N k gamma y)/(N:ℝ) -
      gamma*PosteriorPairProofs.overlap a (x,y)^k| ≤ gamma*(k:ℝ)^2*K^(2*k)/(N:ℝ) := by
  rw [normalized_tensorSignal_inner hN hk a hgamma, ← mul_sub, abs_mul, abs_of_nonneg hgamma]
  have h := TensorOverlapKernelProofs.abs_normalized_covariance_kernel_error_le hN hk
    (fun i ↦ a (x i)) (fun i ↦ a (y i)) hK (fun i ↦ ha (x i)) (fun i ↦ ha (y i))
  simpa only [PosteriorPairProofs.overlap, mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left h hgamma

variable [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem posterior_tensorMoment {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (posterior : Measure (Fin N → S)) [IsProbabilityMeasure posterior]
    (a : S → ℝ) {gamma : ℝ} (hgamma : 0 ≤ gamma) :
    ‖∫ x, tensorSignal a N k gamma x ∂posterior‖^2/(N:ℝ) =
      gamma*∫ z : (Fin N → S) × (Fin N → S),
        (Nat.factorial k : ℝ)*(∑ T : KSubset N k, ∏ n ∈ T.1, a (z.1 n)*a (z.2 n))/(N:ℝ)^k
        ∂posterior.prod posterior := by
  obtain ⟨C,_,hC⟩ := finite_signal_bound (tensorSignal a N k gamma)
  rw [norm_integral_sq_eq_replicaInner posterior _ (measurable_tensorSignal a N k gamma) (.of_forall hC),
    ← integral_div]
  simp_rw [normalized_tensorSignal_inner hN hk a hgamma]
  exact integral_const_mul _ _

theorem posterior_tensorMoment_error {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (posterior : Measure (Fin N → S)) [IsProbabilityMeasure posterior]
    (a : S → ℝ) {gamma K : ℝ} (hgamma : 0 ≤ gamma) (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K) :
    |‖∫ x, tensorSignal a N k gamma x ∂posterior‖^2/(N:ℝ) -
      gamma*∫ z, PosteriorPairProofs.overlap a z^k ∂posterior.prod posterior| ≤
      gamma*(k:ℝ)^2*K^(2*k)/(N:ℝ) := by
  obtain ⟨C,_,hC⟩ := finite_signal_bound (tensorSignal a N k gamma)
  rw [norm_integral_sq_eq_replicaInner posterior _ (measurable_tensorSignal a N k gamma) (.of_forall hC)]
  calc
    _ = |∫ z : (Fin N → S) × (Fin N → S),
        inner ℝ (tensorSignal a N k gamma z.1) (tensorSignal a N k gamma z.2)/(N:ℝ) -
        gamma*PosteriorPairProofs.overlap a z^k ∂posterior.prod posterior| := by
      rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_div, integral_const_mul]
    _ ≤ ∫ z : (Fin N → S) × (Fin N → S),
        |inner ℝ (tensorSignal a N k gamma z.1) (tensorSignal a N k gamma z.2)/(N:ℝ) -
          gamma*PosteriorPairProofs.overlap a z^k| ∂posterior.prod posterior := abs_integral_le_integral_abs
    _ ≤ ∫ _ : (Fin N → S) × (Fin N → S), gamma*(k:ℝ)^2*K^(2*k)/(N:ℝ)
        ∂posterior.prod posterior := integral_mono_ae Integrable.of_finite (integrable_const _)
      (.of_forall fun z ↦ normalized_tensorSignal_inner_error hN hk a hgamma hK ha z.1 z.2)
    _ = _ := by simp

theorem posterior_scalarMoment {N k : ℕ}
    (posterior : Measure (Fin N → S)) [IsProbabilityMeasure posterior]
    (a : S → ℝ) {gamma q : ℝ} (hgamma : 0 ≤ gamma) (hq : 0 ≤ q) :
    ‖∫ x, scalarSignal a N k gamma q x ∂posterior‖^2/(N:ℝ) =
      ((k:ℝ)*gamma*q^(k-1))*∫ z, PosteriorPairProofs.overlap a z ∂posterior.prod posterior := by
  obtain ⟨C,_,hC⟩ := finite_signal_bound (scalarSignal a N k gamma q)
  rw [norm_integral_sq_eq_replicaInner posterior _ (measurable_scalarSignal a N k gamma q) (.of_forall hC),
    ← integral_div]
  simp_rw [normalized_scalarSignal_inner a hgamma hq]
  exact integral_const_mul _ _

theorem posterior_signalResponse {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (posterior : Measure (Fin N → S)) [IsProbabilityMeasure posterior]
    (a : S → ℝ) {gamma q : ℝ} (hgamma : 0 ≤ gamma) (hq : 0 ≤ q) :
    (‖∫ x, tensorSignal a N k gamma x ∂posterior‖^2/(N:ℝ) -
      ‖∫ x, scalarSignal a N k gamma q x ∂posterior‖^2/(N:ℝ))/2 =
      (gamma/2)*∫ z : (Fin N → S) × (Fin N → S),
        (Nat.factorial k : ℝ)*(∑ T : KSubset N k, ∏ n ∈ T.1, a (z.1 n)*a (z.2 n))/(N:ℝ)^k -
          (k:ℝ)*q^(k-1)*PosteriorPairProofs.overlap a z ∂posterior.prod posterior := by
  rw [posterior_tensorMoment hN hk posterior a hgamma, posterior_scalarMoment posterior a hgamma hq,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul]
  ring


end TensorPCA.FinitePriorOverlapProofs
