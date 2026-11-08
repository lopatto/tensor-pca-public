-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GuerraRemainderProofs
public import TensorPCA.TensorOverlapKernelProofs

/-! Uniform-parameter reveal averaging of the signed Guerra response.
Only thermal fluctuations around the random posterior center are controlled. -/
@[expose] public section
namespace TensorPCA.GuerraPinningProofs
open MeasureTheory ProbabilityTheory Set Real PosteriorPairProofs FiniteRevealProofs
open RevealPolynomialProofs BayesianPinningProofs BayesianPinningVarianceProofs GuerraRemainderProofs
open TensorOrbitCountProofs TensorOverlapKernelProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {N : ℕ} (q : Measure (Configuration S N)) [IsProbabilityMeasure q]

theorem uniform_reveal_mono (f g : Finset (Fin N) → Configuration S N → ℝ)
    (hfg : ∀ A x, f A x ≤ g A x) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, f A x ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ≤
    ∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, g A x ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta) := by
  have := uniformInterval_probability hd0
  apply integral_mono_ae
    ((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl)
    ((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl)
  exact ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦
    average_mono _ _ _ ht.1 (ht.2.trans hd1) (fun A ↦
      integral_mono_ae Integrable.of_finite Integrable.of_finite
        (Filter.Eventually.of_forall (hfg A))))

theorem uniform_reveal_affine (f : Finset (Fin N) → Configuration S N → ℝ)
    (c C : ℝ) {delta : ℝ} (hd0 : 0 < delta) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, c-C*f A x ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) =
    c-C*(∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, f A x ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) := by
  have := uniformInterval_probability hd0
  simp_rw [integral_sub (integrable_const _) Integrable.of_finite,
    integral_const_mul, integral_const, probReal_univ, one_smul,
    BayesianPinningVarianceProofs.average_sub, BayesianPinningVarianceProofs.average_const,
    BayesianPinningVarianceProofs.average_const_mul]
  rw [integral_sub (integrable_const _)
    (((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl).const_mul C),
    integral_const_mul, integral_const, probReal_univ, one_smul]

theorem uniform_reveal_sqrt_le (f : Finset (Fin N) → Configuration S N → ℝ)
    (hf : ∀ A x, 0 ≤ f A x) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, Real.sqrt (f A x) ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) ≤
    Real.sqrt (∫ theta, RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, f A x ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)) := by
  have := uniformInterval_probability hd0
  have hm {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
      RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, Real.sqrt (f A x) ∂q) theta ≤
      Real.sqrt (RevealPolynomialProofs.average Finset.univ (fun A ↦ ∫ x, f A x ∂q) theta) := by
    calc
      _ ≤ RevealPolynomialProofs.average Finset.univ (fun A ↦ Real.sqrt (∫ x, f A x ∂q)) theta :=
        average_mono _ _ _ h0 h1 (fun A ↦ integral_sqrt_le_sqrt_integral q
          (Filter.Eventually.of_forall (hf A)) MemLp.of_discrete)
      _ ≤ _ := average_sqrt_le _ _ (fun A ↦ integral_nonneg (hf A)) h0 h1
  have hc := (average_continuous Finset.univ (fun A ↦ ∫ x, f A x ∂q)).sqrt
  have H := integral_mono_ae
    ((memLp_uniformInterval (average_continuous _ _) hd0 1).integrable le_rfl)
    ((memLp_uniformInterval hc hd0 1).integrable le_rfl)
    (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ hm ht.1 (ht.2.trans hd1)))
  refine H.trans ?_
  exact integral_sqrt_le_sqrt_integral _
    (ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ average_nonneg _ _
      ht.1 (ht.2.trans hd1) (fun A _ ↦ integral_nonneg (hf A))))
    (memLp_uniformInterval hc hd0 2)

/-- The actual signed response after pinning has a vanishing thermal error;
the posterior center is never replaced by its external-disorder mean. -/
theorem finite_pinning_power_response_lower_bound (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) {k : ℕ} (hk : 0 < k)
    {m : ℝ} (hm : 0 ≤ m) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta))) ≤
    ∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, ∫ z : Configuration S N × Configuration S N,
        (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z
        ∂(posterior q A x).prod (posterior q A x) ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta) := by
  have hC : 0 ≤ (k : ℝ)*((K^2)^(k-1)+m^(k-1)) := by positivity
  have H := uniform_reveal_mono q
    (fun A x ↦ (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (replicaVariance (posterior q A x) a))
    (fun A x ↦ ∫ z, (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z
      ∂(posterior q A x).prod (posterior q A x))
    (fun A x ↦ by
      have := posterior_probability q A x
      exact posterior_power_response_lower_bound _ a hN hK hb hk hm) hd0 hd1
  rw [uniform_reveal_affine q _ _ _ hd0] at H
  have hj := uniform_reveal_sqrt_le q (fun A x ↦ replicaVariance (posterior q A x) a)
    (fun A x ↦ integral_nonneg (fun z ↦ sq_nonneg _)) hd0 hd1
  have he := hj.trans (Real.sqrt_le_sqrt (finite_pinning_replica_variance_bound q a hN hK hb hd0 hd1))
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left he hC) _).trans H

def tensorOverlapKernel (a : S → ℝ) (k : ℕ) (z : Configuration S N × Configuration S N) : ℝ :=
  ((Nat.factorial k : ℝ)*(∑ T : KSubset N k, ∏ i ∈ T.1, a (z.1 i)*a (z.2 i)))/(N : ℝ)^k

theorem tensor_response_mean_ge_power_response_sub_error (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) {k : ℕ} (hk : 0 < k) (m : ℝ) :
    (∫ z, (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z ∂q.prod q)-
      (k : ℝ)^2*K^(2*k)/(N : ℝ) ≤
    ∫ z, tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*overlap a z ∂q.prod q := by
  have H := integral_mono_ae (μ := q.prod q)
    (f := fun z ↦ ((overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z)-
      (k : ℝ)^2*K^(2*k)/(N : ℝ))
    (g := fun z ↦ tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*overlap a z)
    Integrable.of_finite Integrable.of_finite (Filter.Eventually.of_forall (fun z ↦ by
      have h := abs_normalized_covariance_kernel_error_le hN hk
        (fun i ↦ a (z.1 i)) (fun i ↦ a (z.2 i)) hK (fun i ↦ hb _) (fun i ↦ hb _)
      change |tensorOverlapKernel a k z-(overlap a z)^k| ≤ _ at h
      linarith [(abs_le.mp h).1]))
  simpa only [integral_sub Integrable.of_finite (integrable_const _), integral_const,
    probReal_univ, one_smul] using H

/-- The normalized unordered tensor response has the same lower bound,
plus the explicitly proved finite collision correction. -/
theorem finite_pinning_tensor_response_lower_bound (a : S → ℝ) (hN : 0 < N)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) {k : ℕ} (hk : 0 < k)
    {m : ℝ} (hm : 0 ≤ m) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
      (k : ℝ)^2*K^(2*k)/(N : ℝ) ≤
    ∫ theta, RevealPolynomialProofs.average Finset.univ
      (fun A ↦ ∫ x, ∫ z : Configuration S N × Configuration S N,
        tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*overlap a z
        ∂(posterior q A x).prod (posterior q A x) ∂q) theta
      ∂ProbabilityTheory.cond volume (Icc (0 : ℝ) delta) := by
  have H := uniform_reveal_mono q
    (fun A x ↦ -((k : ℝ)^2*K^(2*k)/(N : ℝ))-(-1)*
      (∫ z, (overlap a z)^k-(k : ℝ)*m^(k-1)*overlap a z
        ∂(posterior q A x).prod (posterior q A x)))
    (fun A x ↦ ∫ z, tensorOverlapKernel a k z-(k : ℝ)*m^(k-1)*overlap a z
      ∂(posterior q A x).prod (posterior q A x))
    (fun A x ↦ by
      have := posterior_probability q A x
      have h := tensor_response_mean_ge_power_response_sub_error (posterior q A x) a hN hK hb hk m
      linarith) hd0 hd1
  rw [uniform_reveal_affine q _ _ _ hd0] at H
  have hs := finite_pinning_power_response_lower_bound q a hN hK hb hk hm hd0 hd1
  linarith

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem squareRootRevealRate_mem (n : ℕ) :
    0 < 1/Real.sqrt (n+1 : ℕ) ∧ 1/Real.sqrt (n+1 : ℕ) ≤ 1 := by
  have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hr : 0 < Real.sqrt (n+1 : ℕ) := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hn)
  exact ⟨div_pos zero_lt_one hr,(div_le_one hr).mpr (Real.one_le_sqrt.mpr hn)⟩

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
/-- With dimension n+1 and reveal rate 1/sqrt(n+1), the explicit thermal
pinning error tends to zero. This needs no rate or concentration hypothesis. -/
theorem pinning_error_tendsto_zero (H C K : ℝ) :
    Filter.Tendsto (fun n : ℕ ↦ C*Real.sqrt (4*K^4*Real.sqrt
      (H/(((n+1 : ℕ) : ℝ)*(1/Real.sqrt (n+1 : ℕ)))))) Filter.atTop (nhds 0) := by
  have hd : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n+1 : ℕ)) Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using Real.tendsto_sqrt_atTop.comp hd
  have hz := (((hs.const_div_atTop H).sqrt.const_mul (4*K^4)).sqrt.const_mul C)
  have he (n : ℕ) : ((n+1 : ℕ) : ℝ)*(1/Real.sqrt (n+1 : ℕ)) = Real.sqrt (n+1 : ℕ) := by
    have hn : (0 : ℝ) < (n+1 : ℕ) := by positivity
    have hr := Real.sqrt_pos.mpr hn
    field_simp [hr.ne']
    nlinarith [Real.sq_sqrt hn.le]
  simp_rw [he]
  simpa only [Real.sqrt_zero, mul_zero] using hz

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure q] in
theorem pinning_tensor_error_tendsto_zero (H C K : ℝ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦ C*Real.sqrt (4*K^4*Real.sqrt
      (H/(((n+1 : ℕ) : ℝ)*(1/Real.sqrt (n+1 : ℕ)))))+
      (k : ℝ)^2*K^(2*k)/((n+1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
  have hd : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)+1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
    (pinning_error_tendsto_zero H C K).add (hd.const_div_atTop ((k : ℝ)^2*K^(2*k)))

end
end TensorPCA.GuerraPinningProofs
