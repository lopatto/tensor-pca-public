-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.GaussianRevealPinningProofs
public import TensorPCA.FinitePriorOverlapProofs

/-! # Finite-prior revealed Guerra interpolation and its derivative -/
@[expose] public section

namespace TensorPCA.FinitePriorRevealedInterpolationProofs

open MeasureTheory ProbabilityTheory GaussianSideChannelProofs GaussianReplicaTransportProofs
open GaussianTwoChannelFreeEnergyProofs GaussianTwoStrengthCalculusProofs GaussianRevealReplicaProofs
open GaussianCombinedPosteriorProofs GaussianRevealPinningProofs FinitePriorChannelProofs
open FinitePriorOverlapProofs FiniteRevealProofs FiniteRevealAveragingProofs GuerraPinningProofs

attribute [local instance] posterior_probability

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] {N k : ℕ}

noncomputable def tensorResponse (a : S → ℝ) (k : ℕ) (m : ℝ)
    (z : (Fin N → S) × (Fin N → S)) : ℝ :=
  tensorOverlapKernel a k z-(k:ℝ)*m^(k-1)*PosteriorPairProofs.overlap a z

noncomputable def revealedInterpolation (mu : Measure (Fin N → S)) (a : S → ℝ)
    (k : ℕ) (gamma m delta t : ℝ) : ℝ :=
  uniformAverage Finset.univ delta (fun mask ↦ ∫ x,
    twoChannelFreeEnergy (posterior mu mask x)
      (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
      (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) / (N:ℝ) ∂mu)

theorem uniformAverage_const_mul {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (delta : ℝ) (F : Finset ι → ℝ) (c : ℝ) :
    uniformAverage I delta (fun mask ↦ c*F mask) = c*uniformAverage I delta F := by
  unfold uniformAverage
  simp_rw [BayesianPinningVarianceProofs.average_const_mul]
  exact integral_const_mul _ _

theorem integrable_combinedMean_sq {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (A : (Fin N → S) → EuclideanSpace ℝ ι) (B : (Fin N → S) → EuclideanSpace ℝ κ)
    (C : (Fin N → S) → EuclideanSpace ℝ ν) :
    Integrable (fun y ↦ ‖combinedMean mu A B C y‖^2) (pairObservationLaw mu A B) := by
  have : IsProbabilityMeasure (pairObservationLaw mu A B) :=
    pairObservationLaw_probability mu A B (measurable_of_finite _) (measurable_of_finite _)
  obtain ⟨K,hK,hCB⟩ := finite_signal_bound C
  refine Integrable.of_bound
    ((stronglyMeasurable_combinedMean mu A B C (measurable_of_finite _).stronglyMeasurable).norm.pow 2).aestronglyMeasurable (K^2) ?_
  exact .of_forall fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_combinedMean_le mu A B
      (measurable_of_finite _) (measurable_of_finite _) C (.of_forall hCB) y) 2

theorem finite_guerra_replica_hasDerivAt
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu] (a : S → ℝ)
    (hN : 0 < N) (hk : 0 < k) {gamma m t : ℝ} (hgamma : 0 ≤ gamma) (hm : 0 ≤ m)
    (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun u ↦ twoChannelFreeEnergy mu
        (fun v ↦ Real.sqrt u • tensorSignal a N k gamma v)
        (fun v ↦ Real.sqrt (1-u) • scalarSignal a N k gamma m v) / (N:ℝ))
      ((gamma/2)*∫ y, ∫ z, tensorResponse a k m z
        ∂(combinedPosteriorKernel mu
          (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
          (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y).prod
          (combinedPosteriorKernel mu
          (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
          (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y)
        ∂pairObservationLaw mu
          (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
          (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v)) t := by
  let A := tensorSignal a N k gamma
  let B := scalarSignal a N k gamma m
  let At := fun v ↦ Real.sqrt t • A v
  let Bt := fun v ↦ Real.sqrt (1-t) • B v
  have hA : Measurable A := measurable_of_finite _
  have hB : Measurable B := measurable_of_finite _
  have hAt : Measurable At := measurable_of_finite _
  have hBt : Measurable Bt := measurable_of_finite _
  have : IsMarkovKernel (combinedPosteriorKernel mu At Bt) := combinedPosteriorKernel_isMarkov mu At Bt hAt hBt
  obtain ⟨KA,hKA,hAB⟩ := finite_signal_bound A
  obtain ⟨KB,hKB,hBB⟩ := finite_signal_bound B
  have hd := (hasDerivAt_guerraPath_commonPosterior mu A B hA hB hKA hKB
    (.of_forall hAB) (.of_forall hBB) ht0 ht1).div_const (N:ℝ)
  have hiA := integrable_combinedMean_sq mu At Bt A
  have hiB := integrable_combinedMean_sq mu At Bt B
  have heq : (((1/2:ℝ)*∫ y, ‖combinedMean mu At Bt A y‖^2 ∂pairObservationLaw mu At Bt)-
      (1/2:ℝ)*∫ y, ‖combinedMean mu At Bt B y‖^2 ∂pairObservationLaw mu At Bt)/(N:ℝ) =
      (gamma/2)*∫ y, ∫ z, tensorResponse a k m z
        ∂(combinedPosteriorKernel mu At Bt y).prod (combinedPosteriorKernel mu At Bt y)
        ∂pairObservationLaw mu At Bt := by
    calc
      _ = ∫ y, (‖combinedMean mu At Bt A y‖^2/(N:ℝ)-
          ‖combinedMean mu At Bt B y‖^2/(N:ℝ))/2 ∂pairObservationLaw mu At Bt := by
        rw [integral_div, integral_sub (hiA.div_const _) (hiB.div_const _), integral_div, integral_div]
        ring
      _ = ∫ y, (gamma/2)*∫ z, tensorResponse a k m z
          ∂(combinedPosteriorKernel mu At Bt y).prod (combinedPosteriorKernel mu At Bt y)
          ∂pairObservationLaw mu At Bt := by
        apply integral_congr_ae
        exact .of_forall fun y ↦ posterior_signalResponse hN hk (combinedPosteriorKernel mu At Bt y) a hgamma hm
      _ = _ := integral_const_mul _ _
  rw [heq] at hd
  exact hd

noncomputable def revealedResponse (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu]
    (a : S → ℝ) (k : ℕ) (gamma m delta t : ℝ) : ℝ :=
  uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y, ∫ z, tensorResponse a k m z
    ∂(combinedPosteriorKernel (posterior mu mask x)
      (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
      (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y).prod
      (combinedPosteriorKernel (posterior mu mask x)
      (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
      (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y)
    ∂pairObservationLaw (posterior mu mask x)
      (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
      (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) ∂mu)

theorem revealedInterpolation_hasDerivAt
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu] (a : S → ℝ)
    (hN : 0 < N) (hk : 0 < k) {gamma m delta t : ℝ} (hgamma : 0 ≤ gamma) (hm : 0 ≤ m)
    (hd0 : 0 < delta) (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (revealedInterpolation mu a k gamma m delta)
      ((gamma/2)*revealedResponse mu a k gamma m delta t) t := by
  have hd := uniformAverage_hasDerivAt Finset.univ hd0
    (fun mask u ↦ ∫ x, twoChannelFreeEnergy (posterior mu mask x)
      (fun v ↦ Real.sqrt u • tensorSignal a N k gamma v)
      (fun v ↦ Real.sqrt (1-u) • scalarSignal a N k gamma m v)/(N:ℝ) ∂mu)
    (fun mask ↦ ∫ x, (gamma/2)*∫ y, ∫ z, tensorResponse a k m z
      ∂(combinedPosteriorKernel (posterior mu mask x)
        (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
        (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y).prod
        (combinedPosteriorKernel (posterior mu mask x)
        (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
        (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) y)
      ∂pairObservationLaw (posterior mu mask x)
        (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
        (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v) ∂mu)
    (fun mask ↦ finite_integral_hasDerivAt mu _ _ (fun x ↦
      finite_guerra_replica_hasDerivAt (posterior mu mask x) a hN hk hgamma hm ht0 ht1))
  simp_rw [integral_const_mul] at hd
  rw [uniformAverage_const_mul] at hd
  exact hd

theorem revealedResponse_lower_bound
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu] (a : S → ℝ)
    (hN : 0 < N) (hk : 0 < k) {K gamma m delta t : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K)
    (hm : 0 ≤ m) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    (1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
      (k : ℝ)^2*K^(2*k)/(N : ℝ) ≤ revealedResponse mu a k gamma m delta t := by
  exact actual_gaussian_pinning_tensor_response_lower_bound mu
    (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
    (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v)
    (measurable_of_finite _) (measurable_of_finite _) a hN hK ha hk hm hd0 hd1

theorem continuous_revealedInterpolation
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu] (a : S → ℝ)
    (k : ℕ) (gamma m : ℝ) {delta : ℝ} (hd0 : 0 < delta) :
    Continuous (revealedInterpolation mu a k gamma m delta) := by
  have hc (nu : Measure (Fin N → S)) [IsProbabilityMeasure nu] :
      Continuous (fun t ↦ twoChannelFreeEnergy nu
        (fun v ↦ Real.sqrt t • tensorSignal a N k gamma v)
        (fun v ↦ Real.sqrt (1-t) • scalarSignal a N k gamma m v)/(N:ℝ)) := by
    obtain ⟨KA,hKA,hAB⟩ := finite_signal_bound (tensorSignal a N k gamma)
    obtain ⟨KB,hKB,hBB⟩ := finite_signal_bound (scalarSignal a N k gamma m)
    have hg : Continuous (fun q : ℝ × ℝ ↦ twoChannelFreeEnergy nu
        (fun v ↦ q.1 • tensorSignal a N k gamma v)
        (fun v ↦ q.2 • scalarSignal a N k gamma m v)) :=
      Differentiable.continuous (fun q ↦ differentiableAt_twoChannelFreeEnergy nu
        (tensorSignal a N k gamma) (scalarSignal a N k gamma m)
        (measurable_of_finite _) (measurable_of_finite _) hKA hKB
        (.of_forall hAB) (.of_forall hBB) q)
    exact (hg.comp (Real.continuous_sqrt.prodMk (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id)))).div_const _
  unfold revealedInterpolation
  apply continuous_uniformAverage Finset.univ hd0
  intro mask
  simp_rw [integral_fintype Integrable.of_finite, smul_eq_mul]
  exact continuous_finsetSum _ (fun x _ ↦ continuous_const.mul (hc (posterior mu mask x)))

/-- A genuine finite endpoint lower bound, obtained by derivative comparison.
Neither endpoint differentiability nor an unproved FTC premise is used. -/
theorem revealedInterpolation_endpoint_lower_bound
    (mu : Measure (Fin N → S)) [IsProbabilityMeasure mu] (a : S → ℝ)
    (hN : 0 < N) (hk : 0 < k) {K gamma m delta : ℝ} (hK : 0 ≤ K) (ha : ∀ s, |a s| ≤ K)
    (hgamma : 0 ≤ gamma) (hm : 0 ≤ m) (hd0 : 0 < delta) (hd1 : delta ≤ 1) :
    revealedInterpolation mu a k gamma m delta 0 + (gamma/2)*
      ((1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
        Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
        (k : ℝ)^2*K^(2*k)/(N : ℝ)) ≤
      revealedInterpolation mu a k gamma m delta 1 := by
  let L := (gamma/2)*((1-(k : ℝ))*m^k-(k : ℝ)*((K^2)^(k-1)+m^(k-1))*
    Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))-
    (k : ℝ)^2*K^(2*k)/(N : ℝ))
  let f := fun t ↦ revealedInterpolation mu a k gamma m delta t-L*t
  have hcont : Continuous f := (continuous_revealedInterpolation mu a k gamma m hd0).sub
    (continuous_const.mul continuous_id)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont.continuousOn
      (f' := fun t ↦ (gamma/2)*revealedResponse mu a k gamma m delta t-L)
    · intro t ht
      have ht' : 0 < t ∧ t < 1 := by simpa only [interior_Icc, Set.mem_Ioo] using ht
      have hd := (revealedInterpolation_hasDerivAt mu a hN hk hgamma hm hd0 ht'.1 ht'.2).sub
        ((hasDerivAt_id t).const_mul L)
      simp only [mul_one] at hd
      convert hd.hasDerivWithinAt using 1
      rfl
    · intro t _
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
        (revealedResponse_lower_bound mu a hN hk hK ha hm hd0 hd1) (by positivity))
  have h := hmono (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨le_rfl,zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 from ⟨zero_le_one,le_rfl⟩) zero_le_one
  dsimp only [f] at h
  simpa only [mul_zero, sub_zero, mul_one, le_sub_iff_add_le] using h


end TensorPCA.FinitePriorRevealedInterpolationProofs
