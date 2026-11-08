-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorGuerraAsymptoticProofs
public import TensorPCA.GaussianFinitePriorApproximationLimitProofs

/-! Finite-prior value reduction from an explicit increment bound for the
reveal-perturbed free energy. Its normalized reveal cost vanishes, and the
lower bound follows from the finite Guerra theorem. -/
@[expose] public section
namespace TensorPCA.FinitePriorValueReductionProofs
open Set Filter MeasureTheory ProbabilityTheory GaussianPriorTransferProofs
open FinitePriorChannelProofs FinitePriorGuerraAsymptoticProofs
open GaussianFinitePriorApproximationLimitProofs
open FinitePriorGuerraLowerProofs FiniteRevealAveragingProofs FiniteRevealProofs
open FinitePriorRevealedInterpolationProofs FiniteRevealFreeEnergyProofs
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- An eventual upper bound for consecutive increments bounds the normalized
sequence. The finite initial segment is retained as an explicit C/N term. -/
theorem normalized_eventual_upper_of_increment (u : ℕ → ℝ) (V : ℝ)
    (hinc : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop, u (n+1)-u n ≤ V+epsilon)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, u n/(n : ℝ) ≤ V+epsilon := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hinc (epsilon/2) (by positivity))
  let c := V+epsilon/2
  let C := u M-c*(M : ℝ)
  have hlin : ∀ n : ℕ, M ≤ n → u n ≤ c*(n : ℝ)+C := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => dsimp [C]; linarith
    | succ n hn ih =>
      have H := hM n hn
      change u (n+1)-u n ≤ c at H
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hsmall : ∀ᶠ n : ℕ in atTop, C/(n : ℝ) < epsilon/2 :=
    (tendsto_const_div_atTop_nhds_zero_nat C).eventually (Iio_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop M,eventually_gt_atTop (0 : ℕ),hsmall] with n hn hpos hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hpos
  have H := div_le_div_of_nonneg_right (hlin n hn) hnR.le
  rw [add_div,mul_div_cancel_right₀ _ hnR.ne'] at H
  dsimp [c] at H
  linarith

section ActualReveal
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Actual unnormalized free energy averaged over independent coordinate
reveals with a uniform reveal parameter in[0,1/sqrt N]. The zero-dimensional
convention has no role in the eventual positive-dimensional estimates. -/
def revealPerturbedFreeEnergy (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (N k : ℕ) (gamma : ℝ) : ℝ :=
  uniformAverage Finset.univ (1/Real.sqrt N) (fun mask => ∫ x,
    mixtureFreeEnergy (posterior (configurationPrior p N) mask x)
      (tensorSignal a N k gamma) ∂configurationPrior p N)

omit [Fintype S] [MeasurableSingletonClass S] in
theorem revealPerturbedFreeEnergy_div_eq (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    (N k : ℕ) (gamma : ℝ) :
    revealPerturbedFreeEnergy p a N k gamma/(N : ℝ) =
      revealedSingleChannel (configurationPrior p N) (tensorSignal a N k gamma) (1/Real.sqrt N) := by
  unfold revealPerturbedFreeEnergy revealedSingleChannel
  simp_rw [integral_div]
  have H := uniformAverage_const_mul Finset.univ (1/Real.sqrt N)
    (fun mask => ∫ x, mixtureFreeEnergy (posterior (configurationPrior p N) mask x)
      (tensorSignal a N k gamma) ∂configurationPrior p N) ((N : ℝ)⁻¹)
  simpa only [div_eq_mul_inv,mul_comm] using H.symm

omit [Fintype S] [MeasurableSingletonClass S] in
theorem revealPerturbedFreeEnergy_eq_raw_add_cost (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) (gamma : ℝ) :
    revealPerturbedFreeEnergy p a N k gamma =
      mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma)+
        uniformAverage Finset.univ (1/Real.sqrt N)
          (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma)) := by
  have hd : 0 < (1 : ℝ)/Real.sqrt N := by positivity
  have H := uniformAverage_const (Finset.univ : Finset (Fin N)) hd
    (mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma))
  rw [uniformAverage_eq_sum Finset.univ hd] at H
  unfold revealPerturbedFreeEnergy
  rw [uniformAverage_eq_sum Finset.univ hd,uniformAverage_eq_sum Finset.univ hd]
  unfold revealFreeEnergyCost
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,H]
  ring

theorem revealPerturbedFreeEnergy_normalized_bounds (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) (gamma : ℝ) :
    freeEnergy p a N k gamma ≤ revealPerturbedFreeEnergy p a N k gamma/(N : ℝ) ∧
      revealPerturbedFreeEnergy p a N k gamma/(N : ℝ) ≤ freeEnergy p a N k gamma+
        (1/Real.sqrt N)*Real.log (Fintype.card S) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [revealPerturbedFreeEnergy_div_eq]
  exact revealedSingleChannel_bounds (configurationPrior p N) (tensorSignal a N k gamma) hN
    (by positivity) ((div_le_one (Real.sqrt_pos.mpr hn)).mpr (Real.one_le_sqrt.mpr hn1))

theorem revealPerturbedFreeEnergy_normalized_difference_tendsto (p : Measure S)
    [IsProbabilityMeasure p] (a : S → ℝ) (k : ℕ) (gamma : ℝ) :
    Tendsto (fun N : ℕ => revealPerturbedFreeEnergy p a N k gamma/(N : ℝ)-freeEnergy p a N k gamma)
      atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have H : Tendsto (fun N : ℕ => (1/Real.sqrt N)*Real.log (Fintype.card S)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using (hs.const_div_atTop 1).mul_const (Real.log (Fintype.card S))
  apply squeeze_zero' _ _ H
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact sub_nonneg.mpr (revealPerturbedFreeEnergy_normalized_bounds p a hN k gamma).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    linarith [(revealPerturbedFreeEnergy_normalized_bounds p a hN k gamma).2]
end ActualReveal

/-- The conditional reduction uses the actual perturbed increments. An
absolute O(N*delta) reveal cost is not used to bound unperturbed increments. -/
theorem finite_freeEnergy_tendsto_of_cavityIncrement
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 0 < k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hIncrement : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop,
      revealPerturbedFreeEnergy p a (N+1) k gamma-revealPerturbedFreeEnergy p a N k gamma ≤
          compactScalarValue p a k gamma+epsilon) :
    Tendsto (fun N : ℕ => freeEnergy p a N k gamma) atTop
      (𝓝 (compactScalarValue p a k gamma)) := by
  let V := compactScalarValue p a k gamma
  let u := fun N : ℕ => revealPerturbedFreeEnergy p a N k gamma
  have hupper {epsilon : ℝ} (hepsilon : 0 < epsilon) :
      ∀ᶠ N : ℕ in atTop, freeEnergy p a N k gamma ≤ V+epsilon := by
    filter_upwards [normalized_eventual_upper_of_increment u V hIncrement hepsilon,
      eventually_gt_atTop (0 : ℕ)] with N hN hpos
    exact (revealPerturbedFreeEnergy_normalized_bounds p a hpos k gamma).1.trans hN
  let e := fun j : ℕ => (1 : ℝ)/((j : ℝ)+1)
  have he (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply LimitTools.tendsto_of_eventual_envelopes
    (lo := fun j _ => V-e j) (hi := fun j _ => V+e j)
    (a := fun j => V-e j) (b := fun j => V+e j)
  · intro j; exact tendsto_const_nhds
  · intro j; exact tendsto_const_nhds
  · intro j
    have Hlo := finite_guerra_compact_eventual_lower p a hk hgamma (he j)
    exact Hlo.and (hupper (he j))
  · simpa only [sub_zero] using tendsto_const_nhds.sub helim
  · simpa only [add_zero] using tendsto_const_nhds.add helim


end
end TensorPCA.FinitePriorValueReductionProofs
