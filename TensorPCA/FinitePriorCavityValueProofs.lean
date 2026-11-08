-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityRateProofs
public import TensorPCA.FinitePriorCavityCommonUpperProofs
public import TensorPCA.FinitePriorCavityErrorLimitProofs
public import TensorPCA.FinitePriorValueReductionProofs

/-! Closure of the finite-prior RS limit through perturbed cavity increments. The zero-strength channel is retained explicitly. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityValueProofs
open Filter MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs FinitePriorChannelProofs
open FinitePriorCavityRateProofs FinitePriorCavityErrorLimitProofs FinitePriorValueReductionProofs
open FinitePriorCavityCommonUpperProofs FinitePriorCavityAveragingProofs FinitePriorScalarDomainProofs
open FinitePriorCavityScalarEndpointProofs GaussianFinitePriorApproximationLimitProofs
open scoped Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem tensorSignal_zero (a : S → ℝ) (N k : ℕ) : tensorSignal a N k 0 = fun _ ↦ 0 := by
  funext x
  ext T
  simp [tensorSignal,TensorOrbitAggregationProofs.unorderedSignal,
    TensorOrbitAggregationProofs.aggregateCoefficient]

theorem freeEnergy_zero (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) :
    freeEnergy p a N k 0 = 0 := by
  rw [freeEnergy,tensorSignal_zero,mixtureFreeEnergy_const]
  simp

theorem scalarPotential_zero (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (k : ℕ) (q : ℝ) :
    scalarPotential p a k 0 q = 0 := by
  simp [scalarPotential,mixtureFreeEnergy_const]

theorem compactScalarValue_zero (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (k : ℕ) :
    compactScalarValue p a k 0 = 0 := by
  have hi : scalarPotential p a k 0 '' Icc (0 : ℝ) 1 = {0} := by
    ext y
    constructor
    · rintro ⟨q,_,rfl⟩
      exact scalarPotential_zero p a k q
    · intro hy
      have hy0 : y = 0 := mem_singleton_iff.mp hy
      exact ⟨0,⟨le_rfl,zero_le_one⟩,by rw [scalarPotential_zero,hy0]⟩
  rw [compactScalarValue,hi,csSup_singleton]

/-- The finite-prior RS value is unconditional. The proof uses the perturbed increments, the pinning remainder, and vanishing reveal
costs, including the zero-strength edge case. -/
theorem finite_freeEnergy_tendsto (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hrho : scalarSecondMoment p a ≤ 1) :
    Filter.Tendsto (fun N : ℕ ↦ freeEnergy p a N k gamma) Filter.atTop
      (𝓝 (compactScalarValue p a k gamma)) := by
  by_cases hzero : gamma = 0
  · subst gamma
    simp only [freeEnergy_zero,compactScalarValue_zero]
    exact tendsto_const_nhds
  · have hgammaPos : 0 < gamma := lt_of_le_of_ne hgamma (Ne.symm hzero)
    obtain ⟨K,hK,hNorm⟩ := finite_signal_bound a
    have hb (s : S) : |a s| ≤ K := by simpa only [Real.norm_eq_abs] using hNorm s
    obtain ⟨C,hC,hCommon⟩ := exists_commonRate_increment_compact_upper_constant p a hk hgammaPos hK hb hrho
    apply finite_freeEnergy_tendsto_of_cavityIncrement (k := k) p a (by omega) hgamma
    intro epsilon hepsilon
    have hErr := (cavity_error_tendsto_zero C K (Real.log (Fintype.card S))).eventually
      (Iio_mem_nhds hepsilon)
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ),hErr] with N hN herr
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
    have hd : (0 : ℝ) < 1/Real.sqrt N := by positivity
    have hd1 : (1 : ℝ)/Real.sqrt N ≤ 1 :=
      (div_le_one (Real.sqrt_pos.mpr hn)).mpr (Real.one_le_sqrt.mpr hn1)
    have hStep := hCommon N hN (delta := 1/Real.sqrt N) hd hd1
    have hStep' : revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt N)-
        revealedFreeEnergyAtRate p a N k gamma (1/Real.sqrt N) ≤
        compactScalarValue p a k gamma+(1/Real.sqrt N)*Real.log (Fintype.card S)+
          C*(1/(N : ℝ)+Real.sqrt (4*K^4*Real.sqrt
            (Real.log (Fintype.card S)/((N : ℝ)*(1/Real.sqrt N))))) := by
      simpa only [compactScalarValue] using hStep
    have hRate := (le_abs_self (revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt (N+1 : ℕ))-
      revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt N))).trans
        (adjacent_reveal_rate_error_le p a hN k gamma)
    change revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt (N+1 : ℕ))-
      revealedFreeEnergyAtRate p a N k gamma (1/Real.sqrt N) ≤ compactScalarValue p a k gamma+epsilon
    have H : revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt (N+1 : ℕ))-
        revealedFreeEnergyAtRate p a N k gamma (1/Real.sqrt N) ≤ compactScalarValue p a k gamma+
        (C*(1/(N : ℝ)+Real.sqrt (4*K^4*Real.sqrt
          (Real.log (Fintype.card S)/((N : ℝ)*(1/Real.sqrt N)))))+
          (1/Real.sqrt N)*Real.log (Fintype.card S)+2*Real.log (Fintype.card S)/Real.sqrt (N+1 : ℕ)) := by
      linarith only [hStep',hRate]
    exact H.trans (by linarith only [herr])

end
end TensorPCA.FinitePriorCavityValueProofs
