-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityAveragingProofs
public import TensorPCA.FiniteRevealFreeEnergyLipschitzProofs

/-! Adjacent-dimension reveal rates differ by a vanishing unnormalized
cost. The common-rate cavity estimate applies to the perturbed sequence. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityRateProofs
open MeasureTheory ProbabilityTheory Set FinitePriorChannelProofs GaussianPriorTransferProofs
open FinitePriorCavityAveragingProofs
open FiniteRevealAveragingProofs FiniteRevealFreeEnergyProofs FiniteRevealFreeEnergyLipschitzProofs
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem revealedFreeEnergyAtRate_lipschitz (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (N k : ℕ) (gamma : ℝ) {delta delta' : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hd' : 0 < delta') (hd1' : delta' ≤ 1) :
    |revealedFreeEnergyAtRate p a N k gamma delta-revealedFreeEnergyAtRate p a N k gamma delta'| ≤
      (N : ℝ)*|delta-delta'| *Real.log (Fintype.card S) := by
  obtain ⟨K,_,hFB⟩ := finite_signal_bound (tensorSignal a N k gamma)
  have H := uniform_revealFreeEnergyCost_lipschitz (configurationPrior p N) (tensorSignal a N k gamma)
    (measurable_of_finite _) (Filter.Eventually.of_forall hFB) hd hd1 hd' hd1'
  rw [revealedFreeEnergyAtRate_eq_raw_add_cost p a N k gamma hd,
    revealedFreeEnergyAtRate_eq_raw_add_cost p a N k gamma hd']
  have hEq : (mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma)+
      uniformAverage Finset.univ delta (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma)))-
      (mixtureFreeEnergy (configurationPrior p N) (tensorSignal a N k gamma)+
      uniformAverage Finset.univ delta' (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma))) =
      uniformAverage Finset.univ delta (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma))-
      uniformAverage Finset.univ delta' (revealFreeEnergyCost (configurationPrior p N) (tensorSignal a N k gamma)) := by ring
  rw [hEq]
  exact H

/-- Changing the N+1 system from its own rate to the common N-system rate
costs at most 2 log(card S)/sqrt(N+1), before division by dimension. -/
theorem adjacent_reveal_rate_error_le (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) (gamma : ℝ) :
    |revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt (N+1 : ℕ))-
      revealedFreeEnergyAtRate p a (N+1) k gamma (1/Real.sqrt N)| ≤
      2*Real.log (Fintype.card S)/Real.sqrt (N+1 : ℕ) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hn1 : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hn2 : (1 : ℝ) ≤ (n+1+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n+1))
  have hd1 : 0 < (1 : ℝ)/Real.sqrt (n+1 : ℕ) := by positivity
  have hd2 : 0 < (1 : ℝ)/Real.sqrt (n+1+1 : ℕ) := by positivity
  have hd1' : (1 : ℝ)/Real.sqrt (n+1 : ℕ) ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr (Real.one_le_sqrt.mpr hn1)
  have hd2' : (1 : ℝ)/Real.sqrt (n+1+1 : ℕ) ≤ 1 :=
    (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr (Real.one_le_sqrt.mpr hn2)
  have : Nonempty S := nonempty_of_isProbabilityMeasure p
  have hlog : 0 ≤ Real.log (Fintype.card S) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  have hRate := revealedFreeEnergyAtRate_lipschitz p a (n+1+1) k gamma hd2 hd2' hd1 hd1'
  have hSmall := squareRootRevealRate_increment_le n
  have hCoef : ((n+1+1 : ℕ) : ℝ)*|1/Real.sqrt (n+1+1 : ℕ)-1/Real.sqrt (n+1 : ℕ)| ≤
      2*(1/Real.sqrt (n+1+1 : ℕ)) := by
    have hDim : ((n+1+1 : ℕ) : ℝ) ≤ 2*((n+1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n+1+1 ≤ 2*(n+1))
    have hMul := mul_le_mul_of_nonneg_left hSmall (by norm_num : (0 : ℝ) ≤ 2)
    exact (mul_le_mul_of_nonneg_right hDim (abs_nonneg _)).trans
      (by simpa only [mul_assoc] using hMul)
  change |revealedFreeEnergyAtRate p a (n+1+1) k gamma (1/Real.sqrt (n+1+1 : ℕ))-
    revealedFreeEnergyAtRate p a (n+1+1) k gamma (1/Real.sqrt (n+1 : ℕ))| ≤ _
  exact hRate.trans ((mul_le_mul_of_nonneg_right hCoef hlog).trans_eq (by ring))

end
end TensorPCA.FinitePriorCavityRateProofs
