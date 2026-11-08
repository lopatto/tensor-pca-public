-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityConditionalUpperProofs
public import TensorPCA.GuerraPinningProofs

/-! The random cavity center is compared with the global scalar RS
maximum. No pointwise bound by the prior second moment is assumed. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityUpperProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorScalarDomainProofs FinitePriorCavityConditionalUpperProofs
open PosteriorPairProofs FiniteRevealProofs
open FiniteRevealAveragingProofs GuerraPinningProofs
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] FiniteRevealProofs.posterior_probability
variable {S Y : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableSpace Y] {N : ℕ}

theorem scalarPotential_le_compactScalarValue (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hrho : scalarSecondMoment p a ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    scalarPotential p a k gamma Q ≤ sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1) := by
  obtain ⟨m,hm,hmax⟩ := exists_global_scalarMaximizer p a hk hgamma
  exact (hmax Q hQ).trans (le_csSup
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).bddAbove_image
      (continuous_scalarPotential p a k gamma).continuousOn)
    ⟨m,⟨hm.1,hm.2.trans hrho⟩,rfl⟩)

theorem integral_scalarPotential_meanOverlap_le_compact
    (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa]
    (nu : Measure Y) [IsProbabilityMeasure nu] (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (hN : 0 < N) {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hrho : scalarSecondMoment p a ≤ 1) :
    (∫ y, scalarPotential p a k gamma (meanOverlap (kappa y) a) ∂nu) ≤ sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1) := by
  obtain ⟨K,_,hK⟩ := finite_signal_bound a
  have hb (s : S) : |a s| ≤ K := by simpa only [Real.norm_eq_abs] using hK s
  have hI := integrable_scalarPotential_meanOverlap kappa nu p a k gamma hN hb
  have H := integral_mono hI (integrable_const (sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1)))
    (fun y ↦ scalarPotential_le_compactScalarValue p a hk hgamma hrho (meanOverlap_nonneg (kappa y) a))
  simpa only [integral_const,probReal_univ,one_smul] using H

section PhysicalAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

theorem uniform_reveal_scalarPotential_le_compact (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (B : (Fin N → S) → E) (hB : Measurable B) (hN : 0 < N)
    {k : ℕ} (hk : 2 ≤ k) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hrho : scalarSecondMoment p a ≤ 1) {delta : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) :
    uniformAverage Finset.univ delta (fun mask ↦ ∫ x, ∫ y,
      scalarPotential p a k gamma (meanOverlap
        (posteriorKernel (posterior (configurationPrior p N) mask x) B y) a)
      ∂mixtureLaw (posterior (configurationPrior p N) mask x) B ∂configurationPrior p N) ≤
      sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1) := by
  have H := uniform_reveal_mono (configurationPrior p N)
    (fun mask x ↦ ∫ y, scalarPotential p a k gamma (meanOverlap
      (posteriorKernel (posterior (configurationPrior p N) mask x) B y) a)
      ∂mixtureLaw (posterior (configurationPrior p N) mask x) B)
    (fun _ _ ↦ sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1)) (fun mask x ↦ by
      have : IsMarkovKernel (posteriorKernel (posterior (configurationPrior p N) mask x) B) :=
        posteriorKernel_isMarkov _ B hB
      have : IsProbabilityMeasure (mixtureLaw (posterior (configurationPrior p N) mask x) B) :=
        mixtureLaw_probability _ B hB
      exact integral_scalarPotential_meanOverlap_le_compact _ _ p a hN hk hgamma hrho) hd hd1
  change _ ≤ uniformAverage Finset.univ delta
    (fun _ ↦ ∫ _x, sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1) ∂configurationPrior p N) at H
  simp only [integral_const,probReal_univ,one_smul] at H
  rw [uniformAverage_const Finset.univ hd] at H
  exact H
end PhysicalAverage

end
end TensorPCA.FinitePriorCavityUpperProofs
