-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityAveragingProofs
public import TensorPCA.FinitePriorCavityConditionalUpperProofs

/-! Removing the fresh-coordinate reveal bit from the scalar cavity
potential. The background depends on old coordinates only. Its Gaussian law
and the fresh symbol are integrated using their product law. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityLastRevealProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorCavityFieldProofs FinitePriorCavityPartitionProofs
open FinitePriorCavityConditionalUpperProofs FinitePriorCavityAveragingProofs FinitePriorCavityPinningProofs
open FinitePriorCavityRevealedIncrementProofs FiniteRevealProofs TensorCavitySubsetProofs PosteriorPairProofs
open RevealPolynomialProofs BayesianPinningVarianceProofs
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] FiniteRevealProofs.posterior_probability

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem kernel_lastReveal_scalarPotential_cost_bounds
    {Y : Type*} [MeasurableSpace Y] {N : ℕ}
    (kappa : Kernel Y (Fin N → S)) [IsMarkovKernel kappa]
    (nu : Measure Y) [IsProbabilityMeasure nu] (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) (k : ℕ) (gamma : ℝ) (hN : 0 < N) {K : ℝ} (hb : ∀ s, |a s| ≤ K)
    {theta : ℝ} (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    0 ≤ (1-theta)*(∫ y, scalarPotential p a k gamma (meanOverlap (kappa y) a) ∂nu)+
      theta*(∫ s, ∫ y, scalarPotential (Measure.dirac s) a k gamma (meanOverlap (kappa y) a) ∂nu ∂p)-
        (∫ y, scalarPotential p a k gamma (meanOverlap (kappa y) a) ∂nu) ∧
    (1-theta)*(∫ y, scalarPotential p a k gamma (meanOverlap (kappa y) a) ∂nu)+
      theta*(∫ s, ∫ y, scalarPotential (Measure.dirac s) a k gamma (meanOverlap (kappa y) a) ∂nu ∂p)-
        (∫ y, scalarPotential p a k gamma (meanOverlap (kappa y) a) ∂nu) ≤
          theta*Real.log (Fintype.card S) := by
  let f := fun y ↦ scalarPotential p a k gamma (meanOverlap (kappa y) a)
  let g := fun s y ↦ scalarPotential (Measure.dirac s) a k gamma (meanOverlap (kappa y) a)
  have hf : Integrable f nu := integrable_scalarPotential_meanOverlap kappa nu p a k gamma hN hb
  have hg (s : S) : Integrable (g s) nu :=
    integrable_scalarPotential_meanOverlap kappa nu (Measure.dirac s) a k gamma hN hb
  have hmean : Integrable (fun y ↦ ∫ s, g s y ∂p) nu := by
    simp_rw [integral_fintype (μ := p) Integrable.of_finite,smul_eq_mul]
    exact integrable_finsetSum _ (fun s _ ↦ (hg s).const_mul _)
  have hswap : (∫ y, ∫ s, g s y ∂p ∂nu) = ∫ s, ∫ y, g s y ∂nu ∂p := by
    simp_rw [integral_fintype (μ := p) Integrable.of_finite,smul_eq_mul]
    rw [integral_finsetSum _ (fun s _ ↦ (hg s).const_mul _)]
    simp_rw [integral_const_mul]
  have hI := ((hf.const_mul (1-theta)).add (hmean.const_mul theta)).sub hf
  have heq : (∫ y, (1-theta)*f y+theta*(∫ s, g s y ∂p)-f y ∂nu) =
      (1-theta)*(∫ y, f y ∂nu)+theta*(∫ s, ∫ y, g s y ∂nu ∂p)-(∫ y, f y ∂nu) := by
    have H := integral_sub ((hf.const_mul (1-theta)).add (hmean.const_mul theta)) hf
    simp only [Pi.add_apply] at H
    rw [integral_add (hf.const_mul _) (hmean.const_mul _),integral_const_mul,integral_const_mul,hswap] at H
    exact H
  have hlo : 0 ≤ ∫ y, (1-theta)*f y+theta*(∫ s, g s y ∂p)-f y ∂nu :=
    integral_nonneg (fun y ↦ (lastReveal_scalarPotential_cost_bounds p a k gamma (meanOverlap (kappa y) a) ht0 ht1).1)
  have hhi := integral_mono hI (integrable_const (theta*Real.log (Fintype.card S)))
    (fun y ↦ (lastReveal_scalarPotential_cost_bounds p a k gamma (meanOverlap (kappa y) a) ht0 ht1).2)
  simp only [Pi.add_apply,Pi.sub_apply] at hhi
  rw [heq] at hlo hhi
  rw [integral_const,probReal_univ,one_smul] at hhi
  exact ⟨hlo,hhi⟩

theorem integral_configurationSplit (p : Measure S) [IsProbabilityMeasure p] (N : ℕ)
    (f : (Fin N → S) × S → ℝ) :
    (∫ X, f (oldConfiguration X,X (Fin.last N)) ∂configurationPrior p (N+1)) =
      ∫ x, ∫ s, f (x,s) ∂p ∂configurationPrior p N := by
  have H := integral_map (μ := configurationPrior p (N+1)) (configurationSplit N).measurable.aemeasurable
    (show AEStronglyMeasurable f ((configurationPrior p (N+1)).map (configurationSplit N)) from
      (measurable_of_finite f).aestronglyMeasurable)
  rw [(configurationSplit_measurePreserving p N).map_eq,integral_prod _ Integrable.of_finite] at H
  simp only [configurationSplit_apply] at H
  exact H.symm

/-- Literal full-mask last-bit elimination for the actual background posterior.
The background kernel and scalar center depend only on the old mask/data, and
the true planted product law supplies the fresh-symbol average. -/
theorem fullmask_scalarPotential_lastReveal_le
    (p : Measure S) [IsProbabilityMeasure p] {N : ℕ} (hN : 0 < N)
    (a : S → ℝ) (k : ℕ) (gamma : ℝ) {K : ℝ} (hb : ∀ s, |a s| ≤ K)
    {theta : ℝ} (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    average Finset.univ (fun A : Finset (Fin (N+1)) ↦ ∫ X,
      let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
      let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
      ∫ y, scalarPotential pLast a k gamma
        (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
          ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p (N+1)) theta ≤
      average Finset.univ (fun A : Finset (Fin N) ↦ ∫ x,
        let qOld := posterior (configurationPrior p N) A x
        ∫ y, scalarPotential p a k gamma
          (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
            ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N) theta+
        theta*Real.log (Fintype.card S) := by
  let F := fun (A : Finset (Fin N)) (x : Fin N → S) (r : Measure S) ↦
    let qOld := posterior (configurationPrior p N) A x
    ∫ y, scalarPotential r a k gamma
      (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma)
  let U := fun A ↦ ∫ x, F A x p ∂configurationPrior p N
  let V := fun A ↦ ∫ x, ∫ s, F A x (Measure.dirac s) ∂p ∂configurationPrior p N
  have hmask (A : Finset (Fin N)) : (1-theta)*U A+theta*V A-U A ≤ theta*Real.log (Fintype.card S) := by
    have hx (x : Fin N → S) : (1-theta)*F A x p+theta*(∫ s, F A x (Measure.dirac s) ∂p)-F A x p ≤
        theta*Real.log (Fintype.card S) := by
      let qOld := posterior (configurationPrior p N) A x
      have : IsMarkovKernel (posteriorKernel qOld (backgroundSignal a N k gamma)) :=
        posteriorKernel_isMarkov qOld _ (measurable_of_finite _)
      have : IsProbabilityMeasure (mixtureLaw qOld (backgroundSignal a N k gamma)) :=
        mixtureLaw_probability qOld _ (measurable_of_finite _)
      exact (kernel_lastReveal_scalarPotential_cost_bounds
        (posteriorKernel qOld (backgroundSignal a N k gamma)) (mixtureLaw qOld (backgroundSignal a N k gamma))
        p a k gamma hN hb ht0 ht1).2
    have H := integral_mono (μ := configurationPrior p N) Integrable.of_finite
      (integrable_const (theta*Real.log (Fintype.card S))) hx
    rw [integral_sub Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,integral_const_mul,integral_const_mul,
      integral_const,probReal_univ,one_smul] at H
    exact H
  have hfull (A : Finset (Fin (N+1))) :
      (∫ X, F (oldPart A) (oldConfiguration X)
        (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) ∂configurationPrior p (N+1)) =
      if Fin.last N ∈ A then V (oldPart A) else U (oldPart A) := by
    by_cases hA : Fin.last N ∈ A
    · simp only [hA,ite_true]
      exact integral_configurationSplit p N (fun z ↦ F (oldPart A) z.1 (Measure.dirac z.2))
    · simp only [hA,ite_false]
      exact integral_oldConfiguration p N (fun x ↦ F (oldPart A) x p)
  have heq : average Finset.univ
      (fun A : Finset (Fin (N+1)) ↦ if Fin.last N ∈ A then V (oldPart A) else U (oldPart A)) theta =
      (1-theta)*average Finset.univ U theta+theta*average Finset.univ V theta := by
    have H := average_oldPart_last N (fun A b ↦ if b then V A else U A) theta
    convert H using 1
    · congr 1
      funext A
      by_cases hA : Fin.last N ∈ A <;> simp [hA]
    · simp
  have H := average_mono Finset.univ
    (fun A ↦ (1-theta)*U A+theta*V A-U A) (fun _ ↦ theta*Real.log (Fintype.card S)) ht0 ht1 hmask
  rw [BayesianPinningVarianceProofs.average_sub,BayesianPinningVarianceProofs.average_add,
    BayesianPinningVarianceProofs.average_const_mul,BayesianPinningVarianceProofs.average_const_mul,
    BayesianPinningVarianceProofs.average_const] at H
  change average Finset.univ (fun A : Finset (Fin (N+1)) ↦ ∫ X,
    F (oldPart A) (oldConfiguration X)
      (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) ∂configurationPrior p (N+1)) theta ≤
        average Finset.univ U theta+theta*Real.log (Fintype.card S)
  simp_rw [hfull]
  rw [heq]
  linarith

end
end TensorPCA.FinitePriorCavityLastRevealProofs
