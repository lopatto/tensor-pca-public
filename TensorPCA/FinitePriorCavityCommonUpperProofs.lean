-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.FinitePriorCavityLastRevealProofs
public import TensorPCA.GaussianRevealVarianceAverageProofs
public import TensorPCA.FinitePriorCavityUpperProofs

/-! The common-rate perturbed cavity increment is controlled by the
scalar cavity potential and the proved pinning variance. The old and new
dimensions use the same reveal rate here; varying-rate comparison is separate. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityCommonUpperProofs
open MeasureTheory ProbabilityTheory Set GaussianPriorTransferProofs GaussianPosteriorProofs
open FinitePriorChannelProofs FinitePriorCavityFieldProofs FinitePriorCavityPartitionProofs
open FinitePriorCavityNormalizationProofs FinitePriorCavityConditionalIncrementProofs
open FinitePriorCavityConditionalUpperProofs FinitePriorCavityRevealedIncrementProofs
open FinitePriorCavityAveragingProofs FinitePriorCavityLastRevealProofs FinitePriorCavityRevealProofs
open FinitePriorCavityPinningProofs GaussianRevealVarianceAverageProofs FinitePriorCavityUpperProofs
open FinitePriorScalarDomainProofs FiniteRevealProofs FiniteRevealAveragingProofs
open TensorCavitySubsetProofs PosteriorPairProofs RevealPolynomialProofs
open BayesianPinningProofs BayesianPinningVarianceProofs
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] FiniteRevealProofs.posterior_probability

variable {S : Type*} [MeasurableSpace S] [Fintype S] [MeasurableSingletonClass S]

theorem exists_mask_increment_upper_constant (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ} (hgamma : 0 < gamma)
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ A : Finset (Fin (N+1)),
      conditionalCavityIncrement p a N k gamma A ≤
        (∫ X,
          let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
          let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
          ∫ y, scalarPotential pLast a k gamma
            (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
              ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p (N+1))+
        C*(1/(N : ℝ)+(∫ x,
          let qOld := posterior (configurationPrior p N) (oldPart A) x
          ∫ y, Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
            ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N)) := by
  obtain ⟨C,hC,hbound⟩ := exists_conditional_increment_upper_constant a hk hgamma hK hb
  refine ⟨C,hC,?_⟩
  intro N hN A
  let fPlus := fun X : Fin (N+1) → S ↦
    mixtureFreeEnergy (posterior (configurationPrior p (N+1)) A X) (tensorSignal a (N+1) k gamma)
  let fOld := fun x : Fin N → S ↦
    mixtureFreeEnergy (posterior (configurationPrior p N) (oldPart A) x) (tensorSignal a N k gamma)
  let P := fun X : Fin (N+1) → S ↦
    let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
    let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
    ∫ y, scalarPotential pLast a k gamma
      (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma)
  let V := fun x : Fin N → S ↦
    let qOld := posterior (configurationPrior p N) (oldPart A) x
    ∫ y, Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
      ∂mixtureLaw qOld (backgroundSignal a N k gamma)
  have hpt : ∀ᵐ X ∂configurationPrior p (N+1),
      fPlus X-fOld (oldConfiguration X) ≤ P X+C*(1/(N : ℝ)+V (oldConfiguration X)) := by
    filter_upwards [configurationSplit_reveal_posterior_map_ae p A] with X hSplit
    have : IsProbabilityMeasure (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) := by
      split_ifs <;> infer_instance
    exact hbound N hN (posterior (configurationPrior p (N+1)) A X)
      (posterior (configurationPrior p N) (oldPart A) (oldConfiguration X))
      (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) hSplit
  have H := integral_mono_ae (μ := configurationPrior p (N+1)) Integrable.of_finite Integrable.of_finite hpt
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    integral_oldConfiguration p N fOld,
    integral_add Integrable.of_finite Integrable.of_finite,integral_const_mul,
    integral_add (integrable_const (1/(N : ℝ))) Integrable.of_finite,
    integral_const,probReal_univ,one_smul,integral_oldConfiguration p N V] at H
  have hEq : (∫ X, fPlus X ∂configurationPrior p (N+1))-(∫ x, fOld x ∂configurationPrior p N) =
      conditionalCavityIncrement p a N k gamma A := revealed_cavity_increment_integral p hN (by omega) hgamma a A
  rw [hEq] at H
  exact H

theorem exists_bernoulli_increment_upper_constant (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ} (hgamma : 0 < gamma)
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ theta : ℝ, 0 ≤ theta → theta ≤ 1 →
      average Finset.univ (conditionalCavityIncrement p a N k gamma) theta ≤
        average Finset.univ (fun A : Finset (Fin N) ↦ ∫ x,
          let qOld := posterior (configurationPrior p N) A x
          ∫ y, scalarPotential p a k gamma
            (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
              ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N) theta+
        theta*Real.log (Fintype.card S)+C*(1/(N : ℝ)+
          average Finset.univ (fun A : Finset (Fin N) ↦ ∫ x,
            let qOld := posterior (configurationPrior p N) A x
            ∫ y, Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
              ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N) theta) := by
  obtain ⟨C,hC,hbound⟩ := exists_mask_increment_upper_constant p a hk hgamma hK hb
  refine ⟨C,hC,?_⟩
  intro N hN theta ht0 ht1
  let P := fun A : Finset (Fin (N+1)) ↦ ∫ X,
    let qOld := posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)
    let pLast := if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p
    ∫ y, scalarPotential pLast a k gamma
      (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p (N+1)
  let Pold := fun A : Finset (Fin N) ↦ ∫ x,
    let qOld := posterior (configurationPrior p N) A x
    ∫ y, scalarPotential p a k gamma
      (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N
  let V := fun A : Finset (Fin N) ↦ ∫ x,
    let qOld := posterior (configurationPrior p N) A x
    ∫ y, Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
      ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N
  have H := average_mono Finset.univ (conditionalCavityIncrement p a N k gamma)
    (fun A ↦ P A+C*(1/(N : ℝ)+V (oldPart A))) ht0 ht1 (hbound N hN)
  rw [BayesianPinningVarianceProofs.average_add,BayesianPinningVarianceProofs.average_const_mul,
    BayesianPinningVarianceProofs.average_add,BayesianPinningVarianceProofs.average_const,average_oldPart] at H
  have hP : average Finset.univ P theta ≤ average Finset.univ Pold theta+theta*Real.log (Fintype.card S) :=
    fullmask_scalarPotential_lastReveal_le p hN a k gamma hb ht0 ht1
  exact H.trans (add_le_add hP (le_refl _))

private theorem integral_affine_two {Y : Type*} [MeasurableSpace Y]
    (mu : Measure Y) [IsProbabilityMeasure mu] (f g : Y → ℝ)
    (hf : Integrable f mu) (hg : Integrable g mu) (b c d : ℝ) :
    (∫ x, f x+b+c*(d+g x) ∂mu) =
      (∫ x, f x ∂mu)+b+c*(d+∫ x, g x ∂mu) := by
  have hfb : Integrable (fun x ↦ f x+b) mu := hf.add (integrable_const b)
  have hdg : Integrable (fun x ↦ d+g x) mu := (integrable_const d).add hg
  have hcg : Integrable (fun x ↦ c*(d+g x)) mu := hdg.const_mul c
  rw [integral_add hfb hcg,integral_add hf (integrable_const b),integral_const_mul,
    integral_add (integrable_const d) hg,integral_const,integral_const,probReal_univ,one_smul]
  simp only [one_smul]

/-- The actual common-rate cavity increment has a uniform finite constant.
The sole remaining scalar average is the old-mask actual background average. -/
theorem exists_commonRate_increment_upper_constant (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ} (hgamma : 0 < gamma)
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      revealedFreeEnergyAtRate p a (N+1) k gamma delta-revealedFreeEnergyAtRate p a N k gamma delta ≤
        uniformAverage Finset.univ delta (fun A : Finset (Fin N) ↦ ∫ x,
          let qOld := posterior (configurationPrior p N) A x
          ∫ y, scalarPotential p a k gamma
            (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
              ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N)+
        delta*Real.log (Fintype.card S)+
        C*(1/(N : ℝ)+Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))) := by
  obtain ⟨C,hC,hbound⟩ := exists_bernoulli_increment_upper_constant p a hk hgamma hK hb
  refine ⟨C,hC,?_⟩
  intro N hN delta hd hd1
  let P := fun A : Finset (Fin N) ↦ ∫ x,
    let qOld := posterior (configurationPrior p N) A x
    ∫ y, scalarPotential p a k gamma
      (meanOverlap (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
        ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N
  let V := fun A : Finset (Fin N) ↦ ∫ x,
    let qOld := posterior (configurationPrior p N) A x
    ∫ y, Real.sqrt (replicaVariance (posteriorKernel qOld (backgroundSignal a N k gamma) y) a)
      ∂mixtureLaw qOld (backgroundSignal a N k gamma) ∂configurationPrior p N
  let mu := ProbabilityTheory.cond volume (Icc (0 : ℝ) delta)
  have : IsProbabilityMeasure mu := uniformInterval_probability hd
  have hLeft : Integrable (fun theta ↦ average Finset.univ (conditionalCavityIncrement p a N k gamma) theta) mu :=
    (memLp_uniformInterval (average_continuous _ _) hd 1).integrable le_rfl
  have hP : Integrable (fun theta ↦ average Finset.univ P theta) mu :=
    (memLp_uniformInterval (average_continuous _ _) hd 1).integrable le_rfl
  have hV : Integrable (fun theta ↦ average Finset.univ V theta) mu :=
    (memLp_uniformInterval (average_continuous _ _) hd 1).integrable le_rfl
  have hRight : Integrable (fun theta ↦ average Finset.univ P theta+delta*Real.log (Fintype.card S)+
      C*(1/(N : ℝ)+average Finset.univ V theta)) mu :=
    (hP.add (integrable_const _)).add (((integrable_const _).add hV).const_mul C)
  have htheta : ∀ᵐ theta ∂mu,
      average Finset.univ (conditionalCavityIncrement p a N k gamma) theta ≤
        average Finset.univ P theta+delta*Real.log (Fintype.card S)+
          C*(1/(N : ℝ)+average Finset.univ V theta) := by
    exact ae_cond_of_forall_mem measurableSet_Icc (fun theta ht ↦ by
      have H := hbound N hN theta ht.1 (ht.2.trans hd1)
      have hlog := mul_le_mul_of_nonneg_right ht.2 (Real.log_natCast_nonneg (Fintype.card S))
      change average Finset.univ (conditionalCavityIncrement p a N k gamma) theta ≤
        average Finset.univ P theta+delta*Real.log (Fintype.card S)+C*(1/(N : ℝ)+average Finset.univ V theta)
      linarith)
  have H := integral_mono_ae hLeft hRight htheta
  rw [integral_affine_two mu _ _ hP hV] at H
  change uniformAverage Finset.univ delta (conditionalCavityIncrement p a N k gamma) ≤
    uniformAverage Finset.univ delta P+delta*Real.log (Fintype.card S)+C*(1/(N : ℝ)+uniformAverage Finset.univ delta V) at H
  have hVar : uniformAverage Finset.univ delta V ≤
      Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta))) :=
    actual_gaussian_pinning_sqrt_variance_bound (configurationPrior p N) (backgroundSignal a N k gamma)
      (measurable_of_finite _) a hN hK hb hd hd1
  rw [uniform_cavity_increment_identity p hN (by omega) hgamma a hd]
  exact H.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1/(N : ℝ))) hVar) hC))

/-- The common-rate RS upper bound. No physical increment,
random-center bound by rho, or value-convergence premise remains. -/
theorem exists_commonRate_increment_compact_upper_constant (p : Measure S) [IsProbabilityMeasure p]
    (a : S → ℝ) {k : ℕ} (hk : 2 ≤ k) {gamma K : ℝ} (hgamma : 0 < gamma)
    (hK : 0 ≤ K) (hb : ∀ s, |a s| ≤ K) (hrho : scalarSecondMoment p a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N → ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      revealedFreeEnergyAtRate p a (N+1) k gamma delta-revealedFreeEnergyAtRate p a N k gamma delta ≤
        sSup (scalarPotential p a k gamma '' Icc (0 : ℝ) 1)+delta*Real.log (Fintype.card S)+
          C*(1/(N : ℝ)+Real.sqrt (4*K^4*Real.sqrt (Real.log (Fintype.card S)/((N : ℝ)*delta)))) := by
  obtain ⟨C,hC,hbound⟩ := exists_commonRate_increment_upper_constant p a hk hgamma hK hb
  refine ⟨C,hC,?_⟩
  intro N hN delta hd hd1
  have H := hbound N hN delta hd hd1
  have hP := uniform_reveal_scalarPotential_le_compact p a (backgroundSignal a N k gamma)
    (measurable_of_finite _) hN hk hgamma.le hrho hd hd1
  linarith

end
end TensorPCA.FinitePriorCavityCommonUpperProofs
