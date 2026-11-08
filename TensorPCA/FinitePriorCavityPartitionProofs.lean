-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityFieldProofs

/-! Finite product-prior cavity partition factorization. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityPartitionProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open GaussianPriorTransferProofs GaussianPosteriorProofs GaussianSideChannelProofs TensorOrbitCountProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S]

def configurationSplit (N : ℕ) : (Fin (N+1) → S) ≃ᵐ ((Fin N → S) × S) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) ↦ S) (Fin.last N)).trans MeasurableEquiv.prodComm

theorem configurationSplit_apply (N : ℕ) (x : Fin (N+1) → S) :
    configurationSplit N x = (oldConfiguration x,x (Fin.last N)) := by
  simp [configurationSplit,MeasurableEquiv.piFinSuccAbove_apply,Fin.insertNthEquiv,oldConfiguration,
    Fin.succAbove_last]
  rfl

theorem configurationSplit_measurePreserving (p : Measure S) [IsProbabilityMeasure p] (N : ℕ) :
    MeasurePreserving (configurationSplit N) (configurationPrior p (N+1)) ((configurationPrior p N).prod p) := by
  have H := (Measure.measurePreserving_swap : MeasurePreserving Prod.swap
    (p.prod (configurationPrior p N)) ((configurationPrior p N).prod p)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) ↦ p) (Fin.last N))
  exact H

theorem oldConfiguration_split_symm (N : ℕ) (z : (Fin N → S) × S) :
    oldConfiguration ((configurationSplit N).symm z) = z.1 := by
  have H := congrArg Prod.fst ((configurationSplit N).apply_symm_apply z)
  simpa only [configurationSplit_apply] using H

theorem lastConfiguration_split_symm (N : ℕ) (z : (Fin N → S) × S) :
    (configurationSplit N).symm z (Fin.last N) = z.2 := by
  have H := congrArg Prod.snd ((configurationSplit N).apply_symm_apply z)
  simpa only [configurationSplit_apply] using H

def backgroundPartition (p : Measure S) (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : ℝ :=
  mixtureLikelihood (configurationPrior p N) (backgroundSignal a N k gamma) (backgroundSignal a N k gamma X+w)

def backgroundPosterior (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : Measure (Fin N → S) :=
  posteriorKernel (configurationPrior p N) (backgroundSignal a N k gamma) (backgroundSignal a N k gamma X+w)

def cavityFactor (p : Measure S) (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (Xlast : S) (w : EuclideanSpace ℝ (KSubset N (k-1))) (x : Fin N → S) : ℝ :=
  ∫ sigma, Real.exp (a sigma*cavityZ a N k gamma X x Xlast w+(a sigma)^2*cavityS a N k gamma x) ∂p

variable [Fintype S] [MeasurableSingletonClass S]

theorem backgroundPartition_pos (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : 0 < backgroundPartition p a N k gamma X w :=
  mixtureLikelihood_pos (configurationPrior p N) (backgroundSignal a N k gamma) (measurable_of_finite _) _

theorem backgroundPosterior_probability (p : Measure S) [IsProbabilityMeasure p] (a : S → ℝ) (N k : ℕ) (gamma : ℝ)
    (X : Fin N → S) (w : EuclideanSpace ℝ (KSubset N k)) : IsProbabilityMeasure (backgroundPosterior p a N k gamma X w) := by
  letI := posteriorKernel_isMarkov (configurationPrior p N) (backgroundSignal a N k gamma) (measurable_of_finite _)
  unfold backgroundPosterior
  infer_instance

/-- Exact product-prior partition identity for the N+1-normalized background
and the true fresh z and s fields. -/
theorem mixtureLikelihood_cavity_integral (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (X : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    mixtureLikelihood (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
      (tensorSignal a (N+1) k gamma X+w) =
      ∫ x, Real.exp (backgroundHamiltonian a N k gamma (oldConfiguration X) x (disorderSplit hk w).1)*
        cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x
          ∂configurationPrior p N := by
  let f : (Fin (N+1) → S) → ℝ := fun x ↦ mixtureWeight (tensorSignal a (N+1) k gamma x)
    (tensorSignal a (N+1) k gamma X+w)
  calc
    _ = ∫ z : (Fin N → S) × S, f ((configurationSplit N).symm z) ∂(configurationPrior p N).prod p :=
      ((MeasurePreserving.symm (configurationSplit N) (configurationSplit_measurePreserving p N)).integral_comp
        (configurationSplit N).symm.measurableEmbedding f).symm
    _ = _ := by
      rw [integral_prod _ (Integrable.of_finite : Integrable (fun z : (Fin N → S) × S ↦ f ((configurationSplit N).symm z))
        ((configurationPrior p N).prod p))]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change (∫ sigma, f ((configurationSplit N).symm (x,sigma)) ∂p) =
        Real.exp (backgroundHamiltonian a N k gamma (oldConfiguration X) x (disorderSplit hk w).1)*
          cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x
      rw [cavityFactor,← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro sigma
      change mixtureWeight (tensorSignal a (N+1) k gamma ((configurationSplit N).symm (x,sigma)))
        (tensorSignal a (N+1) k gamma X+w) = _
      rw [mixtureWeight_cavity hk,oldConfiguration_split_symm,lastConfiguration_split_symm]

theorem mixtureLikelihood_cavity_factor (p : Measure S) [IsProbabilityMeasure p]
    {N k : ℕ} (hk : 0 < k) (a : S → ℝ) (gamma : ℝ)
    (X : Fin (N+1) → S) (w : EuclideanSpace ℝ (KSubset (N+1) k)) :
    mixtureLikelihood (configurationPrior p (N+1)) (tensorSignal a (N+1) k gamma)
      (tensorSignal a (N+1) k gamma X+w) =
      backgroundPartition p a N k gamma (oldConfiguration X) (disorderSplit hk w).1*
        ∫ x, cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x
          ∂backgroundPosterior p a N k gamma (oldConfiguration X) (disorderSplit hk w).1 := by
  rw [mixtureLikelihood_cavity_integral p hk]
  change _ = backgroundPartition p a N k gamma (oldConfiguration X) (disorderSplit hk w).1*
    posteriorMean (configurationPrior p N) (backgroundSignal a N k gamma)
      (cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2)
      (backgroundSignal a N k gamma (oldConfiguration X)+(disorderSplit hk w).1)
  rw [posteriorMean_eq_weightedIntegral (configurationPrior p N) (backgroundSignal a N k gamma) (measurable_of_finite _)]
  change _ = backgroundPartition p a N k gamma (oldConfiguration X) (disorderSplit hk w).1*
    ((backgroundPartition p a N k gamma (oldConfiguration X) (disorderSplit hk w).1)⁻¹*
      ∫ x, mixtureWeight (backgroundSignal a N k gamma x)
        (backgroundSignal a N k gamma (oldConfiguration X)+(disorderSplit hk w).1)*
        cavityFactor p a N k gamma (oldConfiguration X) (X (Fin.last N)) (disorderSplit hk w).2 x ∂configurationPrior p N)
  rw [← mul_assoc,mul_inv_cancel₀ (backgroundPartition_pos p a N k gamma (oldConfiguration X) (disorderSplit hk w).1).ne',one_mul]
  rfl

end
end TensorPCA.FinitePriorCavityPartitionProofs
