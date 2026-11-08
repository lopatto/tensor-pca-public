-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorCavityLawProofs
public import TensorPCA.FiniteProductRevealProofs

/-! Exact common reveal mask and prior decomposition in the finite cavity step. -/
@[expose] public section
namespace TensorPCA.FinitePriorCavityRevealProofs
open MeasureTheory ProbabilityTheory FinitePriorChannelProofs FinitePriorCavityFieldProofs
open FinitePriorCavityPartitionProofs FinitePriorCavityLawProofs FiniteProductRevealProofs TensorCavitySubsetProofs
open scoped RealInnerProductSpace BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S]

def lastOverride {N : ℕ} (A : Finset (Fin (N+1))) (X : Fin (N+1) → S) (sigma : S) : S :=
  if Fin.last N ∈ A then X (Fin.last N) else sigma

theorem oldConfiguration_override {N : ℕ} (A : Finset (Fin (N+1))) (X x : Fin (N+1) → S) :
    oldConfiguration (override A X x) = override (oldPart A) (oldConfiguration X) (oldConfiguration x) := by
  funext i
  simp [oldConfiguration,override,oldPart]

theorem configurationSplit_override {N : ℕ} (A : Finset (Fin (N+1))) (X x : Fin (N+1) → S) :
    configurationSplit N (override A X x) =
      (override (oldPart A) (oldConfiguration X) (oldConfiguration x),lastOverride A X (x (Fin.last N))) := by
  rw [configurationSplit_apply,oldConfiguration_override]
  rfl

variable [Fintype S] [MeasurableSingletonClass S]

theorem lastOverride_prior_map (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin (N+1))) (X : Fin (N+1) → S) :
    p.map (lastOverride A X) = if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p := by
  by_cases hA : Fin.last N ∈ A
  · have heq : lastOverride A X = fun _ : S ↦ X (Fin.last N) := by funext sigma; simp [lastOverride,hA]
    rw [if_pos hA,heq]
    simp
  · have heq : lastOverride A X = id := by funext sigma; simp [lastOverride,hA]
    rw [if_neg hA,heq,Measure.map_id]

/-- The same full reveal mask gives precisely its old-coordinate reveal prior
and the actual revealed/unrevealed last-coordinate prior as independent factors. -/
theorem configurationSplit_override_prior_map (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin (N+1))) (X : Fin (N+1) → S) :
    ((configurationPrior p (N+1)).map (override A X)).map (configurationSplit N) =
      ((configurationPrior p N).map (override (oldPart A) (oldConfiguration X))).prod
        (p.map (lastOverride A X)) := by
  have hcomp : (configurationSplit N) ∘ override A X =
      Prod.map (override (oldPart A) (oldConfiguration X)) (lastOverride A X) ∘ configurationSplit N := by
    funext x
    rw [Function.comp_apply,configurationSplit_override,Function.comp_apply,configurationSplit_apply]
    rfl
  rw [Measure.map_map (configurationSplit N).measurable (measurable_of_finite _),hcomp,
    ← Measure.map_map ((measurable_of_finite _).prodMap (measurable_of_finite _)) (configurationSplit N).measurable,
    (configurationSplit_measurePreserving p N).map_eq,← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _)]

/-- Actual finite reveal posteriors, with the existing null-fiber fallback, have
the common-mask old/last product law for almost every true planted sample. -/
theorem configurationSplit_reveal_posterior_map_ae (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin (N+1))) : ∀ᵐ X ∂configurationPrior p (N+1),
      (FiniteRevealProofs.posterior (configurationPrior p (N+1)) A X).map (configurationSplit N) =
        (FiniteRevealProofs.posterior (configurationPrior p N) (oldPart A) (oldConfiguration X)).prod
          (if Fin.last N ∈ A then Measure.dirac (X (Fin.last N)) else p) := by
  have hMP : MeasurePreserving (oldConfiguration (S := S) (N := N)) (configurationPrior p (N+1)) (configurationPrior p N) :=
    ⟨measurable_of_finite _,oldConfiguration_prior_map p N⟩
  have hOld := hMP.quasiMeasurePreserving.ae (map_override_eq_posterior_ae p (oldPart A))
  filter_upwards [map_override_eq_posterior_ae p A,hOld] with X hFull hOld
  rw [← hFull,configurationSplit_override_prior_map p A X,hOld,lastOverride_prior_map p A X]

end
end TensorPCA.FinitePriorCavityRevealProofs
