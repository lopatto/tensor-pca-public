-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Prod

/-! The product-replica inner moment of a bounded measurable signal.
The probability law is arbitrary; no coordinate independence is required. -/
@[expose] public section
namespace TensorPCA.GaussianReplicaMomentProofs
open MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Omega E : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem signal_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) {C : ℝ} (hAB : ∀ᵐ x ∂q, ‖A x‖ ≤ C) :
    Integrable A q :=
  (integrable_const C).mono' hA.aestronglyMeasurable hAB

theorem replicaInner_integrable (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) {C : ℝ} (hAB : ∀ᵐ x ∂q, ‖A x‖ ≤ C) :
    Integrable (fun z : Omega × Omega ↦ ⟪A z.1,A z.2⟫) (q.prod q) := by
  have hi := signal_integrable q A hA hAB
  exact hi.op_fst_snd continuous_inner ⟨1,fun x y ↦ by
    simpa only [one_mul] using norm_inner_le_norm x y⟩ hi

/-- A genuine product-replica identity, with Bochner integrability proved
from the original almost-everywhere signal bound. -/
theorem norm_integral_sq_eq_replicaInner (q : Measure Omega) [IsProbabilityMeasure q]
    (A : Omega → E) (hA : Measurable A) {C : ℝ} (hAB : ∀ᵐ x ∂q, ‖A x‖ ≤ C) :
    ‖∫ x, A x ∂q‖^2 = ∫ z : Omega × Omega, ⟪A z.1,A z.2⟫ ∂q.prod q := by
  have hi := signal_integrable q A hA hAB
  have H := integral_prod_bilin (innerSL ℝ (E := E)) hi hi
  change (∫ z : Omega × Omega, ⟪A z.1,A z.2⟫ ∂q.prod q) = ⟪∫ x, A x ∂q,∫ x, A x ∂q⟫ at H
  rw [real_inner_self_eq_norm_sq] at H
  exact H.symm

end
end TensorPCA.GaussianReplicaMomentProofs
