-- SPDX-License-Identifier: Apache-2.0
/- Narrow attributed first generic block from immutable source:
https://github.com/pmaronow/slowequilibration-palomar/blob/a28aaa336343c4caf43791ababd8ed0ee5c7b58e/SlowEquilibration/GaussianIndependentBankPositivity.lean
Only realizedPairMass and its measurability/norm bounds are retained.
The unrelated radial positivity theorem and its imports are omitted. -/
module
public import TensorPCA.NonRSUpperProofs.GaussianBankAveraging
public import TensorPCA.NonRSUpperProofs.GaussianSpinKernels
public import Mathlib.Probability.Kernel.Composition.Prod
@[expose] public section
noncomputable section
namespace TensorPCA.GaussianSpinInterpolation
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology
variable {V X H : Type*} [MeasurableSpace V] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
/-- The literal independently sampled Gibbs-pair mass at a jointly
parameterized realized coefficient vector. -/
def realizedPairMass (μ : Measure V) (T : V → H →L[ℝ] ℝ) (Φ : X → H)
    (A : Set (V × V)) (p : X) : ℝ :=
  ((gibbsMeasure μ T (Φ p)).prod (gibbsMeasure μ T (Φ p))).real A

theorem realizedPairMass_measurable (μ : Measure V) [IsProbabilityMeasure μ]
    (T : V → H →L[ℝ] ℝ) (hT : Measurable T) {B : ℝ} (hB : 0≤B)
    (hb : ∀ᵐ z ∂μ,‖T z‖≤B) (Φ : X → H) (hΦ : Measurable Φ)
    (A : Set (V × V)) (hA : MeasurableSet A) : Measurable (realizedPairMass μ T Φ A) := by
  let _ := gibbsKernel_markov μ T hT hB hb
  let G : Kernel X V := (gibbsKernel μ T).comap Φ hΦ
  have hm : Measurable (fun p => ((G ×ₖ G) p).real A) := by
    simpa only [Measure.real] using ((G ×ₖ G).measurable_coe hA).ennreal_toReal
  have heq : (fun p => ((G ×ₖ G) p).real A)=realizedPairMass μ T Φ A := by
    funext p
    rw [Kernel.prod_apply]
    change ((gibbsKernel μ T (Φ p)).prod (gibbsKernel μ T (Φ p))).real A=_
    rw [gibbsKernel_apply μ T hT hB hb]
    rfl
  rwa [heq] at hm

omit [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] in
theorem realizedPairMass_norm_le_one (μ : Measure V) [IsProbabilityMeasure μ]
    (T : V → H →L[ℝ] ℝ) (hT : Measurable T) {B : ℝ}
    (hb : ∀ᵐ z ∂μ,‖T z‖≤B) (Φ : X → H) (A : Set (V × V)) (p : X) :
    ‖realizedPairMass μ T Φ A p‖≤1 := by
  let _ := gibbsMeasure_probability μ T hT hb (Φ p)
  unfold realizedPairMass
  rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

end TensorPCA.GaussianSpinInterpolation
