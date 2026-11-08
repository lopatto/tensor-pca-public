-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.Geometry
public import TensorPCA.CheckedReduction

/-! Finite overlap measurability, boundedness and expectation transport for
arbitrary independently randomized estimators on the reviewed common space. -/

@[expose] public section
namespace TensorPCA.EstimatorTransportProofs
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

theorem overlapIntegralTransport : CheckedReduction.OverlapIntegralTransport.{u,v} := by
  intro k hk lam hlam Ω _ μ _ E A _ ν _ R
  let f (n : ℕ) (z : (Model.Vector (n+1) × Model.Tensor (n+1) k) × A n) : ℝ :=
    |inner ℝ (R.estimator n (Model.observation lam z.1) z.2) z.1.1|
  have hmp (n : ℕ) : MeasurePreserving
      (fun ω ↦ (E.sample n ω, R.auxiliary n ω)) μ
      ((Model.experimentLaw (n+1) k).prod (ν n)) :=
    ⟨(E.measurable n).prodMk (R.measurable n), R.independentLaw n⟩
  have hf (n : ℕ) : Measurable (f n) := by
    have hobs := ((Model.measurable_observation (n+1) k lam).comp measurable_fst).prodMk
      (measurable_snd : Measurable (fun z :
        (Model.Vector (n+1) × Model.Tensor (n+1) k) × A n ↦ z.2))
    have hest := (R.unit n).1.comp hobs
    exact continuous_abs.measurable.comp ((continuous_inner (𝕜 := ℝ)).measurable.comp
      (hest.prodMk (measurable_fst.comp measurable_fst)))
  have hbound (n : ℕ) : ∀ᵐ z ∂(Model.experimentLaw (n+1) k).prod (ν n), ‖f n z‖ ≤ 1 := by
    have hsignal : ∀ᵐ z ∂(Model.experimentLaw (n+1) k).prod (ν n), ‖z.1.1‖ = 1 :=
      Measure.quasiMeasurePreserving_fst.ae
        (Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae (Nat.succ_pos n)))
    filter_upwards [hsignal] with z hz
    have H := abs_real_inner_le_norm
      (R.estimator n (Model.observation lam z.1) z.2) z.1.1
    have he := (R.unit n).2 (Model.observation lam z.1) z.2
    simpa only [f, Real.norm_eq_abs, abs_abs, he, hz, one_mul] using H
  refine ⟨?_, ?_, ?_⟩
  · intro n
    convert ((hf n).comp (hmp n).measurable).aestronglyMeasurable using 1
    funext ω
    rfl
  · intro n
    simpa only [f, Statements.sampleOverlap] using (hmp n).quasiMeasurePreserving.ae (hbound n)
  · intro n
    have H := integral_map (μ := μ) (hmp n).measurable.aemeasurable
      (hf n).aestronglyMeasurable
    rw [(hmp n).map_eq] at H
    simpa only [Model.expectedOverlapPower, pow_one, f, Statements.sampleOverlap] using H

end
end TensorPCA.EstimatorTransportProofs
