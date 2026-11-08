-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSTrialTransport
public import TensorPCA.NonRSLowerProofs.FiniteCSTwoAtom

/-! Every real-line cutoff law in the source CS class is a standard compact trial. The
reverse map is the standard measure comap, with its exact round-trip proved rather
than an assumed covariance equivalence.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

theorem cutoff_mem_interval (mu : Measure ℝ) {q : ℝ}
    (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) :
    ∀ᵐ a ∂mu, a ∈ Icc (0 : ℝ) 1 :=
  hq.2.2.mono fun _ ha => ⟨ha.1, ha.2.trans hq.2.1.le⟩

theorem cutoffComap_isProbability (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {q : ℝ} (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) :
    IsProbabilityMeasure (Measure.comap ((↑) : Overlap → ℝ) mu) := by
  have hm : IsProbabilityMeasure ((Measure.comap ((↑) : Overlap → ℝ) mu).map
      ((↑) : Overlap → ℝ)) := by
    rw [map_comap_subtype_coe measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem (cutoff_mem_interval mu hq)]
    infer_instance
  exact (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mp hm

def cutoffTrial (mu : Measure ℝ) [IsProbabilityMeasure mu] {q : ℝ}
    (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) : Trial :=
  ⟨Measure.comap ((↑) : Overlap → ℝ) mu, cutoffComap_isProbability mu hq⟩

theorem realLaw_cutoffTrial (mu : Measure ℝ) [IsProbabilityMeasure mu] {q : ℝ}
    (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) :
    realLaw (cutoffTrial mu hq) = mu := by
  exact (map_comap_subtype_coe measurableSet_Icc mu).trans
    (Measure.restrict_eq_self_of_ae_mem (cutoff_mem_interval mu hq))

theorem cutoffTrial_ae_le (mu : Measure ℝ) [IsProbabilityMeasure mu] {q : ℝ}
    (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) :
    ∀ᵐ a : Overlap ∂(cutoffTrial mu hq : Measure Overlap), (a : ℝ) ≤ q := by
  change ∀ᵐ a : Overlap ∂Measure.comap ((↑) : Overlap → ℝ) mu, (a : ℝ) ≤ q
  exact (ae_restrict_iff_subtype (μ := mu) (s := Icc (0 : ℝ) 1)
    (p := fun a => a ≤ q) measurableSet_Icc).mp
    (ae_restrict_of_ae (hq.2.2.mono fun _ ha => ha.2))

theorem xHat_cutoffTrial (mu : Measure ℝ) [IsProbabilityMeasure mu] {q : ℝ}
    (hq : RetainedCountProofs.CrisantiSommers.HasCutoff mu q) (t : ℝ) :
    hatCDF (cutoffTrial mu hq : Measure Overlap) t =
      RetainedCountProofs.CrisantiSommers.xHat mu t := by
  rw [← xHat_realLaw, realLaw_cutoffTrial]

end
end TensorPCA.NonRSLowerProofs.FiniteCS
