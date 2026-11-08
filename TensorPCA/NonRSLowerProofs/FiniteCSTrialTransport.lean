-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCSPositivity

/-! Exact transport from standard compact probability trials to the real-line measure
used by the source CS calculus. This map keeps the law and integrated CDF; it does
not discard the linear covariance contribution.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCS
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

/-- The identical overlap law viewed as a measure on the real line. -/
def realLaw (nu : Trial) : Measure ℝ :=
  (nu : Measure Overlap).map ((↑) : Overlap → ℝ)

instance realLaw_isProbability (nu : Trial) : IsProbabilityMeasure (realLaw nu) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance

theorem realLaw_mem_interval (nu : Trial) : ∀ᵐ q ∂realLaw nu, q ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact .of_forall fun q => q.property

theorem xHat_realLaw (nu : Trial) (t : ℝ) :
    RetainedCountProofs.CrisantiSommers.xHat (realLaw nu) t =
      hatCDF (nu : Measure Overlap) t := by
  unfold RetainedCountProofs.CrisantiSommers.xHat realLaw hatCDF
  rw [integral_map measurable_subtype_coe.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun q : ℝ => 1 - max t q)
      ((nu : Measure Overlap).map ((↑) : Overlap → ℝ)))]
  rfl

theorem profile_eq_scaled_xHat_realLaw (beta : ℝ) (nu : Trial) (t : ℝ) :
    profile beta nu t = beta * RetainedCountProofs.CrisantiSommers.xHat (realLaw nu) t := by
  rw [xHat_realLaw]
  rfl

theorem realLaw_hasCutoff (nu : Trial) {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1)
    (hnu : ∀ᵐ a : Overlap ∂(nu : Measure Overlap), (a : ℝ) ≤ q) :
    RetainedCountProofs.CrisantiSommers.HasCutoff (realLaw nu) q := by
  refine ⟨hq.1, hq.2, ?_⟩
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  filter_upwards [hnu] with a ha
  exact ⟨a.property.1, ha⟩

end
end TensorPCA.NonRSLowerProofs.FiniteCS
