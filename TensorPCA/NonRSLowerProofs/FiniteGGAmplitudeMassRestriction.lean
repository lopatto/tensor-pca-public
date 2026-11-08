-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGGWindowLowerMass

/-! Restricting an amplitude law to amplitudes with sufficient conditional old-event
mass. No conditional mean is replaced by its average.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGGAmplitudeMassRestriction
open MeasureTheory Set Filter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem retained_amplitude_mass {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (delta : X → ℝ)
    (hDelta : Measurable delta) (hb : ∀ x,0≤delta x ∧ delta x≤1)
    (p : ℝ) (hp : 0≤p) :
    MeasurableSet {x | p/2≤delta x} ∧
      (∫ x,delta x ∂mu)-p/2≤∫ x,({x | p/2≤delta x}.indicator delta) x ∂mu ∧
      (∫ x,({x | p/2≤delta x}.indicator delta) x ∂mu)≤mu.real {x | p/2≤delta x} := by
  let S := {x | p/2≤delta x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hDelta
  have hDI : Integrable delta mu := Integrable.of_bound hDelta.aestronglyMeasurable 1
    (.of_forall (fun x ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hb x).1]; exact (hb x).2))
  have hSI : Integrable (S.indicator delta) mu := hDI.indicator hS
  have hOne : Integrable (S.indicator (fun _ : X ↦ (1 : ℝ))) mu := (integrable_const _).indicator hS
  have hPoint (x : X) : delta x≤S.indicator delta x+p/2 := by
    by_cases hx : x∈S
    · rw [Set.indicator_of_mem hx]; linarith only [hp]
    · rw [Set.indicator_of_notMem hx]
      have hlt : delta x<p/2 := lt_of_not_ge hx
      simpa only [zero_add] using hlt.le
  have H := integral_mono hDI (hSI.add (integrable_const (p/2))) hPoint
  simp only [Pi.add_apply] at H
  rw [integral_add hSI (integrable_const (p/2)),integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hRetained : (∫ x,delta x ∂mu)-p/2≤∫ x,S.indicator delta x ∂mu := by linarith only [H]
  have hMass := integral_mono hSI hOne (fun x ↦ by
    by_cases hx : x∈S
    · simpa only [Set.indicator_of_mem hx] using (hb x).2
    · simp only [Set.indicator_of_notMem hx,le_refl])
  rw [integral_indicator_const (1 : ℝ) hS,smul_eq_mul,mul_one] at hMass
  exact ⟨hS,hRetained,hMass⟩

theorem amplitude_superlevel_mass_lower {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (delta : X → ℝ)
    (hDelta : Measurable delta) (hb : ∀ x,0≤delta x ∧ delta x≤1)
    (p : ℝ) (hp : 0≤p) (hMean : p≤∫ x,delta x ∂mu) :
    MeasurableSet {x | p/2≤delta x} ∧
      p/2≤∫ x,({x | p/2≤delta x}.indicator delta) x ∂mu ∧
      p/2≤mu.real {x | p/2≤delta x} := by
  obtain ⟨hS,hRetained,hMass⟩ := retained_amplitude_mass mu delta hDelta hb p hp
  have H : p/2≤∫ x,({x | p/2≤delta x}.indicator delta) x ∂mu := by
    linarith only [hMean,hRetained]
  exact ⟨hS,H,H.trans hMass⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGGAmplitudeMassRestriction
