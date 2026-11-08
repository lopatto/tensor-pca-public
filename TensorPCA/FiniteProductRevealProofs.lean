-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FinitePriorChannelProofs
public import TensorPCA.FiniteRevealProofs

/-! Coordinate override is the finite product-prior reveal posterior
on every positive reveal fiber. Null fibers retain the established fallback. -/
@[expose] public section
namespace TensorPCA.FiniteProductRevealProofs
open MeasureTheory ProbabilityTheory Set Filter FinitePriorChannelProofs FiniteRevealProofs FiniteEntropyProofs
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [MeasurableSpace S]

def override {N : ℕ} (A : Finset (Fin N)) (X x : Fin N → S) : Fin N → S :=
  fun i ↦ if i ∈ A then X i else x i

theorem observation_fiber_eq_pi {N : ℕ} (A : Finset (Fin N)) (X : Fin N → S) :
    observation A ⁻¹' {observation A X} = Set.univ.pi (fun i ↦ if i ∈ A then {X i} else Set.univ) := by
  ext x
  constructor
  · intro hx
    have he : observation A x = observation A X := hx
    intro i _
    by_cases hi : i ∈ A
    · have H := congrFun he i
      simpa only [observation,hi,ite_true,Sum.inr.injEq,Set.mem_singleton_iff] using H
    · simp only [hi,ite_false,Set.mem_univ]
  · intro hx
    change observation A x = observation A X
    funext i
    by_cases hi : i ∈ A
    · have H := hx i (Set.mem_univ i)
      simpa only [hi,ite_true,Set.mem_singleton_iff,observation,Sum.inr.injEq] using H
    · simp only [observation,hi,ite_false]

variable [Fintype S] [MeasurableSingletonClass S]

theorem map_override_eq_pi (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin N)) (X : Fin N → S) :
    (configurationPrior p N).map (override A X) = Measure.pi (fun i : Fin N ↦ if i ∈ A then Measure.dirac (X i) else p) := by
  change (Measure.pi (fun _ : Fin N ↦ p)).map (fun x i ↦ if i ∈ A then X i else x i) = _
  rw [Measure.pi_map_pi (fun i ↦ (measurable_of_finite (fun s : S ↦ if i ∈ A then X i else s)).aemeasurable)]
  congr 1
  funext i
  by_cases hi : i ∈ A <;> simp [hi]

/-- The override law reconstructs the exact restricted product prior after
multiplication by the reveal-fiber mass, including null reveal fibers. -/
theorem weighted_map_override_singleton (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin N)) (X y : Fin N → S) :
    (configurationPrior p N) (observation A ⁻¹' {observation A X})*
      ((configurationPrior p N).map (override A X)) {y} =
      (configurationPrior p N) ((observation A ⁻¹' {observation A X}) ∩ {y}) := by
  let C : Fin N → Set S := fun i ↦ if i ∈ A then {X i} else Set.univ
  have hset : (Set.univ.pi C) ∩ {y} = Set.univ.pi (fun i ↦ C i ∩ {y i}) := by
    ext z
    constructor
    · rintro ⟨hz,rfl⟩
      intro i hi
      exact ⟨hz i hi,rfl⟩
    · intro hz
      have he : z = y := funext (fun i ↦ (hz i (Set.mem_univ i)).2)
      exact ⟨fun i hi ↦ (hz i hi).1,he⟩
  rw [map_override_eq_pi p,observation_fiber_eq_pi]
  change (Measure.pi (fun _ : Fin N ↦ p)) (Set.univ.pi C)*
      (Measure.pi (fun i : Fin N ↦ if i ∈ A then Measure.dirac (X i) else p)) {y} =
    (Measure.pi (fun _ : Fin N ↦ p)) ((Set.univ.pi C) ∩ {y})
  rw [hset,Measure.pi_pi,Measure.pi_singleton,Measure.pi_pi,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · by_cases hxy : X i = y i
    · simp [C,hi,hxy]
    · simp [C,hi,hxy,Set.singleton_inter_eq_empty]
  · simp [C,hi]

theorem map_override_eq_posterior (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin N)) (X : Fin N → S)
    (hX : (configurationPrior p N) (observation A ⁻¹' {observation A X}) ≠ 0) :
    (configurationPrior p N).map (override A X) = posterior (configurationPrior p N) A X := by
  apply Measure.ext_of_singleton
  intro y
  unfold posterior condition
  rw [ite_eq_right hX,cond_apply ((measurable_of_finite (observation A)) (measurableSet_singleton _)),
    ← weighted_map_override_singleton p A X y,← mul_assoc,
    ENNReal.inv_mul_cancel hX (measure_ne_top _ _),one_mul]

theorem revealFiber_nonzero_ae (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin N)) : ∀ᵐ X ∂configurationPrior p N,
      (configurationPrior p N) (observation A ⁻¹' {observation A X}) ≠ 0 := by
  apply ae_iff_of_countable.mpr
  intro X hX hzero
  apply hX
  apply measure_mono_null _ hzero
  intro x hx
  have he : x = X := hx
  subst x
  rfl

/-- Almost every actual planted product-prior sample has exactly the existing
finite reveal posterior as its coordinate-override pushforward. -/
theorem map_override_eq_posterior_ae (p : Measure S) [IsProbabilityMeasure p] {N : ℕ}
    (A : Finset (Fin N)) : ∀ᵐ X ∂configurationPrior p N,
      (configurationPrior p N).map (override A X) = posterior (configurationPrior p N) A X := by
  filter_upwards [revealFiber_nonzero_ae p A] with X hX
  exact map_override_eq_posterior p A X hX

end
end TensorPCA.FiniteProductRevealProofs
