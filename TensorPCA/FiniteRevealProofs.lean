-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteConditionalEntropyProofs
public import TensorPCA.RevealPolynomialProofs

/-! Finite reveal observations and posterior information increments. -/
@[expose] public section
namespace TensorPCA.FiniteRevealProofs
open MeasureTheory ProbabilityTheory Set Real FiniteEntropyProofs FiniteConditionalEntropyProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem entropy_map_le_of_recovery {T U W : Type*} [MeasurableSpace T]
    [Fintype U] [Fintype W] [MeasurableSpace U] [MeasurableSpace W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (g : T → W)
    (hf : Measurable f) (a : U → W) (ha : Measurable a)
    (h : ∀ᵐ x ∂μ, a (f x) = g x) : entropy (μ.map g) ≤ entropy (μ.map f) := by
  have hm : (μ.map f).map a = μ.map g :=
    (Measure.map_map ha hf).trans (Measure.map_congr h)
  rw [← hm]
  exact entropy_map_le (μ.map f) a ha

theorem conditionalObservableEntropy_eq_of_recoveries {T S U W : Type*} [MeasurableSpace T]
    [Fintype S] [Fintype U] [Fintype W] [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace W]
    [MeasurableSingletonClass S] [MeasurableSingletonClass U] [MeasurableSingletonClass W]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → S) (r : T → U) (s : T → W)
    (hf : Measurable f) (hr : Measurable r) (hs : Measurable s)
    (a : U → W) (b : W → U) (ha : Measurable a) (hb : Measurable b)
    (har : ∀ᵐ x ∂μ, a (r x) = s x) (hbs : ∀ᵐ x ∂μ, b (s x) = r x) :
    conditionalObservableEntropy μ f r = conditionalObservableEntropy μ f s := by
  have ho1 := entropy_map_le_of_recovery μ r s hr a ha har
  have ho2 := entropy_map_le_of_recovery μ s r hs b hb hbs
  have hj1 := entropy_map_le_of_recovery μ (fun x ↦ (f x,r x)) (fun x ↦ (f x,s x))
    (hf.prodMk hr) (fun p : S × U ↦ (p.1,a p.2)) (measurable_of_finite _)
    (har.mono fun x hx ↦ Prod.ext rfl hx)
  have hj2 := entropy_map_le_of_recovery μ (fun x ↦ (f x,s x)) (fun x ↦ (f x,r x))
    (hf.prodMk hs) (fun p : S × W ↦ (p.1,b p.2)) (measurable_of_finite _)
    (hbs.mono fun x hx ↦ Prod.ext rfl hx)
  have hc1 := conditionalObservableEntropy_chain μ f r hf hr
  have hc2 := conditionalObservableEntropy_chain μ f s hf hs
  linarith

/-- The standard measurable tagged sum separates the hidden marker from every
alphabet value. -/
abbrev Observation (S : Type*) (N : ℕ) := Fin N → (Unit ⊕ S)

instance revealSymbol_measurableSingleton {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] : MeasurableSingletonClass (Unit ⊕ S) where
  measurableSet_singleton x := by
    cases x with
    | inl u => simpa only [Set.image_singleton] using (measurableSet_singleton u).inl_image (β := S)
    | inr s => simpa only [Set.image_singleton] using (measurableSet_singleton s).inr_image (α := Unit)

def observation {S : Type*} {N : ℕ} (A : Finset (Fin N))
    (x : PosteriorPairProofs.Configuration S N) : Observation S N :=
  fun i ↦ if i ∈ A then Sum.inr (x i) else Sum.inl ()

def mask {S : Type*} {N : ℕ} (A : Finset (Fin N)) (o : Observation S N) : Observation S N :=
  fun i ↦ if i ∈ A then o i else Sum.inl ()

theorem mask_observation {S : Type*} {N : ℕ} (A B : Finset (Fin N)) (hAB : A ⊆ B)
    (x : PosteriorPairProofs.Configuration S N) : mask A (observation B x) = observation A x := by
  funext i
  by_cases hi : i ∈ A
  · simp [mask, observation, hi, hAB hi]
  · simp [mask, observation, hi]

theorem observation_insert {S : Type*} {N : ℕ} (A : Finset (Fin N)) (j : Fin N)
    (x : PosteriorPairProofs.Configuration S N) :
    observation (insert j A) x = Function.update (observation A x) j (Sum.inr (x j)) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [observation]
  · simp [observation, hi]

def posterior {S : Type*} [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) (A : Finset (Fin N))
    (x : PosteriorPairProofs.Configuration S N) : Measure (PosteriorPairProofs.Configuration S N) :=
  condition q (observation A) (observation A x)

theorem posterior_probability {S : Type*} [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (x : PosteriorPairProofs.Configuration S N) :
    IsProbabilityMeasure (posterior q A x) := condition_probability q _ _

def coordinateEntropy {S : Type*} [Fintype S] [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) (A : Finset (Fin N)) (i : Fin N) : ℝ :=
  conditionalObservableEntropy q (fun x ↦ x i) (observation A)

def revealedPairInformation {S : Type*} [Fintype S] [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) (A : Finset (Fin N)) (i j : Fin N) : ℝ :=
  conditionalPairInformation q i j (observation A)

theorem coordinateEntropy_insert {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i j : Fin N) :
    coordinateEntropy q (insert j A) i-coordinateEntropy q A i = -revealedPairInformation q A i j := by
  have : Nonempty S := Nonempty.map (fun x : PosteriorPairProofs.Configuration S N ↦ x j)
    q.nonempty_of_neZero
  let d : S := Classical.ofNonempty
  let a : Observation S N → S × Observation S N := fun o ↦ (Sum.elim (fun _ ↦ d) id (o j), mask A o)
  let b : S × Observation S N → Observation S N := fun p ↦ Function.update p.2 j (Sum.inr p.1)
  have ha (x : PosteriorPairProofs.Configuration S N) : a (observation (insert j A) x) = (x j,observation A x) := by
    apply Prod.ext
    · simp [a, observation]
    · exact mask_observation A (insert j A) (Finset.subset_insert _ _) x
  have hb (x : PosteriorPairProofs.Configuration S N) : b (x j,observation A x) = observation (insert j A) x :=
    (observation_insert A j x).symm
  have he := conditionalObservableEntropy_eq_of_recoveries q (fun x ↦ x i)
    (observation (insert j A)) (fun x ↦ (x j,observation A x))
    (measurable_of_finite _) (measurable_of_finite _) (measurable_of_finite _)
    a b (measurable_of_finite _) (measurable_of_finite _)
    (Filter.Eventually.of_forall ha) (Filter.Eventually.of_forall hb)
  have ht := conditional_coordinate_entropy_difference q i j (observation A) (measurable_of_finite _)
  unfold coordinateEntropy revealedPairInformation
  rw [he]
  linarith

theorem coordinateEntropy_nonneg {S : Type*} [Fintype S] [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i : Fin N) : 0 ≤ coordinateEntropy q A i :=
  conditionalObservableEntropy_nonneg q _ _

theorem coordinateEntropy_le_log_card {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i : Fin N) : coordinateEntropy q A i ≤ Real.log (Fintype.card S) :=
  conditionalObservableEntropy_le_log_card q _ _ (measurable_of_finite _)

theorem coordinateEntropy_eq_zero_of_mem {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i : Fin N) (hi : i ∈ A) : coordinateEntropy q A i = 0 := by
  have : Nonempty S := Nonempty.map (fun x : PosteriorPairProofs.Configuration S N ↦ x i)
    q.nonempty_of_neZero
  let d : S := Classical.ofNonempty
  let decode : Observation S N → S := fun o ↦ Sum.elim (fun _ ↦ d) id (o i)
  have heq : (fun x : PosteriorPairProofs.Configuration S N ↦ x i) = decode ∘ observation A := by
    funext x
    simp [decode, observation, hi]
  unfold coordinateEntropy
  rw [heq]
  exact conditionalObservableEntropy_determined q _ (measurable_of_finite _) decode (measurable_of_finite _)

theorem revealedPairInformation_nonneg {S : Type*} [Fintype S] [MeasurableSpace S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N))
    (A : Finset (Fin N)) (i j : Fin N) : 0 ≤ revealedPairInformation q A i j :=
  conditionalPairInformation_nonneg q i j _

theorem revealedPairInformation_eq_zero_of_mem_left {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i j : Fin N) (hi : i ∈ A) : revealedPairInformation q A i j = 0 := by
  have h := coordinateEntropy_insert q A i j
  rw [coordinateEntropy_eq_zero_of_mem q (insert j A) i (Finset.mem_insert_of_mem hi),
    coordinateEntropy_eq_zero_of_mem q A i hi] at h
  linarith

theorem revealedPairInformation_eq_zero_of_mem_right {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i j : Fin N) (hj : j ∈ A) : revealedPairInformation q A i j = 0 := by
  have h := coordinateEntropy_insert q A i j
  rw [Finset.insert_eq_of_mem hj] at h
  linarith

theorem revealedPairInformation_diagonal {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i : Fin N) : revealedPairInformation q A i i = coordinateEntropy q A i := by
  have h := coordinateEntropy_insert q A i i
  rw [coordinateEntropy_eq_zero_of_mem q (insert i A) i (Finset.mem_insert_self _ _)] at h
  linarith

theorem posterior_pairInformation_ne_top {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (x : PosteriorPairProofs.Configuration S N) (i j : Fin N) :
    PosteriorPairProofs.pairInformation (posterior q A x) i j ≠ ∞ := by
  have := posterior_probability q A x
  exact PosteriorPairProofs.pairInformation_ne_top _ i j

/-- The reveal information is exactly the expectation under the actual latent
law of the actual revealed posterior information. -/
theorem revealedPairInformation_eq_integral {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q]
    (A : Finset (Fin N)) (i j : Fin N) :
    revealedPairInformation q A i j =
      ∫ x, (PosteriorPairProofs.pairInformation (posterior q A x) i j).toReal ∂q := by
  let f : Observation S N → ℝ := fun o ↦ (PosteriorPairProofs.pairInformation (condition q (observation A) o) i j).toReal
  have ho : Measurable (observation (S := S) A) := measurable_of_finite _
  have h := integral_map (μ := q) ho.aemeasurable
    (Integrable.of_finite (f := f)).aestronglyMeasurable
  rw [integral_fintype Integrable.of_finite] at h
  have hw (o : Observation S N) : (q.map (observation A)).real {o} = q.real (observation A ⁻¹' {o}) := by
    simp only [measureReal_def, Measure.map_apply ho (measurableSet_singleton o)]
  simp only [smul_eq_mul, hw] at h
  exact h

end
end TensorPCA.FiniteRevealProofs
