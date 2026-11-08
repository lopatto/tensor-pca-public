-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module

public import TensorPCA.FiniteInformationProofs

/-! Finite conditional observable entropy for posterior laws. -/
@[expose] public section
namespace TensorPCA.FiniteConditionalEntropyProofs
open MeasureTheory ProbabilityTheory Set Real FiniteEntropyProofs
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem entropy_map_le {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (f : T → U) (hf : Measurable f) : entropy (μ.map f) ≤ entropy μ := by
  have hc := entropy_chain_rule μ f hf
  have hn := conditionalEntropy_nonneg μ f
  linarith

theorem entropy_map_eq_of_leftInverse_ae {T U : Type*} [Fintype T] [Fintype U]
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] (μ : Measure T) [IsProbabilityMeasure μ]
    (f : T → U) (g : U → T) (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ᵐ x ∂μ, g (f x) = x) : entropy (μ.map f) = entropy μ := by
  have hmap : (μ.map f).map g = μ := by
    calc
      _ = μ.map (fun x ↦ g (f x)) := Measure.map_map hg hf
      _ = μ.map id := Measure.map_congr hgf
      _ = μ := Measure.map_id
  have h1 := entropy_map_le μ f hf
  have h2 := entropy_map_le (μ.map f) g hg
  rw [hmap] at h2
  exact le_antisymm h1 h2

/-- Conditioning commutes with the actual pushforward when the observation
factors through it. The same original-law fallback handles all null fibers. -/
theorem condition_map {T U W : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSpace W] [MeasurableSingletonClass W] (μ : Measure T)
    (f : T → U) (hf : Measurable f) (r : U → W) (hr : Measurable r) (w : W) :
    (condition μ (r ∘ f) w).map f = condition (μ.map f) r w := by
  unfold condition
  rw [Measure.map_apply hf (hr (measurableSet_singleton w))]
  have hpre : f ⁻¹' (r ⁻¹' {w}) = (r ∘ f) ⁻¹' {w} := rfl
  rw [hpre]
  split_ifs
  · rfl
  · rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul _ hf.aemeasurable,
      Measure.restrict_map hf (hr (measurableSet_singleton w)),
      Measure.map_apply hf (hr (measurableSet_singleton w)), hpre]

def conditionalObservableEntropy {T U W : Type*} [MeasurableSpace T] [MeasurableSpace U]
    [MeasurableSpace W] [Fintype U] [Fintype W] (μ : Measure T) (f : T → U) (r : T → W) : ℝ :=
  ∑ w : W, μ.real (r ⁻¹' {w})*entropy ((condition μ r w).map f)

theorem conditionalObservableEntropy_nonneg {T U W : Type*}
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace W] [Fintype U] [Fintype W]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (r : T → W) :
    0 ≤ conditionalObservableEntropy μ f r := by
  apply Finset.sum_nonneg
  intro w _
  have := condition_probability μ r w
  exact mul_nonneg measureReal_nonneg (entropy_nonneg _)

theorem conditionalObservableEntropy_le_log_card {T U W : Type*}
    [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace W] [Fintype U] [Fintype W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (r : T → W) (hr : Measurable r) :
    conditionalObservableEntropy μ f r ≤ Real.log (Fintype.card U) := by
  have hsum : (∑ w : W, μ.real (r ⁻¹' {w})) = 1 := by
    rw [sum_measureReal_preimage_singleton Finset.univ (fun w _ ↦ hr (measurableSet_singleton w))]
    simp
  calc
    _ ≤ ∑ w : W, μ.real (r ⁻¹' {w})*Real.log (Fintype.card U) := by
      apply Finset.sum_le_sum
      intro w _
      have := condition_probability μ r w
      exact mul_le_mul_of_nonneg_left (entropy_le_log_card _) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem entropy_condition_prod_snd {U W : Type*} [Fintype U] [Fintype W]
    [MeasurableSpace U] [MeasurableSpace W] [MeasurableSingletonClass U]
    [MeasurableSingletonClass W] (P : Measure (U × W)) [IsProbabilityMeasure P] (w : W)
    (hw : P (Prod.snd ⁻¹' {w}) ≠ 0) :
    entropy (condition P Prod.snd w) = entropy ((condition P Prod.snd w).map Prod.fst) := by
  have := condition_probability P Prod.snd w
  have hmem : ∀ᵐ p ∂condition P Prod.snd w, p.2 = w := by
    unfold condition
    rw [ite_eq_right hw]
    exact ae_cond_mem (measurable_snd (measurableSet_singleton w))
  have hleft : ∀ᵐ p ∂condition P Prod.snd w, (p.1,w) = p := by
    filter_upwards [hmem] with p hp
    exact Prod.ext rfl hp.symm
  exact (entropy_map_eq_of_leftInverse_ae (condition P Prod.snd w) Prod.fst
    (fun u ↦ (u,w)) measurable_fst measurable_prodMk_right hleft).symm

/-- The conditional entropy of an observable is the actual finite joint entropy
minus its observation entropy, including the explicit null-fiber convention. -/
theorem conditionalObservableEntropy_chain {T U W : Type*} [MeasurableSpace T]
    [Fintype U] [Fintype W] [MeasurableSpace U] [MeasurableSpace W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (r : T → W)
    (hf : Measurable f) (hr : Measurable r) :
    entropy (μ.map (fun x ↦ (f x,r x))) = entropy (μ.map r)+conditionalObservableEntropy μ f r := by
  let F : T → U × W := fun x ↦ (f x,r x)
  have hF : Measurable F := hf.prodMk hr
  let P := μ.map F
  have hobs : P.map Prod.snd = μ.map r := by
    dsimp only [P]
    rw [Measure.map_map measurable_snd hF]
    rfl
  have hfib (w : W) : P (Prod.snd ⁻¹' {w}) = μ (r ⁻¹' {w}) := by
    dsimp only [P]
    rw [Measure.map_apply hF (measurable_snd (measurableSet_singleton w))]
    rfl
  have hpush (w : W) : (condition μ r w).map f = (condition P Prod.snd w).map Prod.fst := by
    have h := condition_map μ F hF Prod.snd measurable_snd w
    change (condition μ r w).map F = condition P Prod.snd w at h
    calc
      _ = ((condition μ r w).map F).map Prod.fst := by
        rw [Measure.map_map measurable_fst hF]
        rfl
      _ = _ := by rw [h]
  have hc := entropy_chain_rule P Prod.snd measurable_snd
  rw [hobs] at hc
  have he : conditionalEntropy P Prod.snd = conditionalObservableEntropy μ f r := by
    unfold conditionalEntropy conditionalObservableEntropy
    apply Finset.sum_congr rfl
    intro w _
    have hrealfib : P.real (Prod.snd ⁻¹' {w}) = μ.real (r ⁻¹' {w}) :=
      congrArg ENNReal.toReal (hfib w)
    rw [hrealfib]
    by_cases hw : μ (r ⁻¹' {w}) = 0
    · simp [measureReal_def, hw]
    have hp : P (Prod.snd ⁻¹' {w}) ≠ 0 := by rwa [hfib]
    rw [entropy_condition_prod_snd P w hp, ← hpush]
  rw [he] at hc
  exact hc

theorem conditionalObservableEntropy_determined {T U W : Type*} [MeasurableSpace T]
    [Fintype U] [Fintype W] [MeasurableSpace U] [MeasurableSpace W]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W]
    (μ : Measure T) [IsProbabilityMeasure μ] (r : T → W) (hr : Measurable r)
    (f : W → U) (hf : Measurable f) : conditionalObservableEntropy μ (f ∘ r) r = 0 := by
  have hc := conditionalObservableEntropy_chain μ (f ∘ r) r (hf.comp hr) hr
  have he := entropy_map_eq_of_leftInverse_ae (μ.map r) (fun w ↦ (f w,w)) Prod.snd
    (hf.prodMk measurable_id) measurable_snd (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hm : (μ.map r).map (fun w ↦ (f w,w)) = μ.map (fun x ↦ ((f ∘ r) x,r x)) :=
    Measure.map_map (hf.prodMk measurable_id) hr
  rw [hm] at he
  linarith

theorem entropy_pair_assoc {T U W Z : Type*} [MeasurableSpace T]
    [Fintype U] [Fintype W] [Fintype Z] [MeasurableSpace U] [MeasurableSpace W] [MeasurableSpace Z]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W] [MeasurableSingletonClass Z]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (g : T → W) (r : T → Z)
    (hf : Measurable f) (hg : Measurable g) (hr : Measurable r) :
    entropy (μ.map (fun x ↦ ((f x,g x),r x))) = entropy (μ.map (fun x ↦ (f x,(g x,r x)))) := by
  let F : T → (U × W) × Z := fun x ↦ ((f x,g x),r x)
  let P := μ.map F
  let a : (U × W) × Z → U × W × Z := fun p ↦ (p.1.1,(p.1.2,p.2))
  let b : U × W × Z → (U × W) × Z := fun p ↦ ((p.1,p.2.1),p.2.2)
  have ha : Measurable a := measurable_of_finite _
  have h := entropy_map_eq_of_leftInverse_ae P a b ha (measurable_of_finite _)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hmap : P.map a = μ.map (fun x ↦ (f x,(g x,r x))) := by
    dsimp only [P]
    rw [Measure.map_map ha (show Measurable F from (hf.prodMk hg).prodMk hr)]
    rfl
  rw [hmap] at h
  exact h.symm

/-- Actual conditional entropy chain/tower rule for finite observables. -/
theorem conditionalObservableEntropy_tower {T U W Z : Type*} [MeasurableSpace T]
    [Fintype U] [Fintype W] [Fintype Z] [MeasurableSpace U] [MeasurableSpace W] [MeasurableSpace Z]
    [MeasurableSingletonClass U] [MeasurableSingletonClass W] [MeasurableSingletonClass Z]
    (μ : Measure T) [IsProbabilityMeasure μ] (f : T → U) (g : T → W) (r : T → Z)
    (hf : Measurable f) (hg : Measurable g) (hr : Measurable r) :
    conditionalObservableEntropy μ (fun x ↦ (f x,g x)) r =
      conditionalObservableEntropy μ g r+
        conditionalObservableEntropy μ f (fun x ↦ (g x,r x)) := by
  have hfg := conditionalObservableEntropy_chain μ (fun x ↦ (f x,g x)) r (hf.prodMk hg) hr
  have hg' := conditionalObservableEntropy_chain μ g r hg hr
  have hf' := conditionalObservableEntropy_chain μ f (fun x ↦ (g x,r x)) hf (hg.prodMk hr)
  have ha := entropy_pair_assoc μ f g r hf hg hr
  linarith

def conditionalPairInformation {S W : Type*} [Fintype S] [Fintype W]
    [MeasurableSpace S] [MeasurableSpace W] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) (i j : Fin N)
    (r : PosteriorPairProofs.Configuration S N → W) : ℝ :=
  ∑ w : W, q.real (r ⁻¹' {w})*(PosteriorPairProofs.pairInformation (condition q r w) i j).toReal

theorem conditioned_pairInformation_ne_top {S W : Type*} [Fintype S]
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q] (i j : Fin N)
    (r : PosteriorPairProofs.Configuration S N → W) (w : W) :
    PosteriorPairProofs.pairInformation (condition q r w) i j ≠ ∞ := by
  have := condition_probability q r w
  exact PosteriorPairProofs.pairInformation_ne_top _ i j

theorem conditionalPairInformation_nonneg {S W : Type*} [Fintype S] [Fintype W]
    [MeasurableSpace S] [MeasurableSpace W] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) (i j : Fin N)
    (r : PosteriorPairProofs.Configuration S N → W) : 0 ≤ conditionalPairInformation q i j r := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg measureReal_nonneg ENNReal.toReal_nonneg

theorem conditionalPairInformation_eq_entropies {S W : Type*} [Fintype S] [Fintype W]
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSingletonClass S] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q] (i j : Fin N)
    (r : PosteriorPairProofs.Configuration S N → W) :
    conditionalPairInformation q i j r =
      conditionalObservableEntropy q (fun x ↦ x i) r+
        conditionalObservableEntropy q (fun x ↦ x j) r-
          conditionalObservableEntropy q (fun x ↦ (x i,x j)) r := by
  unfold conditionalPairInformation conditionalObservableEntropy
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have := condition_probability q r w
  rw [FiniteInformationProofs.pairInformation_eq_entropies]
  change _ = _
  dsimp only [PosteriorPairProofs.coordinateLaw, PosteriorPairProofs.pairLaw]
  ring

/-- Adding another revealed coordinate cannot increase a coordinate's actual
conditional entropy. The difference is actual averaged pair KL. -/
theorem conditional_coordinate_entropy_difference {S W : Type*} [Fintype S] [Fintype W]
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSingletonClass S]
    [MeasurableSingletonClass W] {N : ℕ}
    (q : Measure (PosteriorPairProofs.Configuration S N)) [IsProbabilityMeasure q] (i j : Fin N)
    (r : PosteriorPairProofs.Configuration S N → W) (hr : Measurable r) :
    conditionalObservableEntropy q (fun x ↦ x i) r-
      conditionalObservableEntropy q (fun x ↦ x i) (fun x ↦ (x j,r x)) =
        conditionalPairInformation q i j r := by
  have h := conditionalPairInformation_eq_entropies q i j r
  have ht := conditionalObservableEntropy_tower q (fun x ↦ x i) (fun x ↦ x j) r
    (measurable_pi_apply i) (measurable_pi_apply j) hr
  linarith

end
end TensorPCA.FiniteConditionalEntropyProofs
