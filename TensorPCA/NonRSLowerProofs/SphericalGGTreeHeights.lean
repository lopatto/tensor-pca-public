-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeCylinder
public import TensorPCA.NonRSLowerProofs.FiniteNestedInsertionNumerators

/-! Lower-CDF heights under the fixed-amplitude Gaussian pair law and weak root
insertion coefficients. The strict surrogate and bad-default estimates use those
same heights.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeHeights
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGJetFamily SphericalGGTreeCylinder
open FiniteNestedPartition FiniteNestedInsertionNumerators
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem lowerHeight_monotone {N K : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (x : Fin K → ℝ) : Monotone (fun cut : ℝ ↦ lowerHeight nu v cut x) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  let rho := ((G ×ₖ G) ∘ₘ d).map (fun p : UnitSpin N×UnitSpin N ↦ unitOverlap p.1 p.2)
  intro a b hab
  change (∫ r,(Iio a).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)≤
    (∫ r,(Iio b).indicator (fun _ ↦ (1 : ℝ)) r ∂rho)
  have hInt (cut : ℝ) : Integrable ((Iio cut).indicator (fun _ ↦ (1 : ℝ))) rho := by
    apply Integrable.of_bound (measurable_const.indicator measurableSet_Iio).aestronglyMeasurable 1
    exact .of_forall (fun r ↦ by by_cases h : r∈Iio cut <;> simp [h])
  apply integral_mono (hInt a) (hInt b)
  intro r
  by_cases h : r∈Iio a
  · have hb : r∈Iio b := lt_of_lt_of_le h hab
    simp only [Set.indicator_of_mem h,Set.indicator_of_mem hb,le_refl]
  · simp only [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _


/-- Weak monotonicity gives the height data for the strict cofinal surrogate. Endpoint
atoms remain on the complementary closed upper side.
-/
theorem own_lower_heights_properties {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) (hcuts : Monotone cuts) (x : Fin K → ℝ) :
    (∀l,0≤lowerHeight nu v (cuts l) x) ∧
    Monotone (fun l ↦ lowerHeight nu v (cuts l) x) ∧
    (∀l,lowerHeight nu v (cuts l) x≤1) :=
  ⟨fun l ↦ (lowerHeight_mem_Icc nu hv (cuts l) x).1,
    (lowerHeight_monotone nu hv x).comp hcuts,
    fun l ↦ (lowerHeight_mem_Icc nu hv (cuts l) x).2⟩

theorem own_lower_heights_measurable {N K depth : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) :
    Measurable (fun x : Fin K → ℝ ↦ fun l : Fin depth ↦ lowerHeight nu v (cuts l) x) :=
  Measurable.of_eval (fun l ↦ lowerHeight_measurable nu hv (cuts l))

/-- The weak-height root coefficients are probabilities even if heights repeat or attain
0 or 1. Only the positive full old count is divided.
-/
theorem own_root_numerator_mem_Icc {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth → ℝ) (hcuts : Monotone cuts) (x : Fin K → ℝ) (hn : 0<n)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ)∈Icc (0 : ℝ) 1 := by
  classical
  obtain ⟨hx0,hxm,hx1⟩ := own_lower_heights_properties nu hv cuts hcuts x
  have hNon (j : Insertion depth n t) : 0≤numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t j :=
    numerator_nonneg depth n _ 0 hn (le_refl 0) zero_le_one hx0 hxm hx1 t j
  have hSum : (∑j : Insertion depth n t,numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t j)=(n : ℝ) := by
    simpa only [sub_zero] using numerator_sum depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t
  have hUpper := Finset.single_le_sum (fun j _ ↦ hNon j) (Finset.mem_univ o)
  rw [hSum] at hUpper
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  exact ⟨div_nonneg (hNon o) hnR.le,(div_le_one hnR).2 hUpper⟩

theorem own_root_numerator_sum {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ)
    (cuts : Fin depth → ℝ) (x : Fin K → ℝ) (hn : 0<n)
    (t : NestedPartition depth n) :
    (∑o : Insertion depth n t,numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ))=1 := by
  rw [← Finset.sum_div,numerator_sum,sub_zero]
  exact div_self (by exact_mod_cast hn.ne')

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeHeights
