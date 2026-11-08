-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedMassMeasurability
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianMarkedMoments

/-! Joint measurability of the weighted marked moment in the parameter and common field.
Gaussian maps and the bounded mark stay fixed; only the section-dependent heights
and the parent vary.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedMarkedMomentMeasurability
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedDiscountedPartitionLaw FiniteNestedMassMeasurability
open FiniteNestedGaussianMarkedMoments
open scoped BigOperators
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem weightedMoment_joint_measurable (depth n : ℕ) (T : Fin depth→E→L[ℝ]E)
    {Z : E→ℝ} (hZ : Measurable Z) :
    Measurable (fun p : ((Fin depth→ℝ)×ℝ)×E ↦
      weightedMoment depth n p.1.1 p.1.2 T Z p.2) := by
  classical
  unfold weightedMoment
  exact Finset.measurable_sum _ (fun t _ ↦
    ((mass_joint_measurable depth n t).comp measurable_fst).mul
      ((treeMoment_measurable depth n T hZ t).comp measurable_snd))

theorem weightedMoment_measurable_comp {S : Type*} [MeasurableSpace S]
    (depth n : ℕ) (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z)
    (x : S→Fin depth→ℝ) (p : S→ℝ) (z : S→E)
    (hx : Measurable x) (hp : Measurable p) (hz : Measurable z) :
    Measurable (fun s ↦ weightedMoment depth n (x s) (p s) T Z (z s)) :=
  (weightedMoment_joint_measurable depth n T hZ).comp ((hx.prodMk hp).prodMk hz)

theorem weightedMoment_params_joint_measurable {S : Type*} [MeasurableSpace S]
    (depth n : ℕ) (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z)
    (x : S→Fin depth→ℝ) (p : S→ℝ) (hx : Measurable x) (hp : Measurable p) :
    Measurable (fun w : S×E ↦ weightedMoment depth n (x w.1) (p w.1) T Z w.2) :=
  weightedMoment_measurable_comp depth n T hZ (fun w : S×E ↦ x w.1)
    (fun w : S×E ↦ p w.1) Prod.snd (hx.comp measurable_fst) (hp.comp measurable_fst) measurable_snd

theorem weightedMoment_params_mem {S : Type*} (depth n : ℕ) (T : Fin depth→E→L[ℝ]E)
    {Z : E→ℝ} (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (hBound : ∀z,0≤Z z ∧ Z z≤a)
    (x : S→Fin depth→ℝ) (p : S→ℝ)
    (hp0 : ∀s,0≤p s) (hpx : ∀s j,p s<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (s : S) (z : E) :
    0≤weightedMoment depth n (x s) (p s) T Z z ∧ weightedMoment depth n (x s) (p s) T Z z≤a^n :=
  weightedMoment_mem depth n (x s) (p s) (hp0 s) (hpx s) (hxm s) (hx1 s) T hZ ha hBound z

/-- Any joint amplitude/common-field probability is allowed, including the independent
product law used by Gaussian marking.
-/
theorem weightedMoment_params_integrable {S : Type*} [MeasurableSpace S]
    (depth n : ℕ) (T : Fin depth→E→L[ℝ]E) {Z : E→ℝ} (hZ : Measurable Z)
    {a : ℝ} (ha : 0≤a) (hBound : ∀z,0≤Z z ∧ Z z≤a)
    (x : S→Fin depth→ℝ) (p : S→ℝ) (hx : Measurable x) (hp : Measurable p)
    (hp0 : ∀s,0≤p s) (hpx : ∀s j,p s<x s j) (hxm : ∀s,StrictMono (x s)) (hx1 : ∀s j,x s j≤1)
    (eta : Measure (S×E)) [IsProbabilityMeasure eta] :
    Integrable (fun w : S×E ↦ weightedMoment depth n (x w.1) (p w.1) T Z w.2) eta := by
  apply Integrable.of_bound (weightedMoment_params_joint_measurable depth n T hZ x p hx hp).aestronglyMeasurable (a^n)
  exact ae_of_all _ (fun w ↦ by
    have H := weightedMoment_params_mem depth n T hZ ha hBound x p hp0 hpx hxm hx1 w.1 w.2
    rw [Real.norm_of_nonneg H.1]
    exact H.2)

end
end TensorPCA.NonRSLowerProofs.FiniteNestedMarkedMomentMeasurability
