-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeRootInsertionGG
public import TensorPCA.NonRSLowerProofs.SphericalGGTreeHeights

/-! Unnormalized cylinder insertion residual under consecutive iid laws. The recurrence
uses the lower-tail heights of the amplitude pair law and the full old replica count
as denominator, without conditioning on a parent event.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionResidual
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGTreeCylinder SphericalGGTreeExtraction SphericalGGTreeHeights SphericalGGJetFamily
open SphericalGGTreeBallAverage SphericalGGTreeRootInsertionGG SphericalGGThresholdFirstMomentAverage
open FiniteNestedPartition FiniteNestedInsertionNumerators
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cylinderInsertionResidual {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ)
    (cuts : Fin depth→ℝ) (t : NestedPartition depth n) (o : Insertion depth n t)
    (x : Fin K→ℝ) : ℝ :=
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
  let G := (parameterizedGibbsKernel nu v).sectR x
  (law d G (n+1)).real {s | treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) s}-
    (law d G n).real {old | treeCylinder cuts t old}*
      (numerator depth n (fun l ↦ lowerHeight nu v (cuts l) x) 0 t o/(n : ℝ))

private theorem numerator_parameter_measurable {A : Type*} [MeasurableSpace A]
    (depth n : ℕ) (y : A→Fin depth→ℝ) (p : A→ℝ)
    (hy : ∀l,Measurable (fun x ↦ y x l)) (hp : Measurable p)
    (t : NestedPartition depth n) (o : Insertion depth n t) :
    Measurable (fun x ↦ numerator depth n (y x) (p x) t o) := by
  induction depth generalizing n p with
  | zero => exact measurable_const.sub hp
  | succ depth ih =>
    obtain ⟨c,f⟩ := t
    cases o with
    | none => exact ((hy 0).const_mul (c.length : ℝ)).sub hp
    | some a =>
      obtain ⟨i,o⟩ := a
      exact ih (c.partSize i) (fun x l ↦ y x l.succ) (fun x ↦ y x 0)
        (fun l ↦ hy l.succ) (hy 0) (f i) o

private theorem actualCylinderMass_measurable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (t : NestedPartition depth n) :
    Measurable (fun x : Fin K→ℝ ↦
      (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) n).real {old | treeCylinder cuts t old}) := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  let Phi : (Fin n→UnitSpin N)→ℝ := {old | treeCylinder cuts t old}.indicator (fun _ ↦ 1)
  have hPhi : Measurable Phi := measurable_const.indicator (treeCylinder_measurable cuts t)
  have hPb (old) : |Phi old|≤1 := by by_cases h : treeCylinder cuts t old <;> simp [Phi,h]
  have H := parameterized_law_integral_measurable
    (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) (parameterizedGibbsKernel nu v)
    n (fun _ old ↦ Phi old) (hPhi.comp measurable_snd) (fun _ old ↦ hPb old)
  simpa only [Phi,integral_indicator_const (1 : ℝ) (treeCylinder_measurable cuts t),smul_eq_mul,mul_one] using H

theorem cylinderInsertionResidual_measurable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (t : NestedPartition depth n) (o : Insertion depth n t) :
    Measurable (cylinderInsertionResidual (K := K) nu v cuts t o) :=
  (actualCylinderMass_measurable nu hv cuts ((extendEquiv depth n) ⟨t,o⟩)).sub
    ((actualCylinderMass_measurable nu hv cuts t).mul
      ((numerator_parameter_measurable depth n (fun x l ↦ lowerHeight nu v (cuts l) x)
        (fun _ ↦ 0) (fun l ↦ lowerHeight_measurable nu hv (cuts l)) measurable_const t o).div_const _))

theorem cylinderInsertionResidual_abs_le_one {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (t : NestedPartition depth n)
    (o : Insertion depth n t) (x : Fin K→ℝ) (hn : 0<n) :
    |cylinderInsertionResidual nu v cuts t o x|≤1 := by
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  have hMass {A : Type} [MeasurableSpace A] (mu : Measure A) [IsProbabilityMeasure mu] (S : Set A) :
      mu.real S∈Icc (0 : ℝ) 1 := by
    refine ⟨measureReal_nonneg,?_⟩
    simpa only [probReal_univ] using measureReal_mono (subset_univ S) (measure_ne_top mu _)
  have hOld := hMass (A := Fin n→UnitSpin N) (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) n) {old | treeCylinder cuts t old}
  have hNew := hMass (A := Fin (n+1)→UnitSpin N) (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    ((parameterizedGibbsKernel nu v).sectR x) (n+1))
      {s | treeCylinder cuts ((extendEquiv depth n) ⟨t,o⟩) s}
  have hW := own_root_numerator_mem_Icc nu hv cuts hcuts x hn t o
  have hP0 := mul_nonneg hOld.1 hW.1
  have hP1 := mul_le_mul hOld.2 hW.2 hW.1 zero_le_one
  norm_num only [mul_one] at hP1
  unfold cylinderInsertionResidual
  dsimp only
  exact abs_le.mpr ⟨by linarith only [hNew.1,hP1],by linarith only [hNew.2,hP0]⟩

theorem cylinderInsertionResidual_integrable {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (cuts : Fin depth→ℝ) (hcuts : Monotone cuts) (t : NestedPartition depth n)
    (o : Insertion depth n t) (hn : 0<n) :
    Integrable (cylinderInsertionResidual (K := K) nu v cuts t o) (positiveCubeLaw K) :=
  Integrable.of_bound (cylinderInsertionResidual_measurable nu hv cuts t o).aestronglyMeasurable 1
    (.of_forall (fun x ↦ by simpa only [Real.norm_eq_abs] using cylinderInsertionResidual_abs_le_one nu hv cuts hcuts t o x hn))

theorem insertion_none_error_le {N K depth n : ℕ}
    (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] {v : ℝ} (hv : 0≤v)
    (x : Fin K→ℝ) (cuts : Fin (depth+1)→ℝ) (hcuts : Monotone cuts) (hcuts1 : ∀l,cuts l≤1)
    (c : OrderedFinpartition (n+1)) (f : Children depth c) :
    |cylinderInsertionResidual nu v cuts (⟨c,f⟩ : NestedPartition (depth+1) (n+1)) none x|≤
      (∑b : Fin c.length,|freshBallResidual nu v cuts (⟨c,f⟩ : NestedPartition (depth+1) (n+1)) 0
        (c.emb b ⟨0,c.partSize_pos b⟩) x|)+
      ((c.length : ℝ)+2)*(law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((parameterizedGibbsKernel nu v).sectR x) (n+2)).real {s | ¬thresholdGood cuts s} := by
  simpa only [cylinderInsertionResidual,numerator,sub_zero,Nat.cast_add,Nat.cast_one,mul_div_assoc] using
    root_new_cylinder_error_le nu hv x cuts hcuts hcuts1 c f

end
end TensorPCA.NonRSLowerProofs.SphericalGGTreeInsertionResidual
