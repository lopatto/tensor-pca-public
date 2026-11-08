-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianNodeMarking

/-! Independent cavity-coordinate copies of the finite tree Gaussian mark. A single
Euclidean Gaussian bank is grouped into node vectors.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteNestedGaussianVectorLaw
open MeasureTheory ProbabilityTheory
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedGaussianFeature
open FiniteNestedGaussianNodeMarking FiniteNestedGaussianMarkedMoments
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def nodeNoise {depth n : ℕ} (t : NestedPartition depth n) (M : ℕ)
    (g : EuclideanSpace ℝ (Σc : Coordinate t,Fin M)) :
    Coordinate t→EuclideanSpace ℝ (Fin M) :=
  fun c => WithLp.toLp 2 (fun j => g ⟨c,j⟩)

theorem nodeNoise_continuous {depth n : ℕ} (t : NestedPartition depth n) (M : ℕ) :
    Continuous (nodeNoise t M) := by
  unfold nodeNoise
  fun_prop

theorem nodeNoise_law {depth n : ℕ} (t : NestedPartition depth n) (M : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M))).map (nodeNoise t M)=
      Measure.pi (fun _ : Coordinate t => stdGaussian (EuclideanSpace ℝ (Fin M))) := by
  let curry := MeasurableEquiv.piCurry (fun (_ : Coordinate t) (_ : Fin M) => ℝ)
  let lift := fun noise : Coordinate t→Fin M→ℝ =>
    fun c : Coordinate t => (WithLp.toLp 2 (noise c) : EuclideanSpace ℝ (Fin M))
  have hCurry : (Measure.pi (fun _ : Σc : Coordinate t,Fin M => gaussianReal 0 1)).map curry=
      Measure.pi (fun _ : Coordinate t => Measure.pi (fun _ : Fin M => gaussianReal 0 1)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry (fun (_ : Coordinate t) (_ : Fin M) => gaussianReal 0 1))
  have hLift : (Measure.pi (fun _ : Coordinate t => Measure.pi (fun _ : Fin M => gaussianReal 0 1))).map lift=
      Measure.pi (fun _ : Coordinate t => stdGaussian (EuclideanSpace ℝ (Fin M))) := by
    rw [Measure.pi_map_pi (fun _ => by fun_prop)]
    simp_rw [map_pi_eq_stdGaussian]
  rw [← map_pi_eq_stdGaussian,Measure.map_map (nodeNoise_continuous t M).measurable (by fun_prop)]
  change (Measure.pi (fun _ : Σc : Coordinate t,Fin M => gaussianReal 0 1)).map (lift ∘curry)=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),hCurry,hLift]

def vectorReplicaField {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (M : ℕ)
    (g : EuclideanSpace ℝ (Σc : Coordinate t,Fin M)) : Fin n→EuclideanSpace ℝ (Fin M) :=
  nodeField t y (nodeNoise t M g)

def observedFeature {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (i : Fin n) {M : ℕ} (u : EuclideanSpace ℝ (Fin M)) :
    EuclideanSpace ℝ (Σc : Coordinate t,Fin M) :=
  WithLp.toLp 2 (fun p => values t y i p.1*u p.2)

theorem observed_field {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (i : Fin n) {M : ℕ} (u : EuclideanSpace ℝ (Fin M))
    (g : EuclideanSpace ℝ (Σc : Coordinate t,Fin M)) :
    inner ℝ u (vectorReplicaField t y M g i)=inner ℝ (observedFeature t y i u) g := by
  simp only [vectorReplicaField,nodeField,inner_sum,real_inner_smul_right]
  simp only [nodeNoise,observedFeature,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem observedFeature_gram {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y)
    (i j : Fin n) {M : ℕ} (u v : EuclideanSpace ℝ (Fin M)) :
    inner ℝ (observedFeature t y i u) (observedFeature t y j v)=
      overlap t y i j*inner ℝ u v := by
  simp only [observedFeature,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Fintype.sum_sigma]
  rw [← values_gram t hy0 hym i j,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The full finite vector-observation Gaussian law follows from the exact
hierarchical overlap kernel, including the initial common variance. -/
theorem vector_observation_law_eq {depth n : ℕ} (t : NestedPartition depth n)
    {y : Fin (depth+1)→ℝ} (hy0 : 0≤y 0) (hym : Monotone y) {M : ℕ}
    {I : Type*} [Fintype I] (replica : I→Fin n) (u : I→EuclideanSpace ℝ (Fin M))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (F : I→E→L[ℝ]ℝ)
    (hGram : ∀a b,inner ℝ ((F a).adjoint 1) ((F b).adjoint 1)=
      overlap t y (replica a) (replica b)*inner ℝ (u a) (u b)) :
    (stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M))).map
      (fun g a => inner ℝ (u a) (vectorReplicaField t y M g (replica a)))=
      (stdGaussian E).map (fun g a => F a g) := by
  simp_rw [observed_field]
  apply RetainedCountProofs.GaussianFiniteFeatures.feature_law_eq
    (fun a => innerSL ℝ (observedFeature t y (replica a) (u a))) F
  intro a b
  simpa only [ContinuousLinearMap.adjoint_innerSL_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
    (observedFeature_gram t hy0 hym (replica a) (replica b) (u a) (u b)).trans (hGram a b).symm

theorem vector_mark_integrable {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (M : ℕ) {Z : EuclideanSpace ℝ (Fin M)→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (z : EuclideanSpace ℝ (Fin M)) :
    Integrable (fun g => ∏i : Fin n,Z (z+vectorReplicaField t y M g i))
      (stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M))) := by
  have hMP : MeasurePreserving (nodeNoise t M)
      (stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M)))
      (Measure.pi (fun _ : Coordinate t => stdGaussian (EuclideanSpace ℝ (Fin M)))) :=
    ⟨(nodeNoise_continuous t M).measurable,nodeNoise_law t M⟩
  exact hMP.integrable_comp_of_integrable (node_mark_integrable t y hZ ha hb z)

/-- Euclidean-bank Gaussian marks have the recursive marked moment, retaining the
outside common Gaussian.
-/
theorem vector_mark_eq_root_treeMoment {depth n : ℕ} (t : NestedPartition depth n)
    (y : Fin (depth+1)→ℝ) (M : ℕ) {Z : EuclideanSpace ℝ (Fin M)→ℝ}
    (hZ : Measurable Z) {a : ℝ} (ha : 0≤a) (hb : ∀z,0≤Z z ∧ Z z≤a)
    (z : EuclideanSpace ℝ (Fin M)) :
    (∫g,∏i : Fin n,Z (z+vectorReplicaField t y M g i)
      ∂stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M)))=
      ∫g : EuclideanSpace ℝ (Fin M),treeMoment depth n
        (fun j : Fin depth => Real.sqrt (y j.succ-y j.castSucc) •ContinuousLinearMap.id ℝ _)
        Z (z+Real.sqrt (y 0) •g) t ∂stdGaussian (EuclideanSpace ℝ (Fin M)) := by
  have hm : AEStronglyMeasurable
      (fun noise : Coordinate t→EuclideanSpace ℝ (Fin M) => ∏i : Fin n,Z (z+nodeField t y noise i))
      ((stdGaussian (EuclideanSpace ℝ (Σc : Coordinate t,Fin M))).map (nodeNoise t M)) := by
    rw [nodeNoise_law]
    exact (node_mark_measurable t y hZ z).aestronglyMeasurable
  have H := integral_map (nodeNoise_continuous t M).measurable.aemeasurable hm
  rw [nodeNoise_law] at H
  exact H.symm.trans (node_mark_eq_root_treeMoment t y hZ ha hb z)

end
end TensorPCA.NonRSLowerProofs.FiniteNestedGaussianVectorLaw
