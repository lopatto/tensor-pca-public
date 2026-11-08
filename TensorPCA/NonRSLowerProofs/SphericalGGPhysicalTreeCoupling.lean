-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGExtractedTreeExpectation
public import TensorPCA.NonRSLowerProofs.FiniteCavityTreeMomentApproximation
public import TensorPCA.NonRSLowerProofs.SphericalGGCylinderGramRounding

/-! Bounded physical products couple to the full selected tree PMFs. The fixed grid and
node-law modulus control pointwise Gram error. Two exceptional-event masses enter
the bound, each once.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.SphericalGGPhysicalTreeCoupling
open MeasureTheory ProbabilityTheory Set Filter
open NonRSUpperProofs.GaussianReplicaKernel NonRSUpperProofs.SphericalPositivePerturbation
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteGGPositiveGrid
open FiniteCavityGramMarkContinuity FiniteCavityTreeMomentApproximation
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteNestedGaussianVectorLaw
open SphericalGGTreeExtraction SphericalGGWeightObservable SphericalGGExtractedTreeExpectation
open SphericalGGCylinderGramRounding
open scoped BigOperators RealInnerProductSpace
noncomputable section
universe u

private theorem integral_product_mem_unit {G I : Type*} [MeasurableSpace G] [Fintype I]
    (mu : Measure G) [IsProbabilityMeasure mu] (f : I → G → ℝ)
    (hf : ∀ i g,f i g∈Icc (0 : ℝ) 1) : (∫ g,∏ i,f i g ∂mu)∈Icc (0 : ℝ) 1 := by
  have hNon (g : G) : 0≤∏ i,f i g := Finset.prod_nonneg (fun i _ ↦ (hf i g).1)
  have hB (g : G) : ‖∏ i,f i g‖≤1 := by
    rw [Real.norm_of_nonneg (hNon g)]
    exact Finset.prod_le_one₀ (fun i _ ↦ (hf i g).1) (fun i _ ↦ (hf i g).2)
  have H := norm_integral_le_of_norm_le_const (μ := mu) (f := fun g ↦ ∏ i,f i g)
    (C := 1) (Eventually.of_forall hB)
  simp only [probReal_univ,mul_one,one_mul,Real.norm_eq_abs] at H
  exact ⟨integral_nonneg hNon,(le_abs_self _).trans H⟩

private theorem actual_product_test_properties {N r : ℕ} {G W : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace W]
    (mu : Measure G) [IsProbabilityMeasure mu] (F : Model.Vector N → G → W)
    (hF : Continuous (fun p : Model.Vector N×G ↦ F p.1 p.2))
    (mark : W → ℝ) (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) :
    Measurable (fun old : Fin (r+1) → UnitSpin N ↦ ∫ g,∏ i,mark (F (old i).val g) ∂mu) ∧
    ∀ old : Fin (r+1) → UnitSpin N,(∫ g,∏ i,mark (F (old i).val g) ∂mu)∈Icc (0 : ℝ) 1 := by
  have hJoint : Continuous (fun p : (Fin (r+1) → UnitSpin N)×G ↦ ∏ i,mark (F (p.1 i).val p.2)) := by
    apply continuous_finsetProd Finset.univ
    intro i _
    exact hMark.comp (hF.comp
      ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).prodMk continuous_snd))
  refine ⟨hJoint.stronglyMeasurable.integral_prod_right'.measurable,?_⟩
  intro old
  exact integral_product_mem_unit mu (fun i g ↦ mark (F (old i).val g)) (fun _ _ ↦ hBound _)

private theorem negative_array_measurable (N r : ℕ) (neg : ℝ) :
    MeasurableSet {old : Fin (r+1) → UnitSpin N | ∃ i j,inner ℝ (old i).val (old j).val≤-neg} := by
  have hR (i j : Fin (r+1)) : Measurable (fun old : Fin (r+1) → UnitSpin N ↦ inner ℝ (old i).val (old j).val) :=
    ((continuous_subtype_val.comp (continuous_apply i)).inner (continuous_subtype_val.comp (continuous_apply j))).measurable
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun i ↦ MeasurableSet.iUnion (fun j ↦ measurableSet_le (hR i j) measurable_const))

theorem exists_selected_numerator_coupling (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : Model.Vector M → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {A : Type u} [Fintype A] {N K depth : ℕ},0<depth →
      ∀ (cuts : A → Fin depth → ℝ) (hcuts : ∀ a,Monotone (cuts a)),
      (∀ a l,cuts a l∈Ioo (cutLeft depth l) (cutRight depth l))→
      ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : 0≤v),
      ∀ (S : A → Set (Fin K → ℝ)),(∀ a,MeasurableSet (S a))→
      (∀ a b,a≠b→Disjoint (S a) (S b))→(⋃ a,S a)=univ→
      ∀ (neg : ℝ),0≤neg → neg+1/(depth : ℝ)≤delta →
      letI := parameterizedGibbsKernel_markov (K := K) nu hv
      let T := fun t : NestedPartition depth (r+1) ↦
        ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M),
          ∏ i : Fin (r+1),mark (vectorReplicaField t (fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) ((grid depth) l)) M g i)
          ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M))
      |(∫ q,(∫ g : CavityDisorder N M k,∏ i : Fin (r+1),mark (blockField k mu beta g (q.2 i).val)
          ∂stdGaussian (CavityDisorder N M k)) ∂jointLaw (K := K) nu v r)-
        (∑ a,∫ x,(S a).indicator (fun x ↦ ∑ t,(treePMF (cuts a) (hcuts a)
          (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
            ((parameterizedGibbsKernel nu v).sectR x) (r+1)) t).toReal*T t) x ∂positiveCubeLaw K)|≤
        eps+(jointLaw (K := K) nu v r).real {q | ∃ a,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2}+
          (jointLaw (K := K) nu v r).real {q | ∃ i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg} := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_physical_numerator_tree_moment_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro A hA N K depth hd cuts hcuts hCuts nu hnu v hv S hS hDis hCover neg hNeg hMesh
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let F := fun old : Fin (r+1) → UnitSpin N ↦
    ∫ g : CavityDisorder N M k,∏ i,mark (blockField k mu beta g (old i).val) ∂stdGaussian (CavityDisorder N M k)
  let T := fun t : NestedPartition depth (r+1) ↦
    ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M),∏ i : Fin (r+1),
      mark (vectorReplicaField t (fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) ((grid depth) l)) M g i)
      ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M))
  obtain ⟨hFM,hFB⟩ := actual_product_test_properties (r := r) (stdGaussian (CavityDisorder N M k))
    (fun x g ↦ blockField k mu beta g x) (blockField_joint_continuous N M k mu beta) mark hMark hBound
  have hTB (t : NestedPartition depth (r+1)) : T t∈Icc (0 : ℝ) 1 :=
    integral_product_mem_unit _ _ (fun _ _ ↦ hBound _)
  apply selected_tree_expectation_error nu hv r cuts hcuts S hS hDis hCover F hFM hFB T hTB
    (negative_array_measurable N r neg) heps.le
  intro a old hGood hNotNeg
  have hLower (i j : Fin (r+1)) : -neg ≤ inner ℝ (old i).val (old j).val := by
    by_contra h
    exact hNotNeg ⟨i,j,(lt_of_not_ge h).le⟩
  have hCylinder := treeCylinder_extractTree_of_good (cuts a) (hcuts a) old hGood
  have hClose (i j : Fin (r+1)) :
      |inner ℝ (old i).val (old j).val-overlap (extractTree (cuts a) (hcuts a) old) (grid depth) i j|≤delta :=
    (cylinder_grid_overlap_error hd (cuts a) (hCuts a) _ old hCylinder hNeg hLower i j).trans hMesh
  exact (hMain (grid depth) (by rw [grid_zero]) (grid_monotone hd) (grid_last hd)
    (extractTree (cuts a) (hcuts a) old) old hClose).le

theorem exists_selected_compensator_coupling (r M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (mark : ℝ → ℝ)
    (hMark : Continuous mark) (hBound : ∀ w,mark w∈Icc (0 : ℝ) 1) {eps : ℝ} (heps : 0<eps) :
    ∃ delta : ℝ,0<delta ∧ ∀ {A : Type u} [Fintype A] {N K depth : ℕ},0<N → 0<depth →
      ∀ (cuts : A → Fin depth → ℝ) (hcuts : ∀ a,Monotone (cuts a)),
      (∀ a l,cuts a l∈Ioo (cutLeft depth l) (cutRight depth l))→
      ∀ (nu : Measure (UnitSpin N)) [IsProbabilityMeasure nu] (v : ℝ) (hv : 0≤v),
      ∀ (S : A → Set (Fin K → ℝ)),(∀ a,MeasurableSet (S a))→
      (∀ a b,a≠b→Disjoint (S a) (S b))→(⋃ a,S a)=univ→
      ∀ (neg : ℝ),0≤neg → neg+1/(depth : ℝ)≤delta →
      letI := parameterizedGibbsKernel_markov (K := K) nu hv
      let T := fun t : NestedPartition depth (r+1) ↦
        ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1),
          ∏ i : Fin (r+1),mark (Real.sqrt (M : ℝ)*(vectorReplicaField t
            (fun l ↦ beta^2*((grid depth) l*deriv (Scalar.xiSlice k mu) ((grid depth) l)-
              Scalar.xiSlice k mu ((grid depth) l))) 1 g i) 0)
          ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1))
      |(∫ q,(∫ g : GroundState.Disorder N k,∏ i : Fin (r+1),mark (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (q.2 i).val) g)
          ∂stdGaussian (GroundState.Disorder N k)) ∂jointLaw (K := K) nu v r)-
        (∑ a,∫ x,(S a).indicator (fun x ↦ ∑ t,(treePMF (cuts a) (hcuts a)
          (law (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
            ((parameterizedGibbsKernel nu v).sectR x) (r+1)) t).toReal*T t) x ∂positiveCubeLaw K)|≤
        eps+(jointLaw (K := K) nu v r).real {q | ∃ a,q.1.1∈S a ∧ ¬thresholdGood (cuts a) q.2}+
          (jointLaw (K := K) nu v r).real {q | ∃ i j : Fin (r+1),inner ℝ (q.2 i).val (q.2 j).val≤-neg} := by
  obtain ⟨delta,hDelta,hMain⟩ := exists_physical_compensator_tree_moment_modulus r M k hmu beta mark hMark hBound heps
  refine ⟨delta,hDelta,?_⟩
  intro A hA N K depth hN hd cuts hcuts hCuts nu hnu v hv S hS hDis hCover neg hNeg hMesh
  letI := parameterizedGibbsKernel_markov (K := K) nu hv
  dsimp only
  let F := fun old : Fin (r+1) → UnitSpin N ↦
    ∫ g : GroundState.Disorder N k,∏ i,mark (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) (old i).val) g)
      ∂stdGaussian (GroundState.Disorder N k)
  let T := fun t : NestedPartition depth (r+1) ↦
    ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1),∏ i : Fin (r+1),
      mark (Real.sqrt (M : ℝ)*(vectorReplicaField t
        (fun l ↦ beta^2*((grid depth) l*deriv (Scalar.xiSlice k mu) ((grid depth) l)-
          Scalar.xiSlice k mu ((grid depth) l))) 1 g i) 0)
      ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1))
  obtain ⟨hFM,hFB⟩ := actual_product_test_properties (r := r) (stdGaussian (GroundState.Disorder N k))
    (fun x g ↦ inner ℝ (limitingCompensatorFeature M (fun j : Fin k ↦ (j : ℕ)+1)
      (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) g)
    (limitingCompensatorField_joint_continuous N M k mu beta) mark hMark hBound
  have hTB (t : NestedPartition depth (r+1)) : T t∈Icc (0 : ℝ) 1 :=
    integral_product_mem_unit _ _ (fun _ _ ↦ hBound _)
  apply selected_tree_expectation_error nu hv r cuts hcuts S hS hDis hCover F hFM hFB T hTB
    (negative_array_measurable N r neg) heps.le
  intro a old hGood hNotNeg
  have hLower (i j : Fin (r+1)) : -neg ≤ inner ℝ (old i).val (old j).val := by
    by_contra h
    exact hNotNeg ⟨i,j,(lt_of_not_ge h).le⟩
  have hCylinder := treeCylinder_extractTree_of_good (cuts a) (hcuts a) old hGood
  have hClose (i j : Fin (r+1)) :
      |inner ℝ (old i).val (old j).val-overlap (extractTree (cuts a) (hcuts a) old) (grid depth) i j|≤delta :=
    (cylinder_grid_overlap_error hd (cuts a) (hCuts a) _ old hCylinder hNeg hLower i j).trans hMesh
  exact (hMain hN (grid depth) (by rw [grid_zero]) (grid_monotone hd) (grid_last hd)
    (extractTree (cuts a) (hcuts a) old) old hClose).le

end
end TensorPCA.NonRSLowerProofs.SphericalGGPhysicalTreeCoupling
