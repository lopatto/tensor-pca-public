-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityGaussianArrayLaw
public import TensorPCA.NonRSLowerProofs.FiniteNestedGaussianVectorLaw

/-! Physical derivative-covariance and theta arrays on a finite tree have the
independent node-noise Gaussian laws. The numerator retains its initial xi'(q0)
variance; compensation uses the full M beta^2 theta kernel.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityTreeGaussianLaw
open MeasureTheory ProbabilityTheory Set
open FiniteNestedPartition FiniteNestedPartitionOverlap FiniteNestedGaussianFeature
open FiniteNestedGaussianVectorLaw FiniteNestedGaussianNodeMarking
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteCavityThetaCovariance FiniteCavityGaussianArrayLaw
open NonRSSphericalGroundTrialTransportProofs NonRSUpperProofs.SphericalParisiLabeledCovariance
open scoped BigOperators RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem derivative_heights_admissible {depth : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) :
    0≤beta^2*deriv (Scalar.xiSlice k mu) (q 0) ∧
      Monotone (fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)) := by
  have hc (p : Fin k) : 0≤VariationalProofs.sliceCoefficient k mu p :=
    VariationalProofs.sliceCoefficient_nonneg k hmu p
  have hq (i : Fin (depth+1)) : 0≤q i := hq0.trans (hqm (Fin.zero_le i))
  constructor
  · rw [← source_xi1_eq_deriv_xiSlice k mu]
    exact mul_nonneg (sq_nonneg beta) (xi1_nonnegative _ _ hc hq0)
  · intro i j hij
    rw [← source_xi1_eq_deriv_xiSlice k mu]
    exact mul_le_mul_of_nonneg_left (xi1_monotone_positive _ _ hc (hq i) (hqm hij)) (sq_nonneg beta)

theorem theta_heights_admissible {depth : ℕ} (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) :
    0≤(M : ℝ)*beta^2*(q 0*deriv (Scalar.xiSlice k mu) (q 0)-Scalar.xiSlice k mu (q 0)) ∧
      Monotone (fun l ↦ (M : ℝ)*beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))) := by
  have hc (p : Fin k) : 0≤VariationalProofs.sliceCoefficient k mu p :=
    VariationalProofs.sliceCoefficient_nonneg k hmu p
  have hd (p : Fin k) : 1≤p.val+1 := by omega
  have hq (i : Fin (depth+1)) : 0≤q i := hq0.trans (hqm (Fin.zero_le i))
  have hFactor : 0≤(M : ℝ)*beta^2 := mul_nonneg (Nat.cast_nonneg M) (sq_nonneg beta)
  constructor
  · have H := theta_eq_positive_polynomial (fun p : Fin k ↦ p.val+1)
      (VariationalProofs.sliceCoefficient k mu) hd (q 0)
    rw [theta,source_xi1_eq_deriv_xiSlice,source_xi_eq_xiSlice] at H
    rw [H]
    exact mul_nonneg hFactor (Finset.sum_nonneg (fun p _ ↦
      mul_nonneg (mul_nonneg (hc p) (Nat.cast_nonneg _)) (pow_nonneg hq0 _)))
  · intro i j hij
    have H := theta_monotone_positive (fun p : Fin k ↦ p.val+1)
      (VariationalProofs.sliceCoefficient k mu) hc hd (hq i) (hqm hij)
    simp only [theta,source_xi1_eq_deriv_xiSlice,source_xi_eq_xiSlice] at H
    exact mul_le_mul_of_nonneg_left H hFactor

theorem blockField_tree_array_law {N M depth n : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) (t : NestedPartition depth n)
    (s : Fin n → Model.Vector N) (hGram : ∀ i j,inner ℝ (s i) (s j)=overlap t q i j) :
    let y := fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)
    (stdGaussian (CavityDisorder N M k)).map (fun g i ↦ blockField k mu beta g (s i))=
      (stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M))).map
        (vectorReplicaField t y M) := by
  dsimp only
  let y := fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)
  obtain ⟨hy0,hym⟩ := derivative_heights_admissible k hmu beta q hq0 hqm
  have H := vector_observation_law_eq (y := y) t hy0 hym
    (fun p : Fin n×Fin M ↦ p.1) (fun p ↦ EuclideanSpace.single p.2 1)
    (fun p : Fin n×Fin M ↦ innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (s p.1))) (by
      intro p z
      simp only [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
      rw [cavityFeature_inner k hmu beta,hGram p.1 z.1]
      change inner ℝ (EuclideanSpace.single p.2 1) (EuclideanSpace.single z.2 1)*beta^2*
        deriv (Scalar.xiSlice k mu) (overlap t q p.1 z.1)=
        (beta^2*deriv (Scalar.xiSlice k mu) (overlap t q p.1 z.1))*
          inner ℝ (EuclideanSpace.single p.2 1) (EuclideanSpace.single z.2 1)
      ring)
  let group := fun a : Fin n×Fin M → ℝ ↦ fun i : Fin n ↦
    (WithLp.toLp 2 (fun j : Fin M ↦ a (i,j)) : Model.Vector M)
  have hGroup : Measurable group := by dsimp only [group]; fun_prop
  have hNode : Continuous (vectorReplicaField t y M) := by
    apply continuous_pi
    intro i
    exact (nodeField_continuous t y i).comp (nodeNoise_continuous t M)
  have HM := congrArg (Measure.map group) H
  rw [Measure.map_map hGroup (by fun_prop),Measure.map_map hGroup (by fun_prop)] at HM
  have hLeft : group ∘ (fun g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M) ↦
      fun p : Fin n×Fin M ↦ inner ℝ (EuclideanSpace.single p.2 1) (vectorReplicaField t y M g p.1))=
      vectorReplicaField t y M := by
    funext g i
    apply PiLp.ext
    intro j
    simp only [group,Function.comp_def,EuclideanSpace.inner_single_left,conj_trivial,one_mul]
  have hRight : group ∘ (fun g : CavityDisorder N M k ↦ fun p : Fin n×Fin M ↦
      innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (s p.1)) g)=
      (fun g i ↦ blockField k mu beta g (s i)) := by
    funext g i
    apply PiLp.ext
    intro j
    exact blockField_coordinate k mu beta g (s i) j
  rw [hLeft,hRight] at HM
  exact HM.symm

theorem compensator_tree_array_law {N depth n : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) (t : NestedPartition depth n)
    (s : Fin n → Model.Vector N) (hGram : ∀ i j,inner ℝ (s i) (s j)=overlap t q i j) :
    let z := fun l ↦ beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))
    (stdGaussian (GroundState.Disorder N k)).map (fun g i ↦ inner ℝ
      (limitingCompensatorFeature M (fun p : Fin k ↦ p.val+1)
        (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p) (s i)) g)=
      (stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1))).map
        (fun g i ↦ Real.sqrt (M : ℝ)*(vectorReplicaField t z 1 g i) 0) := by
  dsimp only
  let z := fun l ↦ beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))
  obtain ⟨hz0,hzm⟩ := theta_heights_admissible 1 k hmu beta q hq0 hqm
  simp only [Nat.cast_one,one_mul] at hz0 hzm
  have H := vector_observation_law_eq (y := z) t hz0 hzm
    (fun i : Fin n ↦ i) (fun _ ↦ EuclideanSpace.single (0 : Fin 1) (Real.sqrt (M : ℝ)))
    (fun i ↦ innerSL ℝ (limitingCompensatorFeature M (fun p : Fin k ↦ p.val+1)
      (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p) (s i))) (by
      intro i j
      simp only [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
      rw [thetaFeature_inner hN M k hmu beta,hGram i j]
      simp only [EuclideanSpace.inner_single_left,PiLp.single_apply,conj_trivial,if_pos rfl]
      change (M : ℝ)*beta^2*(overlap t q i j*deriv (Scalar.xiSlice k mu) (overlap t q i j)-
        Scalar.xiSlice k mu (overlap t q i j))=
          (beta^2*(overlap t q i j*deriv (Scalar.xiSlice k mu) (overlap t q i j)-
            Scalar.xiSlice k mu (overlap t q i j)))*(Real.sqrt (M : ℝ)*Real.sqrt (M : ℝ))
      rw [← pow_two,Real.sq_sqrt (Nat.cast_nonneg M)]
      ring)
  simpa only [innerSL_apply_apply,EuclideanSpace.inner_single_left,conj_trivial] using H.symm

theorem blockField_tree_mark_product {N M depth n : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) (t : NestedPartition depth n)
    (s : Fin n → Model.Vector N) (hGram : ∀ i j,inner ℝ (s i) (s j)=overlap t q i j)
    (mark : Model.Vector M → ℝ) (hMark : Continuous mark) :
    let y := fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)
    (∫ g : CavityDisorder N M k,∏ i : Fin n,mark (blockField k mu beta g (s i))
      ∂stdGaussian (CavityDisorder N M k))=
      ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M),
        ∏ i : Fin n,mark (vectorReplicaField t y M g i)
        ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin M)) := by
  dsimp only
  let y := fun l ↦ beta^2*deriv (Scalar.xiSlice k mu) (q l)
  have hLaw := blockField_tree_array_law (M := M) k hmu beta q hq0 hqm t s hGram
  have hTest : Measurable (fun f : Fin n → Model.Vector M ↦ ∏ i,mark (f i)) :=
    (continuous_finsetProd Finset.univ (fun i _ ↦ hMark.comp (continuous_apply i))).measurable
  have hNode : Measurable (vectorReplicaField t y M) := by
    apply measurable_pi_lambda
    intro i
    exact ((nodeField_continuous t y i).comp (nodeNoise_continuous t M)).measurable
  have H := congrArg (fun rho ↦ ∫ f : Fin n → Model.Vector M,∏ i,mark (f i) ∂rho) hLaw
  rw [integral_map (blockField_array_continuous k mu beta s).measurable.aemeasurable hTest.aestronglyMeasurable,
    integral_map hNode.aemeasurable hTest.aestronglyMeasurable] at H
  exact H

theorem compensator_tree_mark_product {N depth n : ℕ} (hN : 0<N) (M k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Fin (depth+1) → ℝ)
    (hq0 : 0≤q 0) (hqm : Monotone q) (t : NestedPartition depth n)
    (s : Fin n → Model.Vector N) (hGram : ∀ i j,inner ℝ (s i) (s j)=overlap t q i j)
    (mark : ℝ → ℝ) (hMark : Continuous mark) :
    let z := fun l ↦ beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))
    (∫ g : GroundState.Disorder N k,∏ i : Fin n,mark (inner ℝ
      (limitingCompensatorFeature M (fun p : Fin k ↦ p.val+1)
        (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p) (s i)) g)
      ∂stdGaussian (GroundState.Disorder N k))=
      ∫ g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1),
        ∏ i : Fin n,mark (Real.sqrt (M : ℝ)*(vectorReplicaField t z 1 g i) 0)
        ∂stdGaussian (EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1)) := by
  dsimp only
  let z := fun l ↦ beta^2*(q l*deriv (Scalar.xiSlice k mu) (q l)-Scalar.xiSlice k mu (q l))
  have hLaw := compensator_tree_array_law hN M k hmu beta q hq0 hqm t s hGram
  have hTest : Measurable (fun f : Fin n → ℝ ↦ ∏ i,mark (f i)) :=
    (continuous_finsetProd Finset.univ (fun i _ ↦ hMark.comp (continuous_apply i))).measurable
  have hLeft : Measurable (fun g : GroundState.Disorder N k ↦ fun i : Fin n ↦ inner ℝ
      (limitingCompensatorFeature M (fun p : Fin k ↦ p.val+1)
        (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p) (s i)) g) := by fun_prop
  have hNode : Measurable (fun g : EuclideanSpace ℝ (Σc : FiniteNestedGaussianFeature.Coordinate t,Fin 1) ↦
      fun i : Fin n ↦ Real.sqrt (M : ℝ)*(vectorReplicaField t z 1 g i) 0) := by
    apply measurable_pi_lambda
    intro i
    exact (((PiLp.continuous_apply 2 _ (0 : Fin 1)).comp
      ((nodeField_continuous t z i).comp (nodeNoise_continuous t 1))).const_mul (Real.sqrt (M : ℝ))).measurable
  have H := congrArg (fun rho ↦ ∫ f : Fin n → ℝ,∏ i,mark (f i) ∂rho) hLaw
  rw [integral_map hLeft.aemeasurable hTest.aestronglyMeasurable,
    integral_map hNode.aemeasurable hTest.aestronglyMeasurable] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteCavityTreeGaussianLaw
