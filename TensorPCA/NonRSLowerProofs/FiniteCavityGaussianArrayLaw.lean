-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
public import TensorPCA.NonRSLowerProofs.FiniteCavityThetaCovariance
public import TensorPCA.RetainedCountProofs.GaussianFiniteFeatures

/-! Equal deterministic spin Gram matrices give equal joint laws of the Gaussian cavity
arrays. A single shared disorder vector drives all replicas.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityGaussianArrayLaw
open MeasureTheory ProbabilityTheory Set
open FiniteCavityIdealField FiniteCavityShellGibbsPartition FiniteCavityNumeratorMoments
open FiniteCavityGaussianCompatibility FiniteCavityThetaCovariance
open OneStepGaussianTiltEndpoint
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem blockField_coordinate {N M : ℕ} (k : ℕ) (mu beta : ℝ)
    (g : CavityDisorder N M k) (x : Model.Vector N) (j : Fin M) :
    inner ℝ (cavityFeature k mu beta (EuclideanSpace.single j 1) x) g=
      blockField k mu beta g x j := by
  rw [cavityFeature_score_eq,EuclideanSpace.inner_single_right]
  simp only [conj_trivial,one_mul]

theorem blockField_array_continuous {N M K : ℕ} (k : ℕ) (mu beta : ℝ)
    (s : Fin K→Model.Vector N) :
    Continuous (fun g : CavityDisorder N M k => fun i : Fin K => blockField k mu beta g (s i)) := by
  unfold blockField
  fun_prop

/-- This is equality of the full vector-field laws, not merely equality of
expected logarithms or separately chosen replica marginals. -/
theorem blockField_array_law_eq_of_gram {N N' M K : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (s : Fin K→Model.Vector N) (t : Fin K→Model.Vector N')
    (hGram : ∀i j,inner ℝ (s i) (s j)=inner ℝ (t i) (t j)) :
    (stdGaussian (CavityDisorder N M k)).map (fun g i => blockField k mu beta g (s i))=
      (stdGaussian (CavityDisorder N' M k)).map (fun g i => blockField k mu beta g (t i)) := by
  have H := RetainedCountProofs.GaussianFiniteFeatures.feature_law_eq
    (fun p : Fin K×Fin M => innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (s p.1)))
    (fun p : Fin K×Fin M => innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (t p.1)))
    (by
      intro p q
      simp only [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
      rw [cavityFeature_inner k hmu beta,cavityFeature_inner k hmu beta,hGram p.1 q.1])
  let group := fun a : Fin K×Fin M→ℝ => fun i : Fin K =>
    (WithLp.toLp 2 (fun j : Fin M => a (i,j)) : Model.Vector M)
  have hGroup : Measurable group := by dsimp only [group]; fun_prop
  have HM := congrArg (Measure.map group) H
  rw [Measure.map_map hGroup (by fun_prop),Measure.map_map hGroup (by fun_prop)] at HM
  have hLeft : group ∘(fun g : CavityDisorder N M k => fun p : Fin K×Fin M =>
      innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (s p.1)) g)=
      (fun g => fun i => blockField k mu beta g (s i)) := by
    funext g i
    apply PiLp.ext
    intro j
    exact blockField_coordinate k mu beta g (s i) j
  have hRight : group ∘(fun g : CavityDisorder N' M k => fun p : Fin K×Fin M =>
      innerSL ℝ (cavityFeature k mu beta (EuclideanSpace.single p.2 1) (t p.1)) g)=
      (fun g => fun i => blockField k mu beta g (t i)) := by
    funext g i
    apply PiLp.ext
    intro j
    exact blockField_coordinate k mu beta g (t i) j
  rw [hLeft,hRight] at HM
  exact HM

/-- The sqrt(M)-sphere numerator marks inherit the complete joint law.
-/
theorem numeratorMark_array_law_eq_of_gram {N N' M K : ℕ} (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (s : Fin K→Model.Vector N) (t : Fin K→Model.Vector N')
    (hGram : ∀i j,inner ℝ (s i) (s j)=inner ℝ (t i) (t j)) :
    (stdGaussian (CavityDisorder N M k)).map (fun g i => numeratorMark k mu beta g (s i))=
      (stdGaussian (CavityDisorder N' M k)).map (fun g i => numeratorMark k mu beta g (t i)) := by
  let marks := fun field : Fin K→Model.Vector M => fun i : Fin K => sphericalLaplace M (field i)
  have hMarks : Measurable marks := by
    apply measurable_pi_lambda
    intro i
    exact (sphericalLaplace_measurable M).comp (measurable_pi_apply i)
  have H := congrArg (Measure.map marks) (blockField_array_law_eq_of_gram k hmu beta s t hGram)
  rw [Measure.map_map hMarks (blockField_array_continuous k mu beta s).measurable,
    Measure.map_map hMarks (blockField_array_continuous k mu beta t).measurable] at H
  simpa only [Function.comp_def,marks,numeratorMark_eq_sphericalLaplace] using H

/-- The true limiting compensator is a scalar array with its full theta
kernel; its degree-one cancellation does not alter the numerator's xi'(0). -/
theorem compensator_array_law_eq_of_gram {N N' K : ℕ} (hN : 0<N) (hN' : 0<N')
    (M k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (s : Fin K→Model.Vector N) (t : Fin K→Model.Vector N')
    (hGram : ∀i j,inner ℝ (s i) (s j)=inner ℝ (t i) (t j)) :
    (stdGaussian (GroundState.Disorder N k)).map (fun g i =>
      inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) (s i)) g)=
      (stdGaussian (GroundState.Disorder N' k)).map (fun g i =>
        inner ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) (t i)) g) := by
  apply RetainedCountProofs.GaussianFiniteFeatures.feature_law_eq
    (fun i : Fin K => innerSL ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) (s i)))
    (fun i : Fin K => innerSL ℝ (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
      (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) (t i)))
  intro i j
  simp only [ContinuousLinearMap.adjoint_innerSL_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  rw [thetaFeature_inner hN M k hmu beta,thetaFeature_inner hN' M k hmu beta,hGram i j]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityGaussianArrayLaw
