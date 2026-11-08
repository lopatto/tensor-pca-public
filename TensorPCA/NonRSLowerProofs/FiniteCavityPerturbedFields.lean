-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbationReference
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGramBounds
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceRestriction
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition

/-! Independent physical and finite-cutoff perturbation banks. The same perturbation
feature is retained in the N-dimensional bulk prior.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison FiniteCavityGaussianCompatibility
open FiniteCavityReferenceGramBounds FiniteCavityReferenceRestriction FiniteCavityPerturbationReference
open FiniteCavityCompensationJointPressure FiniteCavityShellGibbsPartition
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev PerturbedCoordinate (N k K : ℕ) := GroundState.Coordinate N k⊕TensorCoordinate N K
abbrev PerturbedDisorder (N k K : ℕ) := EuclideanSpace ℝ (PerturbedCoordinate N k K)

def perturbedSliceFeature (N k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (x : Model.Vector N) : PerturbedDisorder N k K :=
  sumJoin (beta • GroundState.sliceFeature k mu x,feature (coefficients v a) x)

def perturbedBulkFeature (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (x : Model.Vector N) : PerturbedDisorder N k K :=
  sumJoin (bulkFeature M (fun p : Fin k => (p : ℕ)+1)
    (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x,feature (coefficients v a) x)

def perturbedBulkLinear (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (x : Model.Vector N) : PerturbedDisorder N k K→L[ℝ] ℝ :=
  innerSL ℝ (perturbedBulkFeature N M k K mu beta v a x)

def perturbedBulkGibbs (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (g : PerturbedDisorder N k K) : Measure (Model.Vector N) :=
  gibbsMeasure (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v a) g

theorem perturbedSliceFeature_continuous (N k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) :
    Continuous (perturbedSliceFeature N k K mu beta v a) :=
  sumJoin.continuous.comp (((GroundUpperProofs.continuous_sliceFeature N k mu).const_smul beta).prodMk
    (feature_continuous (coefficients v a)))

theorem perturbedBulkFeature_continuous (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) :
    Continuous (perturbedBulkFeature N M k K mu beta v a) :=
  sumJoin.continuous.comp ((FiniteCavityCompensationJointPressure.bulkFeature_continuous
    (N := N) (M := M) (k := k) (mu := mu) beta).prodMk (feature_continuous (coefficients v a)))

theorem perturbedBulkLinear_measurable (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ) :
    Measurable (perturbedBulkLinear N M k K mu beta v a) :=
  (innerSL ℝ).continuous.measurable.comp (perturbedBulkFeature_continuous N M k K mu beta v a).measurable

theorem joined_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (a : EuclideanSpace ℝ I) (b : EuclideanSpace ℝ J) : ‖sumJoin (a,b)‖≤‖a‖+‖b‖ := by
  have hs : ‖sumJoin (a,b)‖^2=‖a‖^2+‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq,sumJoin_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  nlinarith only [hs,norm_nonneg (sumJoin (a,b)),norm_nonneg a,norm_nonneg b,
    mul_nonneg (norm_nonneg a) (norm_nonneg b)]

theorem perturbedSliceFeature_unit_bound {N k K : ℕ} {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2)
    {x : Model.Vector N} (hx : ‖x‖=1) :
    ‖perturbedSliceFeature N k K mu beta v a x‖≤|beta| *Real.sqrt (N : ℝ)+2*|v| :=
  (joined_norm_le _ _).trans (add_le_add (thermal_sliceFeature_unit_bound hmu beta hx)
    (perturbationFeature_unit_norm_le v a ha hx))

theorem perturbedBulkFeature_unit_bound {N M k K : ℕ} (hM : 0<M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (a : Fin K→ℝ) (ha : ∀p,|a p|≤2)
    {x : Model.Vector N} (hx : ‖x‖=1) :
    ‖perturbedBulkFeature N M k K mu beta v a x‖≤
      Real.sqrt (((N : ℝ)+M)*beta^2*Scalar.xiSlice k mu ((N : ℝ)/((N : ℝ)+M)))+2*|v| := by
  apply (joined_norm_le _ _).trans
  rw [bulkFeature_norm_on_unit hM k hmu beta hx]
  exact add_le_add le_rfl (perturbationFeature_unit_norm_le v a ha hx)

theorem perturbedBulkGibbs_probability {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (a : Fin K→ℝ) (g : PerturbedDisorder N k K) :
    IsProbabilityMeasure (perturbedBulkGibbs N M k K mu beta v a g) := by
  obtain ⟨B,hB,hb⟩ := sphere_feature_bound hN (perturbedBulkFeature N M k K mu beta v a)
    (perturbedBulkFeature_continuous N M k K mu beta v a)
  exact gibbsMeasure_probability (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v a)
    (perturbedBulkLinear_measurable N M k K mu beta v a)
    (hb.mono (fun x hx => by simpa only [perturbedBulkLinear,innerSL_apply_norm] using hx)) g

theorem perturbedBulkGibbs_unit_ae {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (a : Fin K→ℝ) (g : PerturbedDisorder N k K) :
    ∀ᵐ x∂perturbedBulkGibbs N M k K mu beta v a g,‖x‖=1 :=
  (gibbsMeasure_absolutelyContinuous (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v a) g).ae_le
    (Geometry.spherePrior_norm_ae hN)

theorem perturbedBulkLinear_sumJoin (N M k K : ℕ) (mu beta v : ℝ) (a : Fin K→ℝ)
    (x : Model.Vector N) (gB : GroundState.Disorder N k) (gP : PerturbationDisorder N K) :
    perturbedBulkLinear N M k K mu beta v a x (sumJoin (gB,gP))=
      bulkLinear N M k mu beta x gB+linear (coefficients v a) x gP := by
  unfold perturbedBulkLinear perturbedBulkFeature
  rw [innerSL_apply_apply,sumJoin_inner]
  rfl

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
