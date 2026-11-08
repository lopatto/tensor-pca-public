-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
public import TensorPCA.NonRSLowerProofs.FiniteCavityBulkUnitSpinPrior
public import TensorPCA.NonRSUpperProofs.GaussianGibbsAssociation

/-! The physical perturbed bulk prior is the same Gibbs tilt used by the intrinsic
finite-GG construction. All banks and normalizers are retained.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedGibbsTransport
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison FiniteCavityGaussianCompatibility
open FiniteCavityCompensationJointPressure FiniteCavityShellGibbsPartition
open FiniteCavityPerturbedFields FiniteCavityBulkUnitSpinPrior
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem perturbedBulkGibbs_sumJoin {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (a : Fin K→ℝ) (gB : GroundState.Disorder N k) (gP : PerturbationDisorder N K) :
    perturbedBulkGibbs N M k K mu beta v a (sumJoin (gB,gP))=
      gibbsMeasure (bulkGibbs N M k mu beta gB) (linear (coefficients v a)) gP := by
  let bF := bulkFeature (N := N) M (fun p : Fin k ↦ (p : ℕ)+1)
    (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
  obtain ⟨Cb,hCb,hb⟩ := sphere_feature_bound hN bF
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  obtain ⟨Ct,hCt,ht⟩ := sphere_feature_bound hN (perturbedBulkFeature N M k K mu beta v a)
    (perturbedBulkFeature_continuous N M k K mu beta v a)
  have hbL : ∀ᵐx ∂Model.spherePrior N,‖bulkLinear N M k mu beta x‖≤Cb := by
    filter_upwards [hb] with x hx
    simpa only [bulkLinear,bF,innerSL_apply_norm] using hx
  have htL : ∀ᵐx ∂Model.spherePrior N,‖perturbedBulkLinear N M k K mu beta v a x‖≤Ct := by
    filter_upwards [ht] with x hx
    simpa only [perturbedBulkLinear,innerSL_apply_norm] using hx
  unfold perturbedBulkGibbs bulkGibbs
  symm
  exact gibbsMeasure_associate (Model.spherePrior N) (bulkLinear N M k mu beta)
    (bulkLinear_continuous N M k mu beta).measurable hbL gB
    (linear (coefficients v a)) (linear_measurable _) gP
    (perturbedBulkLinear N M k K mu beta v a) (perturbedBulkLinear_measurable N M k K mu beta v a)
    htL (sumJoin (gB,gP)) (.of_forall (fun x ↦ perturbedBulkLinear_sumJoin N M k K mu beta v a x gB gP))

 theorem map_gibbs_bulkPriorKernel_eq_perturbedBulkGibbs {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (a : Fin K→ℝ) (gB : GroundState.Disorder N k) (gP : PerturbationDisorder N K) :
    (gibbsMeasure (bulkPriorKernel N M k mu beta gB)
      (fun z : UnitSpin N ↦ linear (coefficients v a) z.val) gP).map
      ((↑) : UnitSpin N→Model.Vector N)=perturbedBulkGibbs N M k K mu beta v a (sumJoin (gB,gP)) := by
  rw [map_gibbs_bulkPriorKernel hN M k mu beta gB _ (linear_measurable _) gP]
  exact (perturbedBulkGibbs_sumJoin hN M k K mu beta v a gB gP).symm

 theorem integral_gibbs_bulkPriorKernel_eq_perturbedBulkGibbs {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (a : Fin K→ℝ) (gB : GroundState.Disorder N k) (gP : PerturbationDisorder N K)
    (f : Model.Vector N→ℝ) :
    (∫z : UnitSpin N,f z.val ∂gibbsMeasure (bulkPriorKernel N M k mu beta gB)
      (fun z : UnitSpin N ↦ linear (coefficients v a) z.val) gP)=
      ∫x,f x ∂perturbedBulkGibbs N M k K mu beta v a (sumJoin (gB,gP)) := by
  rw [integral_gibbs_bulkPriorKernel hN M k mu beta gB _ (linear_measurable _) gP f,
    perturbedBulkGibbs_sumJoin hN M k K mu beta v a gB gP]

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedGibbsTransport
