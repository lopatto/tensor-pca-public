-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.SphericalGGPopulationMoments
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison

/-! Exact observed population deficit moments for the two cavity marks. Each product
uses one shared cavity Gaussian, averaged before the old-spin replica test. The
compensation feature already contains its M scaling.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityObservedPopulationMoments
open MeasureTheory ProbabilityTheory Set
open NonRSUpperProofs.SphericalPositivePerturbation
open SphericalGGWeightObservable SphericalGGPopulationMoments
open FiniteCavityBulkUnitSpinPrior FiniteCavityPerturbedFields
open FiniteCavityNumeratorMoments FiniteCavityShellGibbsPartition
open OneStepGaussianTiltEndpoint FiniteCavityGaussianCompatibility
open FiniteCavityCompensationThetaComparison GaussianCompactFeatureComparison
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The numerator population uses its upper-clipped spherical mark. The lower bound by
one removes the generic lower clipping.
-/
theorem numerator_population_moment_eq_jointLaw {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k K : ℕ) (mu beta : ℝ) {v : ℝ} (hv : 0≤v)
    (gB : GroundState.Disorder N k) (n : ℕ) {cap : ℝ} (hcap : 1≤cap) :
    letI := bulkPriorKernel_probability hN M k mu beta gB
    (∫amp,(∫gP,(∫gZ,(1-(∫x,min (numeratorMark k mu beta gZ x) cap
      ∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)))/cap)^(n+1)
      ∂stdGaussian (CavityDisorder N M k))
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      ∫q,(∫gZ,∏i : Fin (n+1),(1-min (sphericalLaplace M
        (blockField k mu beta gZ (q.2 i).val)) cap/cap)
        ∂stdGaussian (CavityDisorder N M k))
        ∂jointLaw (K := K) (bulkPriorKernel N M k mu beta gB) v n := by
  letI := bulkPriorKernel_probability hN M k mu beta gB
  have H := actual_bulk_clipped_population_moment_eq_jointLaw hN M k K mu beta hv gB
    (stdGaussian (CavityDisorder N M k)) n
    (Y := numeratorMark k mu beta) (numeratorMark_joint_measurable N M k mu beta)
    (b := 1) (by norm_num) le_rfl hcap
  have hMax (gZ : CavityDisorder N M k) (x : Model.Vector N) :
      max 1 (min (numeratorMark k mu beta gZ x) cap)=
        min (numeratorMark k mu beta gZ x) cap :=
    max_eq_right (le_min (numeratorMark_one_le hM k mu beta gZ x) hcap)
  simp_rw [hMax] at H
  simpa only [numeratorMark_eq_sphericalLaplace] using H

/-- The denominator population uses the full theta Gaussian mark, with both
cutoffs retained. No lower bound by one is imposed on this exponential. -/
theorem compensation_population_moment_eq_jointLaw {N : ℕ} (hN : 0<N)
    (M k K : ℕ) (mu beta : ℝ) {v : ℝ} (hv : 0≤v)
    (gB : GroundState.Disorder N k) (n : ℕ) {b cap : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hcap : 1≤cap) :
    letI := bulkPriorKernel_probability hN M k mu beta gB
    (∫amp,(∫gP,(∫gT,(1-(∫x,max b (min (Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x) gT)) cap)
      ∂perturbedBulkGibbs N M k K mu beta v amp (sumJoin (gB,gP)))/cap)^(n+1)
      ∂stdGaussian (GroundState.Disorder N k))
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      ∫q,(∫gT,∏i : Fin (n+1),(1-max b (min (Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
          (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) (q.2 i).val) gT)) cap)/cap)
        ∂stdGaussian (GroundState.Disorder N k))
        ∂jointLaw (K := K) (bulkPriorKernel N M k mu beta gB) v n := by
  letI := bulkPriorKernel_probability hN M k mu beta gB
  have hF := (thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable
  have hY : Measurable (fun p : GroundState.Disorder N k×Model.Vector N => Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun p : Fin k => p.val+1)
        (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) p.2) p.1)) :=
    (continuous_inner.measurable.comp ((hF.comp measurable_snd).prodMk measurable_fst)).exp
  exact actual_bulk_clipped_population_moment_eq_jointLaw hN M k K mu beta hv gB
    (stdGaussian (GroundState.Disorder N k)) n hY hb hb1 hcap

end
end TensorPCA.NonRSLowerProofs.FiniteCavityObservedPopulationMoments
