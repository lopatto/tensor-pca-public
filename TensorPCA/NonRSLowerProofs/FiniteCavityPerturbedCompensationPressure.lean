-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationFactorization
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison

/-! Exact compensation of the physical field with the same independent
perturbation bank retained on both sides. No perturbation compensator or
perturbation error is introduced. -/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationPressure
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison GaussianFeatureIncrementComparison
open FiniteCavityGaussianCompatibility FiniteCavityCompensationJointPressure
open FiniteCavityPerturbedFields FiniteCavityPerturbedCompensationFactorization
open FiniteCavityCompensationThetaComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Actual
variable {N M k K : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1)
    (beta v : ℝ) (a : Fin K→ℝ)
local notation "bF" => perturbedBulkFeature N M k K mu beta v a
local notation "sF" => perturbedSliceFeature N k K mu beta v a
local notation "eF" => compensatorFeature (N := N) M (fun p : Fin k ↦ (p : ℕ)+1)
  (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "tF" => limitingCompensatorFeature (N := N) M (fun p : Fin k ↦ (p : ℕ)+1)
  (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
include hN hM hmu

 theorem joined_perturbed_compensation_gram (x y : Model.Vector N) :
    inner ℝ (sumJoin (bF x,eF x)) (sumJoin (bF y,eF y))=inner ℝ (sF x) (sF y) := by
  rw [sumJoin_inner,perturbedBulkFeature,perturbedBulkFeature,sumJoin_inner,
    perturbedSliceFeature,perturbedSliceFeature,sumJoin_inner]
  have H := joined_compensation_gram (k := k) hN hM hmu beta x y
  rw [sumJoin_inner] at H
  linarith only [H]

 theorem expected_full_eq_joined_bulk_compensator :
    (∫g,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (sF x)) g
      ∂stdGaussian (PerturbedDisorder N k K))=
    ∫g,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (sumJoin (bF x,eF x))) g
      ∂stdGaussian (EuclideanSpace ℝ (PerturbedCoordinate N k K⊕GroundState.Coordinate N k)) := by
  let j := fun x ↦ sumJoin (bF x,eF x)
  have hb := perturbedBulkFeature_continuous N M k K mu beta v a
  have he := compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hs := perturbedSliceFeature_continuous N k K mu beta v a
  have hj : Continuous j := sumJoin.continuous.comp (hb.prodMk he)
  obtain ⟨Ks,hKs,hbs⟩ := sphere_feature_bound hN sF hs
  obtain ⟨Kj,hKj,hbj⟩ := sphere_feature_bound hN j hj
  have H := expected_logPartition_abs_sub_le (Model.spherePrior N) sF j hs.measurable hj.measurable
    hKs hKj hbs hbj (ddiag := 0) (dpair := 0)
    (.of_forall fun x ↦ by
      dsimp only [j]
      rw [joined_perturbed_compensation_gram hN hM hmu beta v a x x]
      simp only [sub_self,abs_zero,le_refl])
    (.of_forall fun p ↦ by
      dsimp only [j]
      rw [joined_perturbed_compensation_gram hN hM hmu beta v a p.1 p.2]
      simp only [sub_self,abs_zero,le_refl])
  exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa only [zero_add,zero_div] using H))

 theorem expected_full_minus_bulk_eq_exact_compensator :
    (∫g,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (sF x)) g
      ∂stdGaussian (PerturbedDisorder N k K))-
    (∫gB,logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v a) gB
      ∂stdGaussian (PerturbedDisorder N k K))=
    ∫gB,(∫gE,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x ↦ innerSL ℝ (eF x)) gE∂stdGaussian (GroundState.Disorder N k))
      ∂stdGaussian (PerturbedDisorder N k K) := by
  have H := expected_joined_minus_first_eq_increment hN bF eF
    (perturbedBulkFeature_continuous N M k K mu beta v a)
    (compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  rw [←expected_full_eq_joined_bulk_compensator hN hM hmu beta v a] at H
  exact H

 theorem perturbed_compensator_mean_le_theta (gB : PerturbedDisorder N k K) :
    (∫gE,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x ↦ innerSL ℝ (eF x)) gE∂stdGaussian (GroundState.Disorder N k))≤
    ∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x ↦ innerSL ℝ (tF x)) gT∂stdGaussian (GroundState.Disorder N k) := by
  letI := perturbedBulkGibbs_probability hN M k K mu beta v a gB
  have he := compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have ht := thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Ke,hKe,hbe⟩ := sphere_feature_bound hN eF he
  obtain ⟨Kt,hKt,hbt⟩ := sphere_feature_bound hN tF ht
  have hac := gibbsMeasure_absolutelyContinuous (Model.spherePrior N)
    (perturbedBulkLinear N M k K mu beta v a) gB
  exact expected_logPartition_le_of_increment_le (perturbedBulkGibbs N M k K mu beta v a gB)
    eF tF he.measurable ht.measurable hKe hKt (hac.ae_le hbe) (hac.ae_le hbt)
    (exact_theta_increment_norm hN hM hmu beta)

 theorem expected_full_minus_bulk_le_theta_increment :
    (∫g,logPartition (Model.spherePrior N) (fun x ↦ innerSL ℝ (sF x)) g
      ∂stdGaussian (PerturbedDisorder N k K))-
    (∫gB,logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v a) gB
      ∂stdGaussian (PerturbedDisorder N k K))≤
    ∫gB,(∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x ↦ innerSL ℝ (tF x)) gT∂stdGaussian (GroundState.Disorder N k))
      ∂stdGaussian (PerturbedDisorder N k K) := by
  rw [expected_full_minus_bulk_eq_exact_compensator hN hM hmu beta v a]
  have hb := perturbedBulkFeature_continuous N M k K mu beta v a
  have he := compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have ht := thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hEI := feature_increment_joint_integrable hN bF eF hb he
  have hTI := feature_increment_joint_integrable hN bF tF hb ht
  apply integral_mono_ae hEI.integral_prod_left hTI.integral_prod_left
  exact .of_forall (perturbed_compensator_mean_le_theta hN hM hmu beta v a)
end Actual

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedCompensationPressure
