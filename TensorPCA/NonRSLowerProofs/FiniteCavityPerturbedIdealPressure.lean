-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedReferenceComparison
public import TensorPCA.NonRSLowerProofs.FiniteCavityUnitPriorShellLower
public import TensorPCA.NonRSLowerProofs.FiniteCavityIdealRetainedPressure

/-! Retained ideal-pressure factorization for the perturbed bulk Gibbs prior, preserving
its independent finite perturbation bank.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressure
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityPerturbedFields FiniteCavityPerturbedReferenceComparison
open FiniteCavityReferenceLaw FiniteCavityRetainedMass FiniteCavityRetainedPrior
open FiniteCavityReferenceGramBounds FiniteCavityIdealField FiniteCavityShellLinearPartition
open FiniteCavityCompensationJointPressure GaussianFeatureCovarianceComparison
open GaussianCompactFeatureComparison FiniteCavityUnitPriorShellLower
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem retained_integral_ignoring_radius {N M : ℕ} (hN : 0<N) (hM : 0<M)
    {e delta : ℝ} (he : 0<e) (hdelta : 0<delta)
    (f : Model.Vector N×Model.Vector M→ℝ) (hf : AEStronglyMeasurable f
      ((Model.spherePrior N).prod (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)))) :
    (∫z,f (z.1,z.2.2)∂retainedPrior N M e delta)=
      ∫p,f p∂(Model.spherePrior N).prod
        (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)) := by
  have hR : (radiusLaw N) (radiusBox N e)≠0 := (ENNReal.toReal_pos_iff.mp (radiusBoxMass_pos hN he)).1.ne'
  letI := cond_isProbabilityMeasure hR
  have hp : MeasurePreserving (fun z : Model.Vector N×(ℝ×Model.Vector M) => (z.1,z.2.2))
      (retainedPrior N M e delta) ((Model.spherePrior N).prod
        (ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta))) :=
    (MeasurePreserving.id (Model.spherePrior N)).prod measurePreserving_snd
  exact hp.hasLaw.integral_comp hf

section Actual
variable {N M k K : ℕ} (hN : 0<N) (hM : 0<M) {mu e delta : ℝ}
  (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (hdelta : 0<delta) (beta v : ℝ) (amp : Fin K→ℝ)
local notation "a" => perturbedBulkFeature N M k K mu beta v amp
local notation "A" => ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)
include hN hmu hdelta

private theorem ideal_product_feature_bounds :
    ∃KA KB : ℝ,0≤KA ∧ 0≤KB ∧
      (∀ᵐ z∂(Model.spherePrior N).prod A,‖a z.1‖≤KA) ∧
      (∀ᵐ z∂(Model.spherePrior N).prod A,‖cavityFeature k mu beta z.2 z.1‖≤KB) := by
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (perturbedBulkFeature_continuous N M k K mu beta v amp)
  refine ⟨KA,Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1),hKA,by positivity,
    Measure.quasiMeasurePreserving_fst.ae hba,?_⟩
  have hx : ∀ᵐ z∂(Model.spherePrior N).prod A,‖z.1‖=1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hz : ∀ᵐ z∂(Model.spherePrior N).prod A,z.2∈gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (gaussianAnnulus_measurableSet M delta))
  filter_upwards [hx,hz] with z hx hz
  exact cavityFeature_norm_le k hmu beta (by positivity) z.2 hz.2 hx

private theorem full_product_integrable (gB : PerturbedDisorder N k K)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    Integrable (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)) ((Model.spherePrior N).prod A) := by
  obtain ⟨KA,KB,hKA,hKB,hba,hbb⟩ := ideal_product_feature_bounds hN hmu hdelta beta v amp
  have hc := (cavityFeature_joint_continuous N M k mu beta).comp (continuous_fst.prodMk continuous_snd)
  have ha : Continuous (fun p : Model.Vector N×Model.Vector M => a p.1) :=
    (perturbedBulkFeature_continuous N M k K mu beta v amp).comp continuous_fst
  have hs : Continuous (fun p : Model.Vector N×Model.Vector M =>
      inner ℝ (a p.1) gB+inner ℝ (cavityFeature k mu beta p.2 p.1) gZ) :=
    (ha.inner continuous_const).add (hc.inner continuous_const)
  apply Integrable.of_bound hs.rexp.aestronglyMeasurable (Real.exp (KA*‖gB‖+KB*‖gZ‖))
  filter_upwards [hba,hbb] with p hp hq
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  exact add_le_add ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg gB))))
    ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg gZ))))

include hM he

theorem retained_partition_eq_product (gB : PerturbedDisorder N k K)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    (∫z,Real.exp (inner ℝ (idealPerturbedReferenceFeature N M k K mu beta v amp z) (sumJoin (gB,gZ)))
      ∂retainedPrior N M e delta)=
    ∫p : Model.Vector N×Model.Vector M,Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)∂(Model.spherePrior N).prod A := by
  have H := retained_integral_ignoring_radius hN hM he hdelta
    (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ))
    (full_product_integrable hN hmu hdelta beta v amp gB gZ).aestronglyMeasurable
  convert H using 1
  apply integral_congr_ae
  exact .of_forall fun z => by
    change Real.exp (inner ℝ (sumJoin (a z.1,cavityFeature k mu beta z.2.2 z.1)) (sumJoin (gB,gZ)))=_
    rw [sumJoin_inner]

theorem pointwise_ideal_retained_log_factorization (gB : PerturbedDisorder N k K)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealPerturbedReferenceFeature N M k K mu beta v amp z))
      (sumJoin (gB,gZ))=
    logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB+
      Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
        ∂perturbedBulkGibbs N M k K mu beta v amp gB)∂A) := by
  have hAz : (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)≠0 :=
    (ENNReal.toReal_pos_iff.mp (annulusMass_pos hM hdelta)).1.ne'
  letI := cond_isProbabilityMeasure hAz
  letI := perturbedBulkGibbs_probability hN M k K mu beta v amp gB
  have hFI := full_product_integrable hN hmu hdelta beta v amp gB gZ
  have hCI := unit_prior_cavity_joint_integrable k hmu beta (by positivity : 0≤(M : ℝ)*(1+delta))
    (perturbedBulkGibbs N M k K mu beta v amp gB) (perturbedBulkGibbs_unit_ae hN M k K mu beta v amp gB) A
    ((ae_cond_mem (gaussianAnnulus_measurableSet M delta)).mono (fun eta heta => heta.2)) gZ
  have hCpos : 0<∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
      ∂perturbedBulkGibbs N M k K mu beta v amp gB)∂A := by
    rw [← integral_integral_swap (f := fun x eta => Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)) hCI,
      ← integral_prod _ hCI]
    exact integral_exp_pos hCI
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (perturbedBulkFeature_continuous N M k K mu beta v amp)
  have hLa := perturbedBulkLinear_measurable N M k K mu beta v amp
  have hbL : ∀ᵐ x∂Model.spherePrior N,‖perturbedBulkLinear N M k K mu beta v amp x‖≤KA :=
    hba.mono (fun x hx => by simpa only [perturbedBulkLinear,innerSL_apply_norm] using hx)
  let Z := GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ => 1) (perturbedBulkLinear N M k K mu beta v amp) gB
  have hZ : 0<Z := moment_one_pos _ _ hLa hbL gB
  have hEta (eta : Model.Vector M) :
      (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (cavityFeature k mu beta eta x) gZ)∂Model.spherePrior N)=
        Z*(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)∂perturbedBulkGibbs N M k K mu beta v amp gB) := by
    rw [perturbedBulkGibbs,integral_gibbsMeasure (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) hLa hbL]
    change _=Z*((∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)*
      Real.exp (perturbedBulkLinear N M k K mu beta v amp x gB)∂Model.spherePrior N)/Z)
    rw [mul_div_cancel₀ _ hZ.ne']
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [perturbedBulkLinear,innerSL_apply_apply,Real.exp_add]; ring
  have hPartition : (∫p : Model.Vector N×Model.Vector M,
      Real.exp (inner ℝ (a p.1) gB+inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)
      ∂(Model.spherePrior N).prod A)=
      Z*(∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
        ∂perturbedBulkGibbs N M k K mu beta v amp gB)∂A) := by
    rw [integral_prod _ hFI,integral_integral_swap hFI]
    simp_rw [hEta]
    rw [integral_const_mul]
  have H := congrArg Real.log ((retained_partition_eq_product hN hM hmu he hdelta beta v amp gB gZ).trans hPartition)
  rw [Real.log_mul hZ.ne' hCpos.ne'] at H
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,Z] using H


private theorem ideal_retained_component_bounds :
    ∃KA KB : ℝ,0≤KA ∧ 0≤KB ∧
      (∀ᵐ z∂retainedPrior N M e delta,‖a z.1‖≤KA) ∧
      (∀ᵐ z∂retainedPrior N M e delta,‖cavityFeature k mu beta z.2.2 z.1‖≤KB) := by
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (perturbedBulkFeature_continuous N M k K mu beta v amp)
  refine ⟨KA,Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1),hKA,by positivity,
    Measure.quasiMeasurePreserving_fst.ae hba,?_⟩
  filter_upwards [retainedPrior_support_ae hN e delta] with z hz
  exact cavityFeature_norm_le k hmu beta (by positivity) z.2.2 hz.2.2.2.2 hz.1

private theorem ideal_retained_joined_product :
    Integrable (fun p : PerturbedDisorder N k K×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      Real.log (∫z,Real.exp (inner ℝ (a z.1) p.1+inner ℝ (cavityFeature k mu beta z.2.2 z.1) p.2)
        ∂retainedPrior N M e delta))
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) ∧
    (∫g,logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealPerturbedReferenceFeature N M k K mu beta v amp z)) g
      ∂stdGaussian (EuclideanSpace ℝ (PerturbedCoordinate N k K⊕IdealCoordinate N M k)))=
    ∫gB,(∫gZ,Real.log (∫z,Real.exp (inner ℝ (a z.1) gB+inner ℝ (cavityFeature k mu beta z.2.2 z.1) gZ)
      ∂retainedPrior N M e delta)∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))
      ∂stdGaussian (PerturbedDisorder N k K) := by
  letI := retainedPrior_probability hN hM he hdelta
  obtain ⟨KA,KB,hKA,hKB,hba,hbb⟩ := ideal_retained_component_bounds hN hM hmu he hdelta beta v amp
  have ha := (perturbedBulkFeature_continuous N M k K mu beta v amp).comp
    (continuous_fst : Continuous (fun z : Model.Vector N×(ℝ×Model.Vector M) => z.1))
  have hb := (cavityFeature_joint_continuous N M k mu beta).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd) :
      Continuous (fun z : Model.Vector N×(ℝ×Model.Vector M) => (z.1,z.2.2)))
  exact joined_logPartition_product_integrable_and_eq (retainedPrior N M e delta)
    (fun z => a z.1) (fun z => cavityFeature k mu beta z.2.2 z.1) ha.measurable hb.measurable hKA hKB hba hbb

theorem conditional_increment_joint_integrable :
    Integrable (fun p : PerturbedDisorder N k K×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) p.2)
        ∂perturbedBulkGibbs N M k K mu beta v amp p.1)∂A))
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) := by
  have hP := (ideal_retained_joined_product (k := k) hN hM hmu he hdelta beta v amp).1
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (perturbedBulkFeature_continuous N M k K mu beta v amp)
  have hB : Integrable (logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp))
      (stdGaussian (PerturbedDisorder N k K)) := feature_logPartition_integrable _ _
    (perturbedBulkFeature_continuous N M k K mu beta v amp).measurable hKA hba
  have hBP : Integrable (fun p : PerturbedDisorder N k K×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) p.1)
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p => by
    have H := pointwise_ideal_retained_log_factorization hN hM hmu he hdelta beta v amp p.1 p.2
    simp only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,idealPerturbedReferenceFeature,sumJoin_inner] at H
    dsimp only [Pi.sub_apply]
    simp only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul]
    linarith only [H]

theorem expected_ideal_retained_eq_bulk_add_conditional_increment :
    (∫g,logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealPerturbedReferenceFeature N M k K mu beta v amp z)) g
      ∂stdGaussian (EuclideanSpace ℝ (PerturbedCoordinate N k K⊕IdealCoordinate N M k)))=
    (∫gB,logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB∂stdGaussian (PerturbedDisorder N k K))+
    ∫gB,(∫gZ,Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
      ∂perturbedBulkGibbs N M k K mu beta v amp gB)∂A)∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))
      ∂stdGaussian (PerturbedDisorder N k K) := by
  have hP := ideal_retained_joined_product (k := k) hN hM hmu he hdelta beta v amp
  have hI := conditional_increment_joint_integrable (k := k) hN hM hmu he hdelta beta v amp
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (perturbedBulkFeature_continuous N M k K mu beta v amp)
  have hB : Integrable (logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp))
      (stdGaussian (PerturbedDisorder N k K)) := feature_logPartition_integrable _ _
    (perturbedBulkFeature_continuous N M k K mu beta v amp).measurable hKA hba
  have hBP : Integrable (fun p : PerturbedDisorder N k K×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) p.1)
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  have hBI : (∫p : PerturbedDisorder N k K×EuclideanSpace ℝ (IdealCoordinate N M k),
      logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) p.1
      ∂(stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k))))=
      ∫gB,logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB∂stdGaussian (PerturbedDisorder N k K) := by
    rw [integral_fun_fst,probReal_univ,one_smul]
  rw [hP.2,← integral_prod _ hP.1,← integral_prod _ hI,← hBI,← integral_add hBP hI]
  apply integral_congr_ae
  exact .of_forall fun p => by
    have H := pointwise_ideal_retained_log_factorization hN hM hmu he hdelta beta v amp p.1 p.2
    simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,idealPerturbedReferenceFeature,sumJoin_inner] using H

end Actual

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressure
