-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressure
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorMoments

/-! The retained ideal pressure dominates the spherical cavity mark. All Gaussian
product transport and logarithmic integrability are proved here; the two outside
radial restriction masses are unchanged.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressureSpherical
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityPerturbedIdealPressure FiniteCavityNumeratorMoments
open FiniteCavityPerturbedFields FiniteCavityPerturbedReferenceComparison FiniteCavityUnitPriorShellLower
open FiniteCavityRetainedPrior FiniteCavityReferenceGramBounds FiniteCavityIdealField
open FiniteCavityGaussianCompatibility FiniteCavityShellGibbsPartition
open FiniteCavityCompensationJointPressure GaussianFeatureCovarianceComparison
open GaussianCompactFeatureComparison FiniteCavityShellLinearPartition
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem spherical_cavity_feature_bound {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (q : Measure (Model.Vector N)) [IsFiniteMeasure q]
    (hq : ∀ᵐ x∂q,‖x‖=1) :
    ∀ᵐ p : Model.Vector N×Model.Vector M∂q.prod (Model.spherePrior M),
      ‖cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1‖≤
        Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
  have hx : ∀ᵐ p : Model.Vector N×Model.Vector M∂q.prod (Model.spherePrior M),‖p.1‖=1 :=
    Measure.quasiMeasurePreserving_fst.ae hq
  have hu : ∀ᵐ p : Model.Vector N×Model.Vector M∂q.prod (Model.spherePrior M),‖p.2‖=1 :=
    Measure.quasiMeasurePreserving_snd.ae (Geometry.spherePrior_norm_ae hM)
  filter_upwards [hx,hu] with p hx hu
  rw [cavityFeature_norm k hmu beta _ hx,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one]

private theorem spherical_cavity_measurable (N M k : ℕ) (mu beta : ℝ) :
    Measurable (fun p : Model.Vector N×Model.Vector M =>
      cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1) := by
  exact ((cavityFeature_joint_continuous N M k mu beta).comp
    (continuous_fst.prodMk (continuous_snd.const_smul (Real.sqrt (M : ℝ))))).measurable

private theorem spherical_cavity_joint_integrable {N M K : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (amp : Fin K→ℝ)
    (gB : PerturbedDisorder N k K) (gZ : CavityDisorder N M k) :
    Integrable (fun p : Model.Vector N×Model.Vector M =>
      Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1) gZ))
      ((perturbedBulkGibbs N M k K mu beta v amp gB).prod (Model.spherePrior M)) := by
  letI := perturbedBulkGibbs_probability hN M k K mu beta v amp gB
  have hb := spherical_cavity_feature_bound hM k hmu beta (perturbedBulkGibbs N M k K mu beta v amp gB)
    (perturbedBulkGibbs_unit_ae hN M k K mu beta v amp gB)
  have hL := (innerSL ℝ).continuous.measurable.comp (spherical_cavity_measurable N M k mu beta)
  have hbb : ∀ᵐ p∂(perturbedBulkGibbs N M k K mu beta v amp gB).prod (Model.spherePrior M),
      |(1 : ℝ)|≤1 ∧ ‖innerSL ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1)‖≤
        Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1) := by
    filter_upwards [hb] with p hp
    exact ⟨by norm_num,by simpa only [innerSL_apply_norm] using hp⟩
  have H := weight_integrable ((perturbedBulkGibbs N M k K mu beta v amp gB).prod (Model.spherePrior M))
    (fun _ => (1 : ℝ)) (fun p => innerSL ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1))
    measurable_const hL hbb gZ
  apply H.congr
  exact .of_forall fun p => by simp only [GaussianSpinInterpolation.weight,one_mul,innerSL_apply_apply]

section Actual
variable {N M k K : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (amp : Fin K→ℝ)
local notation "a" => perturbedBulkFeature N M k K mu beta v amp
include hN hM hmu

theorem spherical_mark_bulkGibbs_integrable (gB : PerturbedDisorder N k K) (gZ : CavityDisorder N M k) :
    Integrable (fun x => numeratorMark k mu beta gZ x) (perturbedBulkGibbs N M k K mu beta v amp gB) :=
  (spherical_cavity_joint_integrable hN hM k hmu beta v amp gB gZ).integral_prod_left

theorem spherical_mark_bulkGibbs_one_le (gB : PerturbedDisorder N k K) (gZ : CavityDisorder N M k) :
    1≤∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v amp gB := by
  letI := perturbedBulkGibbs_probability hN M k K mu beta v amp gB
  have H := integral_mono_ae (integrable_const (1 : ℝ))
    (spherical_mark_bulkGibbs_integrable hN hM hmu beta v amp gB gZ)
    (.of_forall fun x => numeratorMark_one_le hM k mu beta gZ x)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem pointwise_spherical_log_factorization (gB : PerturbedDisorder N k K) (gZ : CavityDisorder N M k) :
    Real.log (∫p : Model.Vector N×Model.Vector M,
      Real.exp (inner ℝ (a p.1) gB+inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1) gZ)∂(Model.spherePrior N).prod (Model.spherePrior M))=
      logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB+
      Real.log (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v amp gB) := by
  letI := perturbedBulkGibbs_probability hN M k K mu beta v amp gB
  have ha := perturbedBulkFeature_continuous N M k K mu beta v amp
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a ha
  have hb := spherical_cavity_feature_bound hM k hmu beta (Model.spherePrior N) (Geometry.spherePrior_norm_ae hN)
  have H := FiniteCavityIdealRetainedPressure.joint_gibbs_log_factorization (Model.spherePrior N) (Model.spherePrior M)
    a (fun p : Model.Vector N×Model.Vector M => cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1) ha.measurable (spherical_cavity_measurable N M k mu beta) hKA (by positivity) hba hb gB gZ
  have hCI := spherical_cavity_joint_integrable hN hM k hmu beta v amp gB gZ
  have hSwap := integral_integral_swap (f := fun (x : Model.Vector N) (u : Model.Vector M) =>
    Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •u) x) gZ)) hCI
  change (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v amp gB)=_ at hSwap
  change _=logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB+
    Real.log (∫u,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •u) x) gZ)
      ∂perturbedBulkGibbs N M k K mu beta v amp gB)∂Model.spherePrior M) at H
  rw [← hSwap] at H
  exact H

private theorem spherical_joined_product :
    Integrable (fun p : PerturbedDisorder N k K×CavityDisorder N M k =>
      Real.log (∫z : Model.Vector N×Model.Vector M,Real.exp (inner ℝ (a z.1) p.1+inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •z.2) z.1) p.2)
        ∂(Model.spherePrior N).prod (Model.spherePrior M)))
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (CavityDisorder N M k))) := by
  have ha := perturbedBulkFeature_continuous N M k K mu beta v amp
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a ha
  exact (joined_logPartition_product_integrable_and_eq ((Model.spherePrior N).prod (Model.spherePrior M))
    (fun z => a z.1) (fun p : Model.Vector N×Model.Vector M => cavityFeature k mu beta (Real.sqrt (M : ℝ) •p.2) p.1) (ha.measurable.comp measurable_fst) (spherical_cavity_measurable N M k mu beta)
    hKA (by positivity) (Measure.quasiMeasurePreserving_fst.ae hba)
    (spherical_cavity_feature_bound hM k hmu beta (Model.spherePrior N) (Geometry.spherePrior_norm_ae hN))).1

theorem spherical_increment_joint_integrable :
    Integrable (fun p : PerturbedDisorder N k K×CavityDisorder N M k =>
      Real.log (∫x,numeratorMark k mu beta p.2 x∂perturbedBulkGibbs N M k K mu beta v amp p.1))
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (CavityDisorder N M k))) := by
  have hP := spherical_joined_product (k := k) hN hM hmu beta v amp
  have ha := perturbedBulkFeature_continuous N M k K mu beta v amp
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a ha
  have hB : Integrable (logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp))
      (stdGaussian (PerturbedDisorder N k K)) := feature_logPartition_integrable _ _ ha.measurable hKA hba
  have hBP : Integrable (fun p : PerturbedDisorder N k K×CavityDisorder N M k =>
      logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) p.1)
      ((stdGaussian (PerturbedDisorder N k K)).prod (stdGaussian (CavityDisorder N M k))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p => by
    have H := pointwise_spherical_log_factorization hN hM hmu beta v amp p.1 p.2
    dsimp only [Pi.sub_apply]
    linarith only [H]

theorem expected_ideal_retained_ge_bulk_add_spherical_increment {e delta : ℝ}
    (he : 0<e) (hdelta : 0<delta) :
    (∫gB,logPartition (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v amp) gB∂stdGaussian (PerturbedDisorder N k K))+
      (∫gB,(∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v amp gB)
        ∂stdGaussian (CavityDisorder N M k))∂stdGaussian (PerturbedDisorder N k K))≤
    ∫g,logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealPerturbedReferenceFeature N M k K mu beta v amp z)) g
      ∂stdGaussian (EuclideanSpace ℝ (PerturbedCoordinate N k K⊕IdealCoordinate N M k)) := by
  rw [expected_ideal_retained_eq_bulk_add_conditional_increment hN hM hmu he hdelta beta v amp]
  apply add_le_add le_rfl
  have hS := spherical_increment_joint_integrable (k := k) hN hM hmu beta v amp
  have hC := conditional_increment_joint_integrable (k := k) hN hM hmu he hdelta beta v amp
  rw [← integral_prod _ hS,← integral_prod _ hC]
  apply integral_mono_ae hS hC
  exact .of_forall fun p => by
    letI := perturbedBulkGibbs_probability hN M k K mu beta v amp p.1
    have H := conditional_annulus_partition_lower hM k hmu beta hdelta
      (perturbedBulkGibbs N M k K mu beta v amp p.1)
      (perturbedBulkGibbs_unit_ae hN M k K mu beta v amp p.1) p.2
    have hPos := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (spherical_mark_bulkGibbs_one_le hN hM hmu beta v amp p.1 p.2)
    exact Real.log_le_log hPos H

end Actual
end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedIdealPressureSpherical
