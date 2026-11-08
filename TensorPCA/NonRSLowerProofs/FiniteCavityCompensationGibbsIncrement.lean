-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition
public import TensorPCA.GaussianNestedGibbsProofs

/-! Exact compensator increment under the bulk Gibbs probability. The independent
product law and full pressure restoration are already proved; logarithmic
factorization and disorder integrability are proved here.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensationGibbsIncrement
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation GaussianNestedGibbsProofs
open FiniteCavityGaussianCompatibility FiniteCavityCompensationJointPressure
open FiniteCavityShellGibbsPartition GaussianFeatureCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Actual
variable {N M k : ℕ} (hN : 0<N) (mu beta : ℝ)
local notation "a" => bulkFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "b" => compensatorFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
include hN

theorem pointwise_bulk_compensator_log_factorization (gB gE : GroundState.Disorder N k) :
    Real.log (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (b x) gE)∂Model.spherePrior N)=
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB+
        logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (b x)) gE := by
  have ha := FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hb := FiniteCavityCompensationJointPressure.compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hLa := (bulkLinear_continuous N M k mu beta).measurable
  have hLb : Measurable (fun x => innerSL ℝ (b x)) := (innerSL ℝ).continuous.measurable.comp hb.measurable
  have hba' : ∀ᵐ x∂Model.spherePrior N,‖bulkLinear N M k mu beta x‖≤Ka := by
    filter_upwards [hba] with x hx
    simpa only [bulkLinear,innerSL_apply_norm] using hx
  have hbb' : ∀ᵐ x∂Model.spherePrior N,‖innerSL ℝ (b x)‖≤Kb :=
    hbb.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx)
  have hZ := moment_one_pos (Model.spherePrior N) (bulkLinear N M k mu beta) hLa hba' gB
  have hS := shiftedSpinMoment_one_pos (Model.spherePrior N) (fun x => innerSL ℝ (b x))
    (bulkLinear N M k mu beta) hLb hLa
    (hbb'.and hba') gE gB
  have hShift : shiftedSpinMoment (Model.spherePrior N) (fun _ => 1) (fun x => innerSL ℝ (b x))
      (bulkLinear N M k mu beta) gE gB=
      ∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (b x) gE)∂Model.spherePrior N := by
    unfold shiftedSpinMoment GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun x => by
      simp only [one_mul,innerSL_apply_apply,bulkLinear,Real.exp_add]
      ring
  change Real.log (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (b x) gE)∂Model.spherePrior N)=
    Real.log (GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ => 1) (bulkLinear N M k mu beta) gB)+
      Real.log (GaussianSpinInterpolation.moment (bulkGibbs N M k mu beta gB) (fun _ => 1) (fun x => innerSL ℝ (b x)) gE)
  rw [bulkGibbs,moment_gibbs_shift_eq (Model.spherePrior N) (fun _ => 1) (fun x => innerSL ℝ (b x))
    (bulkLinear N M k mu beta) hLa hba',Real.log_div hS.ne' hZ.ne',hShift]
  ring

theorem compensator_increment_joint_integrable :
    Integrable (fun p : GroundState.Disorder N k×GroundState.Disorder N k =>
      logPartition (bulkGibbs N M k mu beta p.1) (fun x => innerSL ℝ (b x)) p.2)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) := by
  have ha := FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hb := FiniteCavityCompensationJointPressure.compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hP := (joined_logPartition_product_integrable_and_eq (Model.spherePrior N) a b ha.measurable hb.measurable
    hKa hKb hba hbb).1
  have hB : Integrable (logPartition (Model.spherePrior N) (bulkLinear N M k mu beta))
      (stdGaussian (GroundState.Disorder N k)) := feature_logPartition_integrable (Model.spherePrior N) a ha.measurable hKa hba
  have hBP : Integrable (fun p : GroundState.Disorder N k×GroundState.Disorder N k =>
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p => by
    dsimp only [Pi.sub_apply]
    have H := pointwise_bulk_compensator_log_factorization (M := M) hN mu beta p.1 p.2
    linarith only [H]

theorem expected_full_minus_bulk_eq_compensator_increment (hM : 0<M)
    (hmu : mu∈Icc (-1 : ℝ) 1) :
    (∫g,logPartition (Model.spherePrior N) (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
        ∂stdGaussian (GroundState.Disorder N k))-
      (∫gB,logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB∂stdGaussian (GroundState.Disorder N k))=
      ∫gB,(∫gE,logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (b x)) gE
        ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (GroundState.Disorder N k) := by
  have ha := FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have hb := FiniteCavityCompensationJointPressure.compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Ka,hKa,hba⟩ := sphere_feature_bound hN a ha
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN b hb
  have hP := (joined_logPartition_product_integrable_and_eq (Model.spherePrior N) a b ha.measurable hb.measurable
    hKa hKb hba hbb).1
  have hB : Integrable (logPartition (Model.spherePrior N) (bulkLinear N M k mu beta))
      (stdGaussian (GroundState.Disorder N k)) := feature_logPartition_integrable (Model.spherePrior N) a ha.measurable hKa hba
  have hBP : Integrable (fun p : GroundState.Disorder N k×GroundState.Disorder N k =>
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  have hI := compensator_increment_joint_integrable hN mu beta (M := M) (k := k)
  rw [expected_full_logPartition_eq_independent_bulk_compensator hN hM hmu beta,
    ← integral_prod _ hP]
  have hFactor : (∫p : GroundState.Disorder N k×GroundState.Disorder N k,
      Real.log (∫x,Real.exp (inner ℝ (a x) p.1+inner ℝ (b x) p.2)∂Model.spherePrior N)
      ∂(stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k)))=
      (∫p : GroundState.Disorder N k×GroundState.Disorder N k,
        logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1
        ∂(stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k)))+
      (∫p : GroundState.Disorder N k×GroundState.Disorder N k,
        logPartition (bulkGibbs N M k mu beta p.1) (fun x => innerSL ℝ (b x)) p.2
        ∂(stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) := by
    rw [← integral_add hBP hI]
    apply integral_congr_ae
    exact .of_forall fun p => pointwise_bulk_compensator_log_factorization (M := M) hN mu beta p.1 p.2
  rw [hFactor,integral_fun_fst,probReal_univ,one_smul,integral_prod _ hI]
  ring

end Actual


end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensationGibbsIncrement
