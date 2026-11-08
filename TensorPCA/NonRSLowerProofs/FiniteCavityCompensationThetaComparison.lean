-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.GaussianFeatureIncrementComparison
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationGibbsIncrement

/-! Compensator domination by the full limiting theta field under the bulk Gibbs prior.
The covariance difference is a positive-semidefinite feature Gram; its individual
entries may have either sign.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation GaussianNestedGibbsProofs
open FiniteCavityGaussianCompatibility FiniteCavityCompensator FiniteCavityCompensationJointPressure
open FiniteCavityCompensationGibbsIncrement FiniteCavityShellGibbsPartition
open GaussianFeatureCovarianceComparison GaussianFeatureIncrementComparison
open scoped RealInnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def remainderFeature {N : ℕ} (M k : ℕ) (mu beta : ℝ) (x : Model.Vector N) : GroundState.Disorder N k :=
  Real.sqrt ((M : ℝ)/(N : ℝ)) • NonRSUpperProofs.FiniteTensorMixtureMaximum.feature
    (fun p : Fin k => (p : ℕ)+1)
    (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p*
      ((p : ℝ)-degreeCompensator N M ((p : ℕ)+1))) x

section Actual
variable {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
local notation "eF" => compensatorFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "tF" => limitingCompensatorFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "bF" => bulkFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)

theorem thetaFeature_continuous : Continuous tF := by
  unfold limitingCompensatorFeature
  exact (continuous_const : Continuous (fun _ : Model.Vector N => Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
    (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)

include hN hM hmu

theorem remainderFeature_inner (x y : Model.Vector N) :
    inner ℝ (remainderFeature M k mu beta x) (remainderFeature M k mu beta y)=
      inner ℝ (tF x) (tF y)-inner ℝ (eF x) (eF y) := by
  have hc (p : Fin k) : 0≤beta^2*VariationalProofs.sliceCoefficient k mu p :=
    mul_nonneg (sq_nonneg beta) (VariationalProofs.sliceCoefficient_nonneg k hmu p)
  have hgap (p : Fin k) : 0≤(p : ℝ)-degreeCompensator N M ((p : ℕ)+1) := by
    simpa only [Nat.add_sub_cancel] using (degreeCompensator_error N ((p : ℕ)+1) hM (by omega)).1
  rw [remainderFeature,remainderFeature,real_inner_smul_left,real_inner_smul_right,
    NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_inner _ _ (fun p => mul_nonneg (hc p) (hgap p)),
    limitingCompensatorFeature_inner M hN _ _ hc,compensatorFeature_inner hN hM _ _ hc]
  have hs := Real.sq_sqrt (show 0≤(M : ℝ)/(N : ℝ) by positivity)
  have hn : (N : ℝ)≠0 := by positivity
  calc
    _ = (Real.sqrt ((M : ℝ)/(N : ℝ)))^2*(N : ℝ)*
        (∑p : Fin k,beta^2*VariationalProofs.sliceCoefficient k mu p*
          ((p : ℝ)-degreeCompensator N M ((p : ℕ)+1))*(inner ℝ x y)^((p : ℕ)+1)) := by ring
    _ = (M : ℝ)*(∑p : Fin k,beta^2*VariationalProofs.sliceCoefficient k mu p*
          ((p : ℝ)-degreeCompensator N M ((p : ℕ)+1))*(inner ℝ x y)^((p : ℕ)+1)) := by rw [hs]; field_simp
    _ = _ := by
      simp only [Finset.mul_sum,Nat.add_sub_cancel]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring

theorem exact_theta_increment_norm (x y : Model.Vector N) : ‖eF x-eF y‖≤‖tF x-tF y‖ := by
  have hdist : ‖tF x-tF y‖^2=‖eF x-eF y‖^2+‖remainderFeature M k mu beta x-remainderFeature M k mu beta y‖^2 := by
    rw [norm_sub_sq_real,norm_sub_sq_real,norm_sub_sq_real]
    simp only [← real_inner_self_eq_norm_sq]
    rw [remainderFeature_inner hN hM hmu beta x x,remainderFeature_inner hN hM hmu beta y y,
      remainderFeature_inner hN hM hmu beta x y]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  nlinarith only [hdist,sq_nonneg ‖remainderFeature M k mu beta x-remainderFeature M k mu beta y‖]

theorem exact_compensator_mean_le_theta (gB : GroundState.Disorder N k) :
    (∫gE,logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (eF x)) gE
      ∂stdGaussian (GroundState.Disorder N k))≤
      ∫gT,logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (tF x)) gT
        ∂stdGaussian (GroundState.Disorder N k) := by
  letI := bulkGibbs_probability hN M k mu beta gB
  have he := FiniteCavityCompensationJointPressure.compensatorFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have ht := thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Ke,hKe,hbe⟩ := sphere_feature_bound hN eF he
  obtain ⟨Kt,hKt,hbt⟩ := sphere_feature_bound hN tF ht
  have hac := gibbsMeasure_absolutelyContinuous (Model.spherePrior N) (bulkLinear N M k mu beta) gB
  exact expected_logPartition_le_of_increment_le (bulkGibbs N M k mu beta gB) eF tF he.measurable ht.measurable
    hKe hKt (hac.ae_le hbe) (hac.ae_le hbt) (exact_theta_increment_norm hN hM hmu beta)

omit hM hmu in
theorem theta_log_factorization (gB gT : GroundState.Disorder N k) :
    Real.log (∫x,Real.exp (inner ℝ (bF x) gB+inner ℝ (tF x) gT)∂Model.spherePrior N)=
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB+
        logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (tF x)) gT := by
  have hb := FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have ht := thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN bF hb
  obtain ⟨Kt,hKt,hbt⟩ := sphere_feature_bound hN tF ht
  have hLb := (bulkLinear_continuous N M k mu beta).measurable
  have hLt : Measurable (fun x => innerSL ℝ (tF x)) := (innerSL ℝ).continuous.measurable.comp ht.measurable
  have hbb' : ∀ᵐ x∂Model.spherePrior N,‖bulkLinear N M k mu beta x‖≤Kb := by
    filter_upwards [hbb] with x hx
    simpa only [bulkLinear,innerSL_apply_norm] using hx
  have hbt' : ∀ᵐ x∂Model.spherePrior N,‖innerSL ℝ (tF x)‖≤Kt :=
    hbt.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx)
  have hZ := moment_one_pos (Model.spherePrior N) (bulkLinear N M k mu beta) hLb hbb' gB
  have hS := shiftedSpinMoment_one_pos (Model.spherePrior N) (fun x => innerSL ℝ (tF x))
    (bulkLinear N M k mu beta) hLt hLb (hbt'.and hbb') gT gB
  have hShift : shiftedSpinMoment (Model.spherePrior N) (fun _ => 1) (fun x => innerSL ℝ (tF x))
      (bulkLinear N M k mu beta) gT gB=
      ∫x,Real.exp (inner ℝ (bF x) gB+inner ℝ (tF x) gT)∂Model.spherePrior N := by
    unfold shiftedSpinMoment GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun x => by
      simp only [one_mul,innerSL_apply_apply,bulkLinear,Real.exp_add]
      ring
  change Real.log (∫x,Real.exp (inner ℝ (bF x) gB+inner ℝ (tF x) gT)∂Model.spherePrior N)=
    Real.log (GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ => 1) (bulkLinear N M k mu beta) gB)+
      Real.log (GaussianSpinInterpolation.moment (bulkGibbs N M k mu beta gB) (fun _ => 1) (fun x => innerSL ℝ (tF x)) gT)
  rw [bulkGibbs,moment_gibbs_shift_eq (Model.spherePrior N) (fun _ => 1) (fun x => innerSL ℝ (tF x))
    (bulkLinear N M k mu beta) hLb hbb',Real.log_div hS.ne' hZ.ne',hShift]
  ring

omit hM hmu in
theorem theta_increment_joint_integrable :
    Integrable (fun p : GroundState.Disorder N k×GroundState.Disorder N k =>
      logPartition (bulkGibbs N M k mu beta p.1) (fun x => innerSL ℝ (tF x)) p.2)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) := by
  have hb := FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  have ht := thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta
  obtain ⟨Kb,hKb,hbb⟩ := sphere_feature_bound hN bF hb
  obtain ⟨Kt,hKt,hbt⟩ := sphere_feature_bound hN tF ht
  have hP := (joined_logPartition_product_integrable_and_eq (Model.spherePrior N) bF tF hb.measurable ht.measurable
    hKb hKt hbb hbt).1
  have hB : Integrable (logPartition (Model.spherePrior N) (bulkLinear N M k mu beta))
      (stdGaussian (GroundState.Disorder N k)) := feature_logPartition_integrable (Model.spherePrior N) bF hb.measurable hKb hbb
  have hBP : Integrable (fun p : GroundState.Disorder N k×GroundState.Disorder N k =>
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (GroundState.Disorder N k))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p => by
    dsimp only [Pi.sub_apply]
    have H := theta_log_factorization (M := M) (mu := mu) hN beta p.1 p.2
    linarith only [H]

theorem expected_full_minus_bulk_le_theta_increment :
    (∫g,logPartition (Model.spherePrior N) (fun x => innerSL ℝ (beta • GroundState.sliceFeature k mu x)) g
        ∂stdGaussian (GroundState.Disorder N k))-
      (∫gB,logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB∂stdGaussian (GroundState.Disorder N k))≤
      ∫gB,(∫gT,logPartition (bulkGibbs N M k mu beta gB) (fun x => innerSL ℝ (tF x)) gT
        ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (GroundState.Disorder N k) := by
  rw [expected_full_minus_bulk_eq_compensator_increment hN mu beta hM hmu]
  apply integral_mono_ae
    (compensator_increment_joint_integrable (M := M) (k := k) hN mu beta).integral_prod_left
    (theta_increment_joint_integrable (M := M) (k := k) (mu := mu) hN beta).integral_prod_left
  exact .of_forall (exact_compensator_mean_le_theta hN hM hmu beta)

end Actual


end
end TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison
