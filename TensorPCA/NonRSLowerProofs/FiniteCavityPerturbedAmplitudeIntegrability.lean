-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedFields
public import TensorPCA.NonRSLowerProofs.FiniteCavityNumeratorIntegrability
public import TensorPCA.NonRSUpperProofs.SphericalPositiveParameterCube

/-! Amplitude measurability and integrability for the physical perturbed pressure and
its same-amplitude bulk cavity observables.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedAmplitudeIntegrability
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityPerturbedFields FiniteCavityIdealField FiniteCavityNumeratorMoments
open FiniteCavityCompensationJointPressure GaussianFeatureCovarianceComparison
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem norm_gaussian_integrable {I : Type*} [Fintype I] :
    Integrable (fun g : EuclideanSpace ℝ I => ‖g‖) (stdGaussian (EuclideanSpace ℝ I)) := by
  have H := GaussianSpinInterpolation.gaussian_norm_integrable (ι := I)
  rwa [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at H

theorem perturbationFeature_joint_continuous (N K : ℕ) (v : ℝ) :
    Continuous (fun p : (Fin K→ℝ)×Model.Vector N => feature (coefficients v p.1) p.2) := by
  unfold feature coefficients RetainedCountProofs.FiniteModel.tensorMonomial
  fun_prop

theorem perturbedSliceFeature_joint_continuous (N k K : ℕ) (mu beta v : ℝ) :
    Continuous (fun p : (Fin K→ℝ)×Model.Vector N => perturbedSliceFeature N k K mu beta v p.1 p.2) := by
  unfold perturbedSliceFeature
  exact GaussianCompactFeatureComparison.sumJoin.continuous.comp
    ((((GroundUpperProofs.continuous_sliceFeature N k mu).const_smul beta).comp continuous_snd).prodMk
      (perturbationFeature_joint_continuous N K v))

theorem perturbedBulkFeature_joint_continuous (N M k K : ℕ) (mu beta v : ℝ) :
    Continuous (fun p : (Fin K→ℝ)×Model.Vector N => perturbedBulkFeature N M k K mu beta v p.1 p.2) := by
  unfold perturbedBulkFeature
  exact GaussianCompactFeatureComparison.sumJoin.continuous.comp
    (((FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).comp continuous_snd).prodMk
      (perturbationFeature_joint_continuous N K v))

theorem slice_logPartition_joint_measurable (N k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun p : (Fin K→ℝ)×PerturbedDisorder N k K =>
      logPartition (Model.spherePrior N) (fun x => innerSL ℝ (perturbedSliceFeature N k K mu beta v p.1 x)) p.2) := by
  have hInput : Continuous (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×Model.Vector N => (p.1.1,p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hScore : Continuous (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×Model.Vector N =>
      inner ℝ (perturbedSliceFeature N k K mu beta v p.1.1 p.2) p.1.2) :=
    ((perturbedSliceFeature_joint_continuous N k K mu beta v).comp hInput).inner continuous_fst.snd
  have H := hScore.rexp.measurable.stronglyMeasurable.integral_prod_right' (ν := Model.spherePrior N)
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply] using H.measurable.log

theorem slice_expected_logPartition_measurable (N k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun a : Fin K→ℝ => ∫g,logPartition (Model.spherePrior N)
      (fun x => innerSL ℝ (perturbedSliceFeature N k K mu beta v a x)) g∂stdGaussian (PerturbedDisorder N k K)) :=
  (slice_logPartition_joint_measurable N k K mu beta v).stronglyMeasurable.integral_prod_right'.measurable

theorem slice_expected_logPartition_cube_integrable {N k K : ℕ} (hN : 0< N) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    Integrable (fun a : Fin K→ℝ => ∫g,logPartition (Model.spherePrior N)
      (fun x => innerSL ℝ (perturbedSliceFeature N k K mu beta v a x)) g∂stdGaussian (PerturbedDisorder N k K))
      (positiveCubeLaw K) := by
  let C := |beta| *Real.sqrt (N : ℝ)+2*|v|
  have hC : 0≤ C := by dsimp only [C]; positivity
  have hG := norm_gaussian_integrable (I := PerturbedCoordinate N k K)
  apply Integrable.of_bound (slice_expected_logPartition_measurable N k K mu beta v).aestronglyMeasurable
    (C*(∫g : PerturbedDisorder N k K,‖g‖∂stdGaussian (PerturbedDisorder N k K)))
  filter_upwards [positiveCubeLaw_abs_le_two K] with a ha
  rw [Real.norm_eq_abs]
  have hF := (perturbedSliceFeature_continuous N k K mu beta v a).measurable
  have hb : ∀ᵐ x∂Model.spherePrior N,‖perturbedSliceFeature N k K mu beta v a x‖≤ C :=
    (Geometry.spherePrior_norm_ae hN).mono (fun x hx => perturbedSliceFeature_unit_bound hmu beta v a ha hx)
  have hI := feature_logPartition_integrable (Model.spherePrior N) _ hF hC hb
  have hbL : ∀ᵐ x∂Model.spherePrior N,‖innerSL ℝ (perturbedSliceFeature N k K mu beta v a x)‖≤ C :=
    hb.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx)
  have H := integral_mono hI.abs (hG.const_mul C) (fun g => abs_logPartition_le _ _
    ((innerSL ℝ).continuous.measurable.comp hF) hbL g)
  rw [integral_const_mul] at H
  exact (abs_integral_le_integral_abs).trans H

/-- The Gibbs integral is jointly measurable in amplitude, bulk disorder, and an
arbitrary measurable observable parameter.
-/
theorem perturbedBulkGibbs_integral_joint_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ)
    (mu beta v : ℝ) {W : Type*} [MeasurableSpace W]
    (rho : W×Model.Vector N→ℝ) (hrho : Measurable rho) :
    Measurable (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×W =>
      ∫x,rho (p.2,x)∂perturbedBulkGibbs N M k K mu beta v p.1.1 p.1.2) := by
  have hInput : Continuous (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×Model.Vector N => (p.1.1,p.2)) :=
    continuous_fst.fst.prodMk continuous_snd
  have hScore : Continuous (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×Model.Vector N =>
      inner ℝ (perturbedBulkFeature N M k K mu beta v p.1.1 p.2) p.1.2) :=
    ((perturbedBulkFeature_joint_continuous N M k K mu beta v).comp hInput).inner continuous_fst.snd
  have hZ := hScore.rexp.measurable.stronglyMeasurable.integral_prod_right' (ν := Model.spherePrior N)
  have hDen : Measurable (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×W =>
      ∫x,Real.exp (inner ℝ (perturbedBulkFeature N M k K mu beta v p.1.1 x) p.1.2)∂Model.spherePrior N) :=
    hZ.measurable.comp measurable_fst
  have hRho := hrho.comp (measurable_fst.snd.prodMk measurable_snd :
    Measurable (fun p : (((Fin K→ℝ)×PerturbedDisorder N k K)×W)×Model.Vector N => (p.1.2,p.2)))
  have hExp := hScore.rexp.measurable.comp (measurable_fst.fst.prodMk measurable_snd :
    Measurable (fun p : (((Fin K→ℝ)×PerturbedDisorder N k K)×W)×Model.Vector N => (p.1.1,p.2)))
  have hNum := (hRho.mul hExp).stronglyMeasurable.integral_prod_right' (ν := Model.spherePrior N)
  have H := hNum.measurable.div hDen
  convert H using 1
  funext p
  obtain ⟨C,hC,hb⟩ := sphere_feature_bound hN (perturbedBulkFeature N M k K mu beta v p.1.1)
    (perturbedBulkFeature_continuous N M k K mu beta v p.1.1)
  have hbL : ∀ᵐ x∂Model.spherePrior N,‖perturbedBulkLinear N M k K mu beta v p.1.1 x‖≤ C :=
    hb.mono (fun x hx => by simpa only [perturbedBulkLinear,innerSL_apply_norm] using hx)
  rw [perturbedBulkGibbs,integral_gibbsMeasure (Model.spherePrior N) (perturbedBulkLinear N M k K mu beta v p.1.1)
    (perturbedBulkLinear_measurable N M k K mu beta v p.1.1) hbL]
  simp only [expectation,GaussianSpinInterpolation.moment,weight,one_mul,perturbedBulkLinear,innerSL_apply_apply,Function.comp_apply,Pi.mul_apply,Pi.div_apply]

private theorem probability_integral_abs_bound {V : Type*} [MeasurableSpace V] (nu : Measure V)
    [IsProbabilityMeasure nu] {F : V→ℝ} (hF : Measurable F) {C : ℝ} (hb : ∀x,|F x|≤ C) :
    Integrable F nu ∧ |∫x,F x∂nu|≤ C := by
  have hI : Integrable F nu := Integrable.of_bound hF.aestronglyMeasurable C
    (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  refine ⟨hI,?_⟩
  have H := integral_mono hI.abs (integrable_const C) hb
  simpa only [integral_const,probReal_univ,one_smul] using (abs_integral_le_integral_abs).trans H

theorem numerator_log_joint_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×CavityDisorder N M k =>
      Real.log (∫x,numeratorMark k mu beta p.2 x∂perturbedBulkGibbs N M k K mu beta v p.1.1 p.1.2)) :=
  (perturbedBulkGibbs_integral_joint_measurable hN M k K mu beta v
    (fun p : CavityDisorder N M k×Model.Vector N => numeratorMark k mu beta p.1 p.2)
    (numeratorMark_joint_measurable N M k mu beta)).log

theorem numerator_population_amplitude_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun a : Fin K→ℝ => ∫gB,(∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x
      ∂perturbedBulkGibbs N M k K mu beta v a gB)∂stdGaussian (CavityDisorder N M k))∂stdGaussian (PerturbedDisorder N k K)) :=
  (numerator_log_joint_measurable hN M k K mu beta v).stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem numerator_log_abs_bound {N M k K : ℕ} (hN : 0< N) (hM : 0< M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (a : Fin K→ℝ)
    (gB : PerturbedDisorder N k K) (gZ : CavityDisorder N M k) :
    |Real.log (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v a gB)|≤
      (Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖gZ‖ := by
  let q := perturbedBulkGibbs N M k K mu beta v a gB
  letI := perturbedBulkGibbs_probability hN M k K mu beta v a gB
  have hq := perturbedBulkGibbs_unit_ae hN M k K mu beta v a gB
  have hI := (numeratorMark_memLp_spin hM k hmu beta q hq gZ).integrable (by norm_num : (1 : ENNReal)≤2)
  have hLo := integral_mono_ae (integrable_const (1 : ℝ)) hI (.of_forall (fun x => numeratorMark_one_le hM k mu beta gZ x))
  have hHi := integral_mono_ae hI (integrable_const (Real.exp
    ((Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖gZ‖)))
    (hq.mono (fun x hx => numeratorMark_le_exp_of_unit hM k hmu beta gZ hx))
  simp only [integral_const,probReal_univ,one_smul] at hLo hHi
  have hPos : 0<∫x,numeratorMark k mu beta gZ x∂q := zero_lt_one.trans_le hLo
  have H := Real.log_le_log hPos hHi
  rw [Real.log_exp] at H
  rw [abs_of_nonneg (Real.log_nonneg hLo)]
  exact H

theorem numerator_population_cube_integrable {N M k K : ℕ} (hN : 0< N) (hM : 0< M) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    Integrable (fun a : Fin K→ℝ => ∫gB,(∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x
      ∂perturbedBulkGibbs N M k K mu beta v a gB)∂stdGaussian (CavityDisorder N M k))∂stdGaussian (PerturbedDisorder N k K))
      (positiveCubeLaw K) := by
  let c := Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)
  let C := c*(∫g : CavityDisorder N M k,‖g‖∂stdGaussian (CavityDisorder N M k))
  have hGI := (norm_gaussian_integrable (I := IdealCoordinate N M k)).const_mul c
  have hMeas := numerator_log_joint_measurable hN M k K mu beta v
  have hInnerMeas := (hMeas.stronglyMeasurable.integral_prod_right' (ν := stdGaussian (CavityDisorder N M k))).measurable
  have hBound (a : Fin K→ℝ) (gB : PerturbedDisorder N k K) :
      |∫gZ,Real.log (∫x,numeratorMark k mu beta gZ x∂perturbedBulkGibbs N M k K mu beta v a gB)
        ∂stdGaussian (CavityDisorder N M k)|≤ C := by
    have hm := hMeas.comp (measurable_const.prodMk measurable_id :
      Measurable (fun gZ : CavityDisorder N M k => ((a,gB),gZ)))
    have hb := numerator_log_abs_bound hN hM hmu beta v a gB
    have hi := hGI.mono' hm.aestronglyMeasurable (.of_forall (fun gZ => by simpa only [Real.norm_eq_abs,Function.comp_apply,c] using hb gZ))
    have H := integral_mono hi.abs hGI (fun gZ => hb gZ)
    rw [integral_const_mul] at H
    exact (abs_integral_le_integral_abs).trans H
  have hOuter (a : Fin K→ℝ) := probability_integral_abs_bound (stdGaussian (PerturbedDisorder N k K))
    (hInnerMeas.comp (measurable_const.prodMk measurable_id)) (hBound a)
  exact (probability_integral_abs_bound (positiveCubeLaw K)
    (numerator_population_amplitude_measurable hN M k K mu beta v) (fun a => (hOuter a).2)).1

private theorem theta_feature_continuous (N M k : ℕ) (mu beta : ℝ) :
    Continuous (fun x : Model.Vector N => FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
      (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p) x) := by
  unfold FiniteCavityGaussianCompatibility.limitingCompensatorFeature
  exact (continuous_const : Continuous (fun _ : Model.Vector N => Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
    (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)

theorem theta_log_joint_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×GroundState.Disorder N k =>
      logPartition (perturbedBulkGibbs N M k K mu beta v p.1.1 p.1.2)
        (fun x => innerSL ℝ (FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
          (fun j : Fin k => (j : ℕ)+1) (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j) x)) p.2) := by
  have hScore : Continuous (fun p : GroundState.Disorder N k×Model.Vector N =>
      inner ℝ (FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
        (fun j : Fin k => (j : ℕ)+1) (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j) p.2) p.1) :=
    ((theta_feature_continuous N M k mu beta).comp continuous_snd).inner continuous_fst
  have H := (perturbedBulkGibbs_integral_joint_measurable hN M k K mu beta v _ hScore.rexp.measurable).log
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply] using H

theorem theta_population_amplitude_measurable {N : ℕ} (hN : 0< N) (M k K : ℕ) (mu beta v : ℝ) :
    Measurable (fun a : Fin K→ℝ => ∫gB,(∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x => innerSL ℝ (FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
        (fun j : Fin k => (j : ℕ)+1) (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j) x)) gT
      ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (PerturbedDisorder N k K)) :=
  (theta_log_joint_measurable hN M k K mu beta v).stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem theta_population_cube_integrable {N M k K : ℕ} (hN : 0< N) (mu beta v : ℝ) :
    Integrable (fun a : Fin K→ℝ => ∫gB,(∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB)
      (fun x => innerSL ℝ (FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
        (fun j : Fin k => (j : ℕ)+1) (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j) x)) gT
      ∂stdGaussian (GroundState.Disorder N k))∂stdGaussian (PerturbedDisorder N k K)) (positiveCubeLaw K) := by
  let tF := fun x : Model.Vector N => FiniteCavityGaussianCompatibility.limitingCompensatorFeature M
    (fun j : Fin k => (j : ℕ)+1) (fun j => beta^2*VariationalProofs.sliceCoefficient k mu j) x
  have ht : Continuous tF := theta_feature_continuous N M k mu beta
  obtain ⟨Ct,hCt,hbt⟩ := sphere_feature_bound hN tF ht
  let C := Ct*(∫g : GroundState.Disorder N k,‖g‖∂stdGaussian (GroundState.Disorder N k))
  have hGI := (norm_gaussian_integrable (I := GroundState.Coordinate N k)).const_mul Ct
  have hMeas := theta_log_joint_measurable hN M k K mu beta v
  have hInnerMeas := (hMeas.stronglyMeasurable.integral_prod_right' (ν := stdGaussian (GroundState.Disorder N k))).measurable
  have hBound (a : Fin K→ℝ) (gB : PerturbedDisorder N k K) :
      |∫gT,logPartition (perturbedBulkGibbs N M k K mu beta v a gB) (fun x => innerSL ℝ (tF x)) gT
        ∂stdGaussian (GroundState.Disorder N k)|≤ C := by
    let q := perturbedBulkGibbs N M k K mu beta v a gB
    letI := perturbedBulkGibbs_probability hN M k K mu beta v a gB
    have hq : q≪Model.spherePrior N := gibbsMeasure_absolutelyContinuous (Model.spherePrior N)
      (perturbedBulkLinear N M k K mu beta v a) gB
    have hbQ : ∀ᵐ x∂q,‖tF x‖≤ Ct := hq.ae_le hbt
    have hbL : ∀ᵐ x∂q,‖innerSL ℝ (tF x)‖≤ Ct :=
      hbQ.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx)
    have hm := hMeas.comp (measurable_const.prodMk measurable_id :
      Measurable (fun gT : GroundState.Disorder N k => ((a,gB),gT)))
    have hb (gT : GroundState.Disorder N k) : |logPartition q (fun x => innerSL ℝ (tF x)) gT|≤ Ct*‖gT‖ :=
      abs_logPartition_le q _ ((innerSL ℝ).continuous.measurable.comp ht.measurable) hbL gT
    have hi := hGI.mono' hm.aestronglyMeasurable (.of_forall (fun gT => by simpa only [Real.norm_eq_abs,Function.comp_apply,q,tF] using hb gT))
    have H := integral_mono hi.abs hGI hb
    rw [integral_const_mul] at H
    exact (abs_integral_le_integral_abs).trans H
  have hOuter (a : Fin K→ℝ) := probability_integral_abs_bound (stdGaussian (PerturbedDisorder N k K))
    (hInnerMeas.comp (measurable_const.prodMk measurable_id)) (hBound a)
  exact (probability_integral_abs_bound (positiveCubeLaw K)
    (theta_population_amplitude_measurable hN M k K mu beta v) (fun a => (hOuter a).2)).1


end
end TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedAmplitudeIntegrability
