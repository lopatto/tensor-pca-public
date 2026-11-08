-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedASSLower
public import TensorPCA.NonRSLowerProofs.FiniteCavityPerturbedAmplitudeIntegrability
public import TensorPCA.NonRSUpperProofs.GaussianBankAveraging

/-! Exact disintegration of the cavity functional into fixed physical bulk disorder and
its independent perturbation bank. Raw population logs are integrable before any
lower bound is averaged. No new cavity value is defined.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityObservedFunctionalAveraging
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison
open FiniteCavityPerturbedFields FiniteCavityPerturbedASSLower
open FiniteCavityPerturbedAmplitudeIntegrability FiniteCavityCompensationJointPressure
open FiniteCavityGaussianCompatibility FiniteCavityNumeratorMoments FiniteCavityIdealField
open NonRSUpperProofs.SphericalPositivePerturbation
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem gaussian_norm_integrable {I : Type*} [Fintype I] :
    Integrable (fun g : EuclideanSpace ℝ I ↦ ‖g‖) (stdGaussian (EuclideanSpace ℝ I)) := by
  have H := GaussianSpinInterpolation.gaussian_norm_integrable (ι := I)
  rwa [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at H

theorem actual_population_mean_measurable {N : ℕ} (hN : 0<N) (M k K : ℕ)
    (mu beta v : ℝ) (gB : GroundState.Disorder N k) {W : Type*} [MeasurableSpace W]
    (Y : W×Model.Vector N → ℝ) (hY : Measurable Y) :
    Measurable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×W ↦
      ∫x,Y (p.2,x) ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))) := by
  have hJoin : Measurable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×W ↦
      sumJoin (gB,p.1.2)) :=
    sumJoin.continuous.measurable.comp (measurable_const.prodMk measurable_fst.snd)
  have hInput : Measurable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×W ↦
      ((p.1.1,sumJoin (gB,p.1.2)),p.2)) :=
    (measurable_fst.fst.prodMk hJoin).prodMk measurable_snd
  convert (perturbedBulkGibbs_integral_joint_measurable hN M k K mu beta v Y hY).comp hInput using 1 <;> rfl

private theorem theta_log_abs_bound {N : ℕ} (hN : 0<N) (M k K : ℕ) (mu beta v : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (a : Fin K→ℝ) (D : PerturbedDisorder N k K) (g : GroundState.Disorder N k),
      |Real.log (∫x,Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun p : Fin k ↦ p.val+1)
          (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p) x) g)
        ∂perturbedBulkGibbs N M k K mu beta v a D)|≤C*‖g‖ := by
  let F := limitingCompensatorFeature (N := N) M (fun p : Fin k ↦ p.val+1)
    (fun p ↦ beta^2*VariationalProofs.sliceCoefficient k mu p)
  have hF : Continuous F := by
    unfold F limitingCompensatorFeature
    exact (continuous_const : Continuous (fun _ : Model.Vector N ↦ Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
      (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)
  obtain ⟨C,hC,hb⟩ := sphere_feature_bound hN F hF
  refine ⟨C,hC,?_⟩
  intro a D g
  letI := perturbedBulkGibbs_probability hN M k K mu beta v a D
  have hAc := gibbsMeasure_absolutelyContinuous (Model.spherePrior N)
    (perturbedBulkLinear N M k K mu beta v a) D
  have hBase : ∀ᵐx ∂perturbedBulkGibbs N M k K mu beta v a D,‖F x‖≤C := hAc.ae_le hb
  have hQB : ∀ᵐx ∂perturbedBulkGibbs N M k K mu beta v a D,‖innerSL ℝ (F x)‖≤C :=
    hBase.mono (fun x hx ↦ by simpa only [innerSL_apply_norm] using hx)
  have H := abs_logPartition_le (perturbedBulkGibbs N M k K mu beta v a D)
    (fun x ↦ innerSL ℝ (F x)) ((innerSL ℝ).continuous.measurable.comp hF.measurable) hQB g
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply] using H

private theorem integral_abs_bound {W : Type*} [MeasurableSpace W] (gamma : Measure W)
    {f B : W→ℝ} (hf : Measurable f) (hB : Integrable B gamma) (hb : ∀w,|f w|≤B w) :
    Integrable f gamma ∧ |∫w,f w∂gamma|≤∫w,B w∂gamma := by
  have hi := hB.mono' hf.aestronglyMeasurable (.of_forall fun w ↦ by
    simpa only [Real.norm_eq_abs] using hb w)
  exact ⟨hi,(abs_integral_le_integral_abs).trans (integral_mono hi.abs hB hb)⟩

theorem fixed_bulk_raw_logs_integrable {N M k K : ℕ} (hN : 0<N) (hM : 0<M)
    {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (gB : GroundState.Disorder N k) :
    Integrable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k ↦
      Real.log (∫x,numeratorMark k mu beta p.2 x
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
      (((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (CavityDisorder N M k))) ∧
    Integrable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k ↦
      Real.log (∫x,Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) p.2)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2))))
      (((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (GroundState.Disorder N k))) := by
  have hNum := (actual_population_mean_measurable hN M k K mu beta v gB
    (fun p : CavityDisorder N M k×Model.Vector N ↦ numeratorMark k mu beta p.1 p.2)
    (numeratorMark_joint_measurable N M k mu beta)).log
  have hNBound := (gaussian_norm_integrable (I := IdealCoordinate N M k)).const_mul
    (Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))
  have hNPull : Integrable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k ↦
      (Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1))*‖p.2‖)
      (((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (CavityDisorder N M k))) :=
    measurePreserving_snd.integrable_comp_of_integrable hNBound
  have hNumInt := hNPull.mono'
    hNum.aestronglyMeasurable (.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using
        numerator_log_abs_bound hN hM hmu beta v p.1.1 (sumJoin (gB,p.1.2)) p.2)
  obtain ⟨C,hC,hB⟩ := theta_log_abs_bound hN M k K mu beta v
  have hF : Continuous (fun x : Model.Vector N ↦
      limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) := by
    unfold limitingCompensatorFeature
    exact (continuous_const : Continuous (fun _ : Model.Vector N ↦ Real.sqrt ((M : ℝ)/(N : ℝ)))).smul
      (NonRSUpperProofs.FiniteTensorMixtureMaximum.feature_continuous _ _)
  have hY := (continuous_inner.measurable.comp
    ((hF.measurable.comp measurable_snd).prodMk measurable_fst)).exp
  have hTheta := (actual_population_mean_measurable hN M k K mu beta v gB _ hY).log
  have hTBound := (gaussian_norm_integrable (I := GroundState.Coordinate N k)).const_mul C
  have hTPull : Integrable (fun p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k ↦ C*‖p.2‖)
      (((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (GroundState.Disorder N k))) :=
    measurePreserving_snd.integrable_comp_of_integrable hTBound
  have hThetaInt := hTPull.mono'
    hTheta.aestronglyMeasurable (.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs,Function.comp_apply] using hB p.1.1 (sumJoin (gB,p.1.2)) p.2)
  exact ⟨hNumInt,hThetaInt⟩

private theorem probability_integral_bound {W : Type*} [MeasurableSpace W]
    (gamma : Measure W) [IsProbabilityMeasure gamma] (f : W→ℝ) {C : ℝ}
    (hb : ∀w,|f w|≤C) : |∫w,f w∂gamma|≤C := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one,one_mul] using
    norm_integral_le_of_norm_le_const (μ := gamma) (f := f)
      (.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hb w)

theorem bulk_observed_integrable_and_eq {N M k K : ℕ} (hN : 0<N) (hM : 0<M)
    {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) :
    let num := fun (gB : GroundState.Disorder N k)
        (p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k) ↦
      Real.log (∫x,numeratorMark k mu beta p.2 x
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    let comp := fun (gB : GroundState.Disorder N k)
        (p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k) ↦
      Real.log (∫x,Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) p.2)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    let gammaNum := ((positiveCubeLaw K).prod
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (CavityDisorder N M k))
    let gammaComp := ((positiveCubeLaw K).prod
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (GroundState.Disorder N k))
    Integrable (fun gB ↦ (∫p,num gB p∂gammaNum)-(∫p,comp gB p∂gammaComp))
      (stdGaussian (GroundState.Disorder N k)) ∧
    (∫amp,perturbedCavityFunctional N M k K mu beta v amp∂positiveCubeLaw K)=
      ∫gB,((∫p,num gB p∂gammaNum)-(∫p,comp gB p∂gammaComp))
        ∂stdGaussian (GroundState.Disorder N k) := by
  dsimp only
  let Num := fun p : (Fin K→ℝ)×PerturbedDisorder N k K ↦
    ∫gZ : CavityDisorder N M k,Real.log (∫x,numeratorMark k mu beta gZ x
      ∂perturbedBulkGibbs N M k K mu beta v p.1 p.2)∂stdGaussian (CavityDisorder N M k)
  let Comp := fun p : (Fin K→ℝ)×PerturbedDisorder N k K ↦
    ∫gT : GroundState.Disorder N k,Real.log (∫x,Real.exp (inner ℝ
      (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
        (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) gT)
      ∂perturbedBulkGibbs N M k K mu beta v p.1 p.2)∂stdGaussian (GroundState.Disorder N k)
  have hNM : Measurable Num :=
    (numerator_log_joint_measurable hN M k K mu beta v).stronglyMeasurable.integral_prod_right'.measurable
  have hCRaw : Measurable (fun p : ((Fin K→ℝ)×PerturbedDisorder N k K)×GroundState.Disorder N k ↦
      Real.log (∫x,Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) p.2)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 p.1.2)) := by
    simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply] using
      theta_log_joint_measurable hN M k K mu beta v
  have hCM : Measurable Comp := hCRaw.stronglyMeasurable.integral_prod_right'.measurable
  let cN := Real.sqrt (M : ℝ)*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)
  let CN := cN*(∫g : CavityDisorder N M k,‖g‖∂stdGaussian (CavityDisorder N M k))
  have hNI := (gaussian_norm_integrable (I := IdealCoordinate N M k)).const_mul cN
  have hNB (a : Fin K→ℝ) (D : PerturbedDisorder N k K) : |Num (a,D)|≤CN := by
    have hm := (numerator_log_joint_measurable hN M k K mu beta v).comp
      (measurable_const.prodMk measurable_id : Measurable (fun g : CavityDisorder N M k ↦ ((a,D),g)))
    have H := (integral_abs_bound (stdGaussian (CavityDisorder N M k)) hm hNI
      (fun g ↦ numerator_log_abs_bound hN hM hmu beta v a D g)).2
    simpa only [integral_const_mul,Function.comp_apply,Num,CN] using H
  obtain ⟨cC,hcC,hCB⟩ := theta_log_abs_bound hN M k K mu beta v
  let CC := cC*(∫g : GroundState.Disorder N k,‖g‖∂stdGaussian (GroundState.Disorder N k))
  have hCI := (gaussian_norm_integrable (I := GroundState.Coordinate N k)).const_mul cC
  have hCBound (a : Fin K→ℝ) (D : PerturbedDisorder N k K) : |Comp (a,D)|≤CC := by
    have hm := hCRaw.comp (measurable_const.prodMk measurable_id :
      Measurable (fun g : GroundState.Disorder N k ↦ ((a,D),g)))
    have H := (integral_abs_bound (stdGaussian (GroundState.Disorder N k)) hm hCI (hCB a D)).2
    simpa only [integral_const_mul,Function.comp_apply,Comp,CC] using H
  let F := fun p : (Fin K→ℝ)×PerturbedDisorder N k K ↦ Num p-Comp p
  have hFM : Measurable F := hNM.sub hCM
  have hFB (p : (Fin K→ℝ)×PerturbedDisorder N k K) : |F p|≤CN+CC :=
    (abs_sub _ _).trans (add_le_add (hNB p.1 p.2) (hCBound p.1 p.2))
  have hEach (a : Fin K→ℝ) :
      (∫D,F (a,D)∂stdGaussian (PerturbedDisorder N k K))=
        perturbedCavityFunctional N M k K mu beta v a := by
    have hNInt : Integrable (fun D ↦ Num (a,D)) (stdGaussian (PerturbedDisorder N k K)) :=
      Integrable.of_bound (hNM.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable CN
        (.of_forall fun D ↦ by simpa only [Real.norm_eq_abs] using hNB a D)
    have hCInt : Integrable (fun D ↦ Comp (a,D)) (stdGaussian (PerturbedDisorder N k K)) :=
      Integrable.of_bound (hCM.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable CC
        (.of_forall fun D ↦ by simpa only [Real.norm_eq_abs] using hCBound a D)
    rw [show (fun D ↦ F (a,D))=(fun D ↦ Num (a,D)-Comp (a,D)) from rfl,integral_sub hNInt hCInt]
    simp only [Num,Comp,perturbedCavityFunctional,logPartition,GaussianSpinInterpolation.moment,
      weight,one_mul,innerSL_apply_apply]
  have hSwap := external_parameter_joined_gaussian_swap (positiveCubeLaw K) F hFM
    (fun p ↦ by simpa only [Real.norm_eq_abs] using hFB p)
  simp only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] at hSwap
  have hInnerEq (gB : GroundState.Disorder N k) :
      (∫amp,(∫gP,F (amp,sumJoin (gB,gP))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)=
      (∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k,
        Real.log (∫x,numeratorMark k mu beta p.2 x
          ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
        ∂((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
          (stdGaussian (CavityDisorder N M k)))-
      (∫p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k,
        Real.log (∫x,Real.exp (inner ℝ
          (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
            (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) p.2)
          ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
        ∂((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
          (stdGaussian (GroundState.Disorder N k))) := by
    obtain ⟨hiN,hiC⟩ := fixed_bulk_raw_logs_integrable (K := K) hN hM hmu beta v gB
    rw [integral_prod _ hiN,integral_prod _ hiN.integral_prod_left,
      integral_prod _ hiC,integral_prod _ hiC.integral_prod_left]
    rw [←integral_sub hiN.integral_prod_left.integral_prod_left hiC.integral_prod_left.integral_prod_left]
    apply integral_congr_ae
    filter_upwards [hiN.integral_prod_left.prod_right_ae,hiC.integral_prod_left.prod_right_ae] with amp hNIa hCIa
    exact integral_sub hNIa hCIa
  have hJoint : Measurable (fun p : (GroundState.Disorder N k×(Fin K→ℝ))×PerturbationDisorder N K ↦
      F (p.1.2,sumJoin (p.1.1,p.2))) :=
    hFM.comp (measurable_fst.snd.prodMk (sumJoin.continuous.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)))
  have hOM : Measurable (fun gB : GroundState.Disorder N k ↦
      ∫amp,(∫gP,F (amp,sumJoin (gB,gP))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K) :=
    hJoint.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  have hOB (gB : GroundState.Disorder N k) :
      |∫amp,(∫gP,F (amp,sumJoin (gB,gP))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K|≤CN+CC :=
    probability_integral_bound _ _ (fun amp ↦ probability_integral_bound _ _
      (fun gP ↦ hFB (amp,sumJoin (gB,gP))))
  have hOI : Integrable (fun gB : GroundState.Disorder N k ↦
      ∫amp,(∫gP,F (amp,sumJoin (gB,gP))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))∂positiveCubeLaw K)
      (stdGaussian (GroundState.Disorder N k)) :=
    Integrable.of_bound hOM.aestronglyMeasurable (CN+CC)
      (.of_forall fun gB ↦ by simpa only [Real.norm_eq_abs] using hOB gB)
  constructor
  · exact hOI.congr (.of_forall hInnerEq)
  · calc
      _=(∫amp,(∫D,F (amp,D)∂stdGaussian (PerturbedDisorder N k K))∂positiveCubeLaw K) :=
        integral_congr_ae (.of_forall fun amp ↦ (hEach amp).symm)
      _=_ := by simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using hSwap
      _=_ := integral_congr_ae (.of_forall hInnerEq)

theorem cube_cavity_lower_of_fixed_bulk_lower {N M k K : ℕ} (hN : 0<N) (hM : 0<M)
    {mu : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta v : ℝ) (L : ℝ) :
    let num := fun (gB : GroundState.Disorder N k)
        (p : ((Fin K→ℝ)×PerturbationDisorder N K)×CavityDisorder N M k) ↦
      Real.log (∫x,numeratorMark k mu beta p.2 x
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    let comp := fun (gB : GroundState.Disorder N k)
        (p : ((Fin K→ℝ)×PerturbationDisorder N K)×GroundState.Disorder N k) ↦
      Real.log (∫x,Real.exp (inner ℝ
        (limitingCompensatorFeature M (fun j : Fin k ↦ j.val+1)
          (fun j ↦ beta^2*VariationalProofs.sliceCoefficient k mu j) x) p.2)
        ∂perturbedBulkGibbs N M k K mu beta v p.1.1 (sumJoin (gB,p.1.2)))
    let gammaNum := ((positiveCubeLaw K).prod
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (CavityDisorder N M k))
    let gammaComp := ((positiveCubeLaw K).prod
      (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))).prod
        (stdGaussian (GroundState.Disorder N k))
    (∀gB,L≤((∫p,num gB p∂gammaNum)-(∫p,comp gB p∂gammaComp))/(M : ℝ))→
      L≤(∫amp,perturbedCavityFunctional N M k K mu beta v amp∂positiveCubeLaw K)/(M : ℝ) := by
  dsimp only
  intro hLower
  have H := bulk_observed_integrable_and_eq (K := K) (k := k) hN hM hmu beta v
  dsimp only at H
  have HL := integral_mono (integrable_const L) (H.1.div_const (M : ℝ)) hLower
  rw [integral_const,probReal_univ,one_smul,integral_div,←H.2] at HL
  exact HL

end
end TensorPCA.NonRSLowerProofs.FiniteCavityObservedFunctionalAveraging
