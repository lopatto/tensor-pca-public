-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityRetainedPrior
public import TensorPCA.NonRSLowerProofs.FiniteCavityReferenceGramBounds
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure
public import TensorPCA.NonRSLowerProofs.FiniteCavityShellGibbsPartition

/-! Exact factorization of the normalized retained ideal partition. The annulus mass
cancels only inside its conditional probability. The two outside restriction masses
are left to the reference-pressure comparison.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityIdealRetainedPressure
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityRetainedPrior FiniteCavityRetainedMass FiniteCavityReferenceLaw
open FiniteCavityReferenceGramBounds FiniteCavityIdealField FiniteCavityGaussianCompatibility
open FiniteCavityShellGibbsPartition FiniteCavityShellLinearPartition
open FiniteCavityCompensationJointPressure GaussianCompactFeatureComparison
open GaussianFeatureCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem fixed_cavity_joint_integrable {N M : ℕ} (k : ℕ) {mu L : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hL : 0≤L)
    (q : Measure (Model.Vector N)) [IsProbabilityMeasure q] (hq : ∀ᵐ x∂q,‖x‖=1)
    (nu : Measure (Model.Vector M)) [IsFiniteMeasure nu] (hEta : ∀ᵐ eta∂nu,‖eta‖^2≤L)
    (g : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    Integrable (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (cavityFeature k mu beta p.2 p.1) g))
      (q.prod nu) := by
  have hs : Continuous (fun p : Model.Vector N×Model.Vector M => inner ℝ (cavityFeature k mu beta p.2 p.1) g) :=
    ((cavityFeature_joint_continuous N M k mu beta).comp (continuous_fst.prodMk continuous_snd)).inner continuous_const
  apply Integrable.of_bound hs.rexp.aestronglyMeasurable
    (Real.exp (Real.sqrt L*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1)*‖g‖))
  apply (Measure.ae_prod_iff_ae_ae (isClosed_le hs.rexp.norm continuous_const).measurableSet).2
  filter_upwards [hq] with x hx
  filter_upwards [hEta] with eta heta
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  exact ((le_abs_self _).trans (abs_real_inner_le_norm _ _)).trans
    (mul_le_mul_of_nonneg_right (cavityFeature_norm_le k hmu beta hL eta heta hx) (norm_nonneg g))

private theorem annulus_integral_eq_mass_mul_cond {M : ℕ} (hM : 0<M) {delta : ℝ}
    (hdelta : 0<delta) (f : Model.Vector M→ℝ) :
    (∫eta in gaussianAnnulus M delta,f eta∂stdGaussian (Model.Vector M))=
      annulusMass M delta*(∫eta,f eta∂ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)) := by
  have hp := annulusMass_pos hM hdelta
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  change _=annulusMass M delta*((annulusMass M delta)⁻¹*_)
  rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]

theorem conditional_annulus_partition_bulkGibbs_lower {N M : ℕ} (hN : 0<N) (hM : 0<M)
    (k : ℕ) {mu delta : ℝ} (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ) (hdelta : 0<delta)
    (gB : GroundState.Disorder N k) (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    (∫x,(∫u,Real.exp (inner ℝ (cavityFeature k mu beta (Real.sqrt (M : ℝ) •u) x) gZ)
      ∂Model.spherePrior M)∂bulkGibbs N M k mu beta gB)≤
    ∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
      ∂bulkGibbs N M k mu beta gB)
      ∂ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta) := by
  have H := annulus_partition_bulkGibbs_lower hN hM k hmu beta delta hdelta.le gB gZ
  rw [annulus_integral_eq_mass_mul_cond hM hdelta] at H
  change annulusMass M delta*_≤annulusMass M delta*_ at H
  have hp := annulusMass_pos hM hdelta
  nlinarith only [H,hp]

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

/-- Ordinary Gibbs factorization with an independent auxiliary prior. All
normalizers and the needed product integrability follow from feature bounds. -/
theorem joint_gibbs_log_factorization {V W I J : Type*} [MeasurableSpace V] [MeasurableSpace W]
    [Fintype I] [Fintype J] (nu : Measure V) (zeta : Measure W)
    [IsProbabilityMeasure nu] [IsProbabilityMeasure zeta]
    (a : V→EuclideanSpace ℝ I) (b : V×W→EuclideanSpace ℝ J)
    (ha : Measurable a) (hb : Measurable b) {KA KB : ℝ} (hKA : 0≤KA) (hKB : 0≤KB)
    (hba : ∀ᵐ x∂nu,‖a x‖≤KA) (hbb : ∀ᵐ p∂nu.prod zeta,‖b p‖≤KB)
    (gB : EuclideanSpace ℝ I) (gZ : EuclideanSpace ℝ J) :
    Real.log (∫p : V×W,Real.exp (inner ℝ (a p.1) gB+inner ℝ (b p) gZ)∂nu.prod zeta)=
      logPartition nu (fun x => innerSL ℝ (a x)) gB+
        Real.log (∫w,(∫x,Real.exp (inner ℝ (b (x,w)) gZ)
          ∂gibbsMeasure nu (fun x => innerSL ℝ (a x)) gB)∂zeta) := by
  have hL := (innerSL ℝ).continuous.measurable.comp ha
  have hbL : ∀ᵐ x∂nu,‖innerSL ℝ (a x)‖≤KA :=
    hba.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx)
  let q := gibbsMeasure nu (fun x => innerSL ℝ (a x)) gB
  letI := gibbsMeasure_probability nu (fun x => innerSL ℝ (a x)) hL hbL gB
  have hq : q.prod zeta≪nu.prod zeta :=
    (gibbsMeasure_absolutelyContinuous nu (fun x => innerSL ℝ (a x)) gB).prod Measure.AbsolutelyContinuous.rfl
  have hmB : Measurable (fun p : V×W => inner ℝ (b p) gZ) :=
    (ContinuousLinearMap.apply ℝ ℝ gZ).continuous.measurable.comp ((innerSL ℝ).continuous.measurable.comp hb)
  have hmA : Measurable (fun p : V×W => inner ℝ (a p.1) gB) :=
    (ContinuousLinearMap.apply ℝ ℝ gB).continuous.measurable.comp ((innerSL ℝ).continuous.measurable.comp (ha.comp measurable_fst))
  have hCI : Integrable (fun p : V×W => Real.exp (inner ℝ (b p) gZ)) (q.prod zeta) := by
    apply Integrable.of_bound hmB.exp.aestronglyMeasurable (Real.exp (KB*‖gZ‖))
    filter_upwards [hq.ae_le hbb] with p hp
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg gZ))))
  have hFI : Integrable (fun p : V×W => Real.exp (inner ℝ (a p.1) gB+inner ℝ (b p) gZ)) (nu.prod zeta) := by
    apply Integrable.of_bound (hmA.add hmB).exp.aestronglyMeasurable (Real.exp (KA*‖gB‖+KB*‖gZ‖))
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hba,hbb] with p hp hq
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    exact add_le_add ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg gB))))
      ((le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg gZ))))
  have hCpos : 0<∫w,(∫x,Real.exp (inner ℝ (b (x,w)) gZ)∂q)∂zeta := by
    rw [← integral_integral_swap hCI,← integral_prod _ hCI]
    exact integral_exp_pos hCI
  let Z := GaussianSpinInterpolation.moment nu (fun _ => 1) (fun x => innerSL ℝ (a x)) gB
  have hZ : 0<Z := moment_one_pos _ _ hL hbL gB
  have hPoint (w : W) :
      (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (b (x,w)) gZ)∂nu)=
      Z*(∫x,Real.exp (inner ℝ (b (x,w)) gZ)∂q) := by
    rw [show q=gibbsMeasure nu (fun x => innerSL ℝ (a x)) gB from rfl,
      integral_gibbsMeasure nu (fun x => innerSL ℝ (a x)) hL hbL]
    change _=Z*((∫x,Real.exp (inner ℝ (b (x,w)) gZ)*Real.exp (inner ℝ (a x) gB)∂nu)/Z)
    rw [mul_div_cancel₀ _ hZ.ne']
    apply integral_congr_ae
    exact .of_forall fun x => by dsimp only; rw [Real.exp_add]; ring
  have hPart : (∫p : V×W,Real.exp (inner ℝ (a p.1) gB+inner ℝ (b p) gZ)∂nu.prod zeta)=
      Z*(∫w,(∫x,Real.exp (inner ℝ (b (x,w)) gZ)∂q)∂zeta) := by
    rw [integral_prod _ hFI,integral_integral_swap hFI]
    simp_rw [hPoint]
    rw [integral_const_mul]
  have H := congrArg Real.log hPart
  rw [Real.log_mul hZ.ne' hCpos.ne'] at H
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,Z,q] using H

section Actual
variable {N M k : ℕ} (hN : 0<N) (hM : 0<M) {mu e delta : ℝ}
  (hmu : mu∈Icc (-1 : ℝ) 1) (he : 0<e) (hdelta : 0<delta) (beta : ℝ)
local notation "a" => bulkFeature (N := N) M (fun p : Fin k => (p : ℕ)+1) (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)
local notation "A" => ProbabilityTheory.cond (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)
include hN hmu hdelta

private theorem ideal_product_feature_bounds :
    ∃KA KB : ℝ,0≤KA ∧ 0≤KB ∧
      (∀ᵐ z∂(Model.spherePrior N).prod A,‖a z.1‖≤KA) ∧
      (∀ᵐ z∂(Model.spherePrior N).prod A,‖cavityFeature k mu beta z.2 z.1‖≤KB) := by
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  refine ⟨KA,Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1),hKA,by positivity,
    Measure.quasiMeasurePreserving_fst.ae hba,?_⟩
  have hx : ∀ᵐ z∂(Model.spherePrior N).prod A,‖z.1‖=1 :=
    Measure.quasiMeasurePreserving_fst.ae (Geometry.spherePrior_norm_ae hN)
  have hz : ∀ᵐ z∂(Model.spherePrior N).prod A,z.2∈gaussianAnnulus M delta :=
    Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (gaussianAnnulus_measurableSet M delta))
  filter_upwards [hx,hz] with z hx hz
  exact cavityFeature_norm_le k hmu beta (by positivity) z.2 hz.2 hx

private theorem full_product_integrable (gB : GroundState.Disorder N k)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    Integrable (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)) ((Model.spherePrior N).prod A) := by
  obtain ⟨KA,KB,hKA,hKB,hba,hbb⟩ := ideal_product_feature_bounds hN hmu hdelta beta
  have hc := (cavityFeature_joint_continuous N M k mu beta).comp (continuous_fst.prodMk continuous_snd)
  have ha : Continuous (fun p : Model.Vector N×Model.Vector M => a p.1) :=
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).comp continuous_fst
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

theorem retained_partition_eq_product (gB : GroundState.Disorder N k)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    (∫z,Real.exp (inner ℝ (idealReferenceFeature N M k mu beta z) (sumJoin (gB,gZ)))
      ∂retainedPrior N M e delta)=
    ∫p : Model.Vector N×Model.Vector M,Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)∂(Model.spherePrior N).prod A := by
  have H := retained_integral_ignoring_radius hN hM he hdelta
    (fun p : Model.Vector N×Model.Vector M => Real.exp (inner ℝ (a p.1) gB+
      inner ℝ (cavityFeature k mu beta p.2 p.1) gZ))
    (full_product_integrable hN hmu hdelta beta gB gZ).aestronglyMeasurable
  convert H using 1
  apply integral_congr_ae
  exact .of_forall fun z => by
    change Real.exp (inner ℝ (sumJoin (a z.1,cavityFeature k mu beta z.2.2 z.1)) (sumJoin (gB,gZ)))=_
    rw [sumJoin_inner]

theorem pointwise_ideal_retained_log_factorization (gB : GroundState.Disorder N k)
    (gZ : EuclideanSpace ℝ (IdealCoordinate N M k)) :
    logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealReferenceFeature N M k mu beta z))
      (sumJoin (gB,gZ))=
    logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB+
      Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
        ∂bulkGibbs N M k mu beta gB)∂A) := by
  have hAz : (stdGaussian (Model.Vector M)) (gaussianAnnulus M delta)≠0 :=
    (ENNReal.toReal_pos_iff.mp (annulusMass_pos hM hdelta)).1.ne'
  letI := cond_isProbabilityMeasure hAz
  letI := bulkGibbs_probability hN M k mu beta gB
  have hFI := full_product_integrable hN hmu hdelta beta gB gZ
  have hCI := fixed_cavity_joint_integrable k hmu beta (by positivity : 0≤(M : ℝ)*(1+delta))
    (bulkGibbs N M k mu beta gB) (bulkGibbs_norm_ae hN M k mu beta gB) A
    ((ae_cond_mem (gaussianAnnulus_measurableSet M delta)).mono (fun eta heta => heta.2)) gZ
  have hCpos : 0<∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
      ∂bulkGibbs N M k mu beta gB)∂A := by
    rw [← integral_integral_swap (f := fun x eta => Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)) hCI,
      ← integral_prod _ hCI]
    exact integral_exp_pos hCI
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  have hLa := (bulkLinear_continuous N M k mu beta).measurable
  have hbL : ∀ᵐ x∂Model.spherePrior N,‖bulkLinear N M k mu beta x‖≤KA :=
    hba.mono (fun x hx => by simpa only [bulkLinear,innerSL_apply_norm] using hx)
  let Z := GaussianSpinInterpolation.moment (Model.spherePrior N) (fun _ => 1) (bulkLinear N M k mu beta) gB
  have hZ : 0<Z := moment_one_pos _ _ hLa hbL gB
  have hEta (eta : Model.Vector M) :
      (∫x,Real.exp (inner ℝ (a x) gB+inner ℝ (cavityFeature k mu beta eta x) gZ)∂Model.spherePrior N)=
        Z*(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)∂bulkGibbs N M k mu beta gB) := by
    rw [bulkGibbs,integral_gibbsMeasure (Model.spherePrior N) (bulkLinear N M k mu beta) hLa hbL]
    change _=Z*((∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)*
      Real.exp (bulkLinear N M k mu beta x gB)∂Model.spherePrior N)/Z)
    rw [mul_div_cancel₀ _ hZ.ne']
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [bulkLinear,innerSL_apply_apply,Real.exp_add]; ring
  have hPartition : (∫p : Model.Vector N×Model.Vector M,
      Real.exp (inner ℝ (a p.1) gB+inner ℝ (cavityFeature k mu beta p.2 p.1) gZ)
      ∂(Model.spherePrior N).prod A)=
      Z*(∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
        ∂bulkGibbs N M k mu beta gB)∂A) := by
    rw [integral_prod _ hFI,integral_integral_swap hFI]
    simp_rw [hEta]
    rw [integral_const_mul]
  have H := congrArg Real.log ((retained_partition_eq_product hN hM hmu he hdelta beta gB gZ).trans hPartition)
  rw [Real.log_mul hZ.ne' hCpos.ne'] at H
  simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,Z] using H


private theorem ideal_retained_component_bounds :
    ∃KA KB : ℝ,0≤KA ∧ 0≤KB ∧
      (∀ᵐ z∂retainedPrior N M e delta,‖a z.1‖≤KA) ∧
      (∀ᵐ z∂retainedPrior N M e delta,‖cavityFeature k mu beta z.2.2 z.1‖≤KB) := by
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  refine ⟨KA,Real.sqrt ((M : ℝ)*(1+delta))*|beta| *Real.sqrt (deriv (Scalar.xiSlice k mu) 1),hKA,by positivity,
    Measure.quasiMeasurePreserving_fst.ae hba,?_⟩
  filter_upwards [retainedPrior_support_ae hN e delta] with z hz
  exact cavityFeature_norm_le k hmu beta (by positivity) z.2.2 hz.2.2.2.2 hz.1

private theorem ideal_retained_joined_product :
    Integrable (fun p : GroundState.Disorder N k×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      Real.log (∫z,Real.exp (inner ℝ (a z.1) p.1+inner ℝ (cavityFeature k mu beta z.2.2 z.1) p.2)
        ∂retainedPrior N M e delta))
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) ∧
    (∫g,logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealReferenceFeature N M k mu beta z)) g
      ∂stdGaussian (EuclideanSpace ℝ (GroundState.Coordinate N k⊕IdealCoordinate N M k)))=
    ∫gB,(∫gZ,Real.log (∫z,Real.exp (inner ℝ (a z.1) gB+inner ℝ (cavityFeature k mu beta z.2.2 z.1) gZ)
      ∂retainedPrior N M e delta)∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))
      ∂stdGaussian (GroundState.Disorder N k) := by
  letI := retainedPrior_probability hN hM he hdelta
  obtain ⟨KA,KB,hKA,hKB,hba,hbb⟩ := ideal_retained_component_bounds hN hM hmu he hdelta beta
  have ha := (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).comp
    (continuous_fst : Continuous (fun z : Model.Vector N×(ℝ×Model.Vector M) => z.1))
  have hb := (cavityFeature_joint_continuous N M k mu beta).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd) :
      Continuous (fun z : Model.Vector N×(ℝ×Model.Vector M) => (z.1,z.2.2)))
  exact joined_logPartition_product_integrable_and_eq (retainedPrior N M e delta)
    (fun z => a z.1) (fun z => cavityFeature k mu beta z.2.2 z.1) ha.measurable hb.measurable hKA hKB hba hbb

theorem conditional_increment_joint_integrable :
    Integrable (fun p : GroundState.Disorder N k×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) p.2)
        ∂bulkGibbs N M k mu beta p.1)∂A))
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) := by
  have hP := (ideal_retained_joined_product (k := k) hN hM hmu he hdelta beta).1
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  have hB : Integrable (logPartition (Model.spherePrior N) (bulkLinear N M k mu beta))
      (stdGaussian (GroundState.Disorder N k)) := feature_logPartition_integrable _ _
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable hKA hba
  have hBP : Integrable (fun p : GroundState.Disorder N k×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  apply (hP.sub hBP).congr
  exact .of_forall fun p => by
    have H := pointwise_ideal_retained_log_factorization hN hM hmu he hdelta beta p.1 p.2
    simp only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,idealReferenceFeature,sumJoin_inner] at H
    dsimp only [Pi.sub_apply]
    simp only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul]
    linarith only [H]

theorem expected_ideal_retained_eq_bulk_add_conditional_increment :
    (∫g,logPartition (retainedPrior N M e delta) (fun z => innerSL ℝ (idealReferenceFeature N M k mu beta z)) g
      ∂stdGaussian (EuclideanSpace ℝ (GroundState.Coordinate N k⊕IdealCoordinate N M k)))=
    (∫gB,logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB∂stdGaussian (GroundState.Disorder N k))+
    ∫gB,(∫gZ,Real.log (∫eta,(∫x,Real.exp (inner ℝ (cavityFeature k mu beta eta x) gZ)
      ∂bulkGibbs N M k mu beta gB)∂A)∂stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))
      ∂stdGaussian (GroundState.Disorder N k) := by
  have hP := ideal_retained_joined_product (k := k) hN hM hmu he hdelta beta
  have hI := conditional_increment_joint_integrable (k := k) hN hM hmu he hdelta beta
  obtain ⟨KA,hKA,hba⟩ := sphere_feature_bound hN a
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta)
  have hB : Integrable (logPartition (Model.spherePrior N) (bulkLinear N M k mu beta))
      (stdGaussian (GroundState.Disorder N k)) := feature_logPartition_integrable _ _
    (FiniteCavityCompensationJointPressure.bulkFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable hKA hba
  have hBP : Integrable (fun p : GroundState.Disorder N k×EuclideanSpace ℝ (IdealCoordinate N M k) =>
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1)
      ((stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k)))) :=
    measurePreserving_fst.integrable_comp_of_integrable hB
  have hBI : (∫p : GroundState.Disorder N k×EuclideanSpace ℝ (IdealCoordinate N M k),
      logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) p.1
      ∂(stdGaussian (GroundState.Disorder N k)).prod (stdGaussian (EuclideanSpace ℝ (IdealCoordinate N M k))))=
      ∫gB,logPartition (Model.spherePrior N) (bulkLinear N M k mu beta) gB∂stdGaussian (GroundState.Disorder N k) := by
    rw [integral_fun_fst,probReal_univ,one_smul]
  rw [hP.2,← integral_prod _ hP.1,← integral_prod _ hI,← hBI,← integral_add hBP hI]
  apply integral_congr_ae
  exact .of_forall fun p => by
    have H := pointwise_ideal_retained_log_factorization hN hM hmu he hdelta beta p.1 p.2
    simpa only [logPartition,GaussianSpinInterpolation.moment,weight,one_mul,innerSL_apply_apply,idealReferenceFeature,sumJoin_inner] using H

end Actual


end
end TensorPCA.NonRSLowerProofs.FiniteCavityIdealRetainedPressure
