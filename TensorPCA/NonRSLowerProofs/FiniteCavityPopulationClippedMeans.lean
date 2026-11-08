-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.NumeratorMarkClippingTheorems
public import TensorPCA.NonRSLowerProofs.CompensationMarkClippingTheorems
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationThetaComparison

/-! Observed population means under an arbitrary unit-supported prior. Numerator raw
means dominate clipped means >=1. Compensation clipped means lie in [b,cap], without
a lower bound of one on the raw exponential. Gaussian log integrability is proved
separately.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteCavityPopulationClippedMeans
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation
open FiniteCavityNumeratorMoments NumeratorMarkClippingMeasure NumeratorMarkClippingTheorems
open FiniteCavityGaussianCompatibility FiniteCavityCompensatorEmpirical
open FiniteCavityCompensationThetaComparison GaussianFeatureCovarianceComparison
open FiniteCavityCompensatorGaussianMoments
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem numerator_clipped_mean_measurable (N M k : ℕ) (mu beta L : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] :
    Measurable (fun g : CavityDisorder N M k => ∫x,min (numeratorMark k mu beta g x) L ∂nu) := by
  have hm : Measurable (fun p : CavityDisorder N M k×Model.Vector N =>
      min (numeratorMark k mu beta p.1 p.2) L) :=
    (numeratorMark_joint_measurable N M k mu beta).min measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem numerator_clipped_mean_bounds {N M : ℕ} (hM : 0<M) (k : ℕ) (mu beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu] {L : ℝ} (hL : 1≤L)
    (g : CavityDisorder N M k) :
    1≤(∫x,min (numeratorMark k mu beta g x) L ∂nu) ∧
      (∫x,min (numeratorMark k mu beta g x) L ∂nu)≤L := by
  have hJoint : Measurable (Function.uncurry (numeratorMark (N := N) (M := M) k mu beta)) :=
    numeratorMark_joint_measurable N M k mu beta
  have hm : Measurable (fun x : Model.Vector N => numeratorMark k mu beta g x) :=
    hJoint.of_uncurry_left (x := g)
  have hi := clip_integrable nu hm (ae_of_all _ (numeratorMark_one_le hM k mu beta g)) hL
  have Hlo := integral_mono (integrable_const (1 : ℝ)) hi
    (fun x => le_min (numeratorMark_one_le hM k mu beta g x) hL)
  have Hhi := integral_mono hi (integrable_const L) (fun x => min_le_right (numeratorMark k mu beta g x) L)
  simpa only [integral_const,probReal_univ,one_smul] using And.intro Hlo Hhi

theorem numerator_population_log_clipping {N M : ℕ} (hM : 0<M) (k : ℕ) {mu : ℝ}
    (hmu : mu∈Icc (-1 : ℝ) 1) (beta : ℝ)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) {L : ℝ} (hL : 1≤L) :
    let Y := fun g : CavityDisorder N M k => ∫x,numeratorMark k mu beta g x ∂nu
    let C := fun g : CavityDisorder N M k => ∫x,min (numeratorMark k mu beta g x) L ∂nu
    Integrable (fun g => Real.log (Y g)) (stdGaussian (CavityDisorder N M k)) ∧
    Integrable (fun g => Real.log (C g)) (stdGaussian (CavityDisorder N M k)) ∧
    0≤(∫g,Real.log (Y g) ∂stdGaussian (CavityDisorder N M k))-
      (∫g,Real.log (C g) ∂stdGaussian (CavityDisorder N M k)) ∧
    (∫g,Real.log (Y g) ∂stdGaussian (CavityDisorder N M k))-
      (∫g,Real.log (C g) ∂stdGaussian (CavityDisorder N M k))≤
      Real.exp (2*(M : ℝ)*beta^2*deriv (Scalar.xiSlice k mu) 1)/L := by
  let gamma := stdGaussian (CavityDisorder N M k)
  let F := fun p : CavityDisorder N M k×Model.Vector N => numeratorMark k mu beta p.1 p.2
  have hm : Measurable F := numeratorMark_joint_measurable N M k mu beta
  have hOne : ∀ᵐp∂gamma.prod nu,1≤F p := ae_of_all _ (fun p => numeratorMark_one_le hM k mu beta p.1 p.2)
  have hiF := mark_integrable_of_square (gamma.prod nu) hm hOne (numeratorMark_joint_sq_integrable hM k hmu beta nu hnu)
  have hiC := clip_integrable (gamma.prod nu) hm hOne hL
  have hiY := hiF.integral_prod_left
  have hiMean := hiC.integral_prod_left
  have hb : ∀ᵐg∂gamma,1≤(∫x,min (numeratorMark k mu beta g x) L ∂nu) ∧
      (∫x,min (numeratorMark k mu beta g x) L ∂nu)≤∫x,numeratorMark k mu beta g x ∂nu := by
    filter_upwards [hiF.prod_right_ae,hiC.prod_right_ae] with g hg hc
    exact ⟨(numerator_clipped_mean_bounds hM k mu beta nu hL g).1,
      integral_mono hc hg (fun x => min_le_left _ _)⟩
  have H := expected_log_sub_le_expected_sub gamma hiY hiMean hb
  have hTail := numerator_mean_clip_tail_le hM k hmu beta nu hnu hL
  have hEq : (∫g,(∫x,numeratorMark k mu beta g x ∂nu)-(∫x,min (numeratorMark k mu beta g x) L ∂nu) ∂gamma)=
      ∫p : CavityDisorder N M k×Model.Vector N,F p-min (F p) L ∂gamma.prod nu := by
    rw [integral_prod _ hTail.1]
    apply integral_congr_ae
    filter_upwards [hiF.prod_right_ae,hiC.prod_right_ae] with g hg hc
    exact (integral_sub hg hc).symm
  refine ⟨log_integrable_of_one_le gamma hiY (hb.mono (fun _ h => h.1.trans h.2)),
    log_integrable_of_one_le gamma hiMean (hb.mono (fun _ h => h.1)),H.1,?_⟩
  exact H.2.trans (by rw [hEq]; exact hTail.2.2)

private theorem clipped_mean_bounds {V : Type*} [MeasurableSpace V]
    (nu : Measure V) [IsProbabilityMeasure nu] {Y : V→ℝ} (hY : Measurable Y)
    {b cap : ℝ} (hb : 0<b) (hbc : b≤cap) :
    b≤(∫x,max b (min (Y x) cap) ∂nu) ∧ (∫x,max b (min (Y x) cap) ∂nu)≤cap := by
  have hi : Integrable (fun x => max b (min (Y x) cap)) nu := by
    apply Integrable.of_bound (measurable_const.max (hY.min measurable_const)).aestronglyMeasurable cap
    exact ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (hb.le.trans (le_max_left _ _))]
      exact max_le hbc (min_le_right _ _))
  have hlo := integral_mono (integrable_const b) hi (fun x => le_max_left b (min (Y x) cap))
  have hhi := integral_mono hi (integrable_const cap) (fun x => max_le hbc (min_le_right (Y x) cap))
  simpa only [integral_const,probReal_univ,one_smul] using And.intro hlo hhi

section Compensation
variable {N M k : ℕ} {mu : ℝ} (beta : ℝ)
local notation "F" => limitingCompensatorFeature (N := N) M (fun p : Fin k => (p : ℕ)+1)
  (fun p => beta^2*VariationalProofs.sliceCoefficient k mu p)

theorem compensation_clipped_mean_measurable (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (b cap : ℝ) :
    Measurable (fun g : GroundState.Disorder N k =>
      ∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu) := by
  have hF := (thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable
  have hClip : Measurable (fun p : GroundState.Disorder N k×Model.Vector N =>
      max b (min (Real.exp (inner ℝ (F p.2) p.1)) cap)) :=
    measurable_const.max ((expMark_joint_measurable hF).min measurable_const)
  exact hClip.stronglyMeasurable.integral_prod_right'.measurable

theorem compensation_clipped_mean_bounds (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap) (g : GroundState.Disorder N k) :
    b≤(∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu) ∧
      (∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu)≤cap := by
  apply clipped_mean_bounds nu _ hb (hb1.trans hc)
  have hScore : Continuous (fun x : Model.Vector N => inner ℝ (F x) g) :=
    continuous_inner.comp ((thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).prodMk continuous_const)
  exact (Real.continuous_exp.comp hScore).measurable

theorem compensation_clipped_log_integrable (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    {b cap : ℝ} (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap) :
    Integrable (fun g : GroundState.Disorder N k =>
      Real.log (∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu)) (stdGaussian (GroundState.Disorder N k)) := by
  have hm := compensation_clipped_mean_measurable (N := N) (M := M) (k := k) (mu := mu) beta nu b cap
  apply Integrable.of_bound hm.log.aestronglyMeasurable (|Real.log b|+|Real.log cap|)
  exact ae_of_all _ (fun g => by
    have H := compensation_clipped_mean_bounds (N := N) (M := M) (k := k) (mu := mu) beta nu hb hb1 hc g
    have hlo := Real.log_le_log hb H.1
    have hhi := Real.log_le_log (hb.trans_le H.1) H.2
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le (Real.log b),le_abs_self (Real.log cap),abs_nonneg (Real.log b),abs_nonneg (Real.log cap)])

theorem compensation_population_log_integrable (hN : 0<N) (hmu : mu∈Icc (-1 : ℝ) 1)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) :
    Integrable (fun g : GroundState.Disorder N k => Real.log (∫x,Real.exp (inner ℝ (F x) g) ∂nu))
      (stdGaussian (GroundState.Disorder N k)) := by
  let C := (M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1)
  have hF := (thetaFeature_continuous (N := N) (M := M) (k := k) (mu := mu) beta).measurable
  have hB : ∀ᵐx∂nu,‖F x‖≤Real.sqrt C := hnu.mono (fun x hx =>
    Real.le_sqrt_of_sq_le (thetaFeature_norm_sq hN M k hmu beta hx).le)
  have H := feature_logPartition_integrable nu F hF (Real.sqrt_nonneg C) hB
  have HE : logPartition nu (fun x => innerSL ℝ (F x))=
      (fun g => Real.log (∫x,Real.exp (inner ℝ (F x) g) ∂nu)) := by
    funext g
    simp only [GaussianSpinInterpolation.logPartition,GaussianSpinInterpolation.moment,
      GaussianSpinInterpolation.weight,one_mul,innerSL_apply_apply]
  rw [HE] at H
  exact H

theorem compensation_population_log_clipping (hN : 0<N) (hmu : mu∈Icc (-1 : ℝ) 1)
    (nu : Measure (Model.Vector N)) [IsProbabilityMeasure nu]
    (hnu : ∀ᵐx∂nu,x∈Model.unitSphere N) {b cap : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hc : 1≤cap) :
    let A := fun g : GroundState.Disorder N k => Real.log (∫x,Real.exp (inner ℝ (F x) g) ∂nu)
    let B := fun g : GroundState.Disorder N k => Real.log (∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu)
    Integrable A (stdGaussian (GroundState.Disorder N k)) ∧
    Integrable B (stdGaussian (GroundState.Disorder N k)) ∧
    |(∫g,A g ∂stdGaussian (GroundState.Disorder N k))-(∫g,B g ∂stdGaussian (GroundState.Disorder N k))|≤
      2*Real.exp (9*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1))/2)/cap+
        2*b*Real.exp (2*((M : ℝ)*beta^2*(deriv (Scalar.xiSlice k mu) 1-Scalar.xiSlice k mu 1))) := by
  have hiA := compensation_population_log_integrable (N := N) (M := M) (k := k) (mu := mu) beta hN hmu nu hnu
  have hiB := compensation_clipped_log_integrable (N := N) (M := M) (k := k) (mu := mu) beta nu hb hb1 hc
  have H := CompensationMarkClippingTheorems.compensation_log_clipping_error_le
    hN M k hmu beta nu hnu (alpha := 1) hb hb1 hc zero_lt_one le_rfl
  have HI := norm_integral_le_integral_norm (μ := stdGaussian (GroundState.Disorder N k))
    (f := fun g : GroundState.Disorder N k => Real.log (∫x,Real.exp (inner ℝ (F x) g) ∂nu)-
      Real.log (∫x,max b (min (Real.exp (inner ℝ (F x) g)) cap) ∂nu))
  simp only [Real.norm_eq_abs] at HI
  rw [integral_sub hiA hiB] at HI
  exact ⟨hiA,hiB,HI.trans (by simpa only [Real.rpow_one,div_one] using H.2)⟩
end Compensation

end
end TensorPCA.NonRSLowerProofs.FiniteCavityPopulationClippedMeans
