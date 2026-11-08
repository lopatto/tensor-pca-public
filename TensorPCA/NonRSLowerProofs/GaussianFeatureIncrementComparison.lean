-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteCavityCompensationJointPressure

/-! Increment-covariance comparison for two finite Gaussian feature fields. This wraps
the already proved continuous-spin Gaussian interpolation; its endpoints use the
independent coordinate-block Gaussian laws.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GaussianFeatureIncrementComparison
open MeasureTheory ProbabilityTheory Set GaussianSpinInterpolation GaussianSpinComparison
open GaussianCompactFeatureComparison GaussianFeatureCovarianceComparison
open FiniteCavityCompensationJointPressure
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem expected_logPartition_le_of_increment_le
    {V I J : Type*} [MeasurableSpace V] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (nu : Measure V) [IsProbabilityMeasure nu]
    (a : V→EuclideanSpace ℝ I) (b : V→EuclideanSpace ℝ J)
    (ha : Measurable a) (hb : Measurable b) {KA KB : ℝ} (hKA : 0≤KA) (hKB : 0≤KB)
    (hba : ∀ᵐ x∂nu,‖a x‖≤KA) (hbb : ∀ᵐ x∂nu,‖b x‖≤KB)
    (hinc : ∀x y,‖a x-a y‖≤‖b x-b y‖) :
    (∫g,logPartition nu (fun x => innerSL ℝ (a x)) g∂stdGaussian (EuclideanSpace ℝ I))≤
      ∫g,logPartition nu (fun x => innerSL ℝ (b x)) g∂stdGaussian (EuclideanSpace ℝ J) := by
  have hL : Measurable (combinedLinear a b) :=
    (innerSL ℝ).continuous.measurable.comp (sumJoin.continuous.measurable.comp (ha.prodMk hb))
  have hj (u : EuclideanSpace ℝ I) (v : EuclideanSpace ℝ J) : ‖sumJoin (u,v)‖≤‖u‖+‖v‖ := by
    have hsq : ‖sumJoin (u,v)‖^2=‖u‖^2+‖v‖^2 := by
      rw [← real_inner_self_eq_norm_sq,sumJoin_inner,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    nlinarith only [hsq,norm_nonneg (sumJoin (u,v)),norm_nonneg u,norm_nonneg v,
      mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  have hLB : ∀ᵐ x∂nu,‖combinedLinear a b x‖≤KA+KB := by
    filter_upwards [hba,hbb] with x hax hbx
    change ‖innerSL ℝ (sumJoin (a x,b x))‖≤KA+KB
    rw [innerSL_apply_norm]
    exact (hj _ _).trans (add_le_add hax hbx)
  have H := gaussian_increment_comparison nu (combinedLinear a b) hL (add_nonneg hKA hKB) hLB blockLabel
    (.of_forall fun p => combined_increment_nonnegative a b hinc p.1 p.2)
  have hsplit : MeasurePreserving (sumSplit (ι := I) (κ := J))
      (SYK.standardGaussianMeasureOnEuclidean (I⊕J))
      ((SYK.standardGaussianMeasureOnEuclidean I).prod (SYK.standardGaussianMeasureOnEuclidean J)) :=
    ⟨sumSplit.continuous.measurable,sumSplit_gaussian_map⟩
  have hfst := measurePreserving_fst.comp hsplit
  have hsnd := measurePreserving_snd.comp hsplit
  have hla : HasLaw (fun g => (sumSplit (ι := I) (κ := J) g).1)
      (SYK.standardGaussianMeasureOnEuclidean I) (SYK.standardGaussianMeasureOnEuclidean (I⊕J)) :=
    ⟨hfst.measurable.aemeasurable,hfst.map_eq⟩
  have hlb : HasLaw (fun g => (sumSplit (ι := I) (κ := J) g).2)
      (SYK.standardGaussianMeasureOnEuclidean J) (SYK.standardGaussianMeasureOnEuclidean (I⊕J)) :=
    ⟨hsnd.measurable.aemeasurable,hsnd.map_eq⟩
  have hAc := (logPartition_contDiff nu (fun x => innerSL ℝ (a x))
    ((innerSL ℝ).continuous.measurable.comp ha) hKA
    (hba.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx))).continuous
  have hBc := (logPartition_contDiff nu (fun x => innerSL ℝ (b x))
    ((innerSL ℝ).continuous.measurable.comp hb) hKB
    (hbb.mono (fun x hx => by simpa only [innerSL_apply_norm] using hx))).continuous
  have hea := hla.integral_comp hAc.aestronglyMeasurable
  have heb := hlb.integral_comp hBc.aestronglyMeasurable
  simp only [Function.comp_apply] at hea heb
  have h0 (g : EuclideanSpace ℝ (I⊕J)) :
      logPartition nu (combinedLinear a b) (rotation blockLabel 0 g)=
        logPartition nu (fun x => innerSL ℝ (a x)) (sumSplit g).1 := by
    unfold logPartition GaussianSpinInterpolation.moment weight
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x => by dsimp only; rw [combined_rotation_zero]; rfl
  have hp (g : EuclideanSpace ℝ (I⊕J)) :
      logPartition nu (combinedLinear a b) (rotation blockLabel (Real.pi/2) g)=
        logPartition nu (fun x => innerSL ℝ (b x)) (sumSplit g).2 := by
    unfold logPartition GaussianSpinInterpolation.moment weight
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x => by dsimp only; rw [combined_rotation_pi_div_two]; rfl
  unfold averagedRotatedLogPartition at H
  simp_rw [h0,hp] at H
  rw [hea,heb] at H
  simpa only [GaussianConcentrationBridge.standardGaussianMeasure_bridge] using H


end
end TensorPCA.NonRSLowerProofs.GaussianFeatureIncrementComparison
