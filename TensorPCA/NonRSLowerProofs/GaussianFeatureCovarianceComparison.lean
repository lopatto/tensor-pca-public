-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
-- Gaussian split/join proof adapted narrowly from the checked
-- GaussianCompactFeatureComparison port, slowequilibration
-- a28aaa336343c4caf43791ababd8ed0ee5c7b58e (Apache-2.0).
module
public import TensorPCA.NonRSLowerProofs.GaussianAbsoluteCovarianceComparison
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Absolute expected log-partition comparison for two finite Gaussian feature fields,
with no constant-diagonal assumption.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.GaussianFeatureCovarianceComparison
open MeasureTheory ProbabilityTheory Set Filter GaussianSpinInterpolation GaussianSpinComparison
open GaussianAbsoluteCovarianceComparison
open scoped RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

private def gaussianSplit : EuclideanSpace ℝ (I⊕J) →L[ℝ] EuclideanSpace ℝ I×EuclideanSpace ℝ J :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w ↦ (WithLp.toLp 2 (fun i ↦ w (.inl i)),WithLp.toLp 2 (fun j ↦ w (.inr j)))
      map_add' := by intro w z; ext i <;> rfl
      map_smul' := by intro a w; ext i <;> rfl }

private def gaussianJoin : (EuclideanSpace ℝ I×EuclideanSpace ℝ J) →L[ℝ] EuclideanSpace ℝ (I⊕J) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p ↦ WithLp.toLp 2 (Sum.elim p.1 p.2)
      map_add' := by intro p q; ext (i|j) <;> rfl
      map_smul' := by intro a p; ext (i|j) <;> rfl }

private theorem gaussianSplit_map :
    (SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (gaussianSplit (I := I) (J := J))=
      (SYK.standardGaussianMeasureOnEuclidean I).prod (SYK.standardGaussianMeasureOnEuclidean J) := by
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : I⊕J ↦ ℝ)
  have he := measurePreserving_sumPiEquivProdPi (fun _ : I⊕J ↦ gaussianReal 0 1)
  have hs : gaussianSplit ∘ (WithLp.toLp 2 : (I⊕J → ℝ) → EuclideanSpace ℝ (I⊕J))=
      (Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ∘ e := rfl
  unfold SYK.standardGaussianMeasureOnEuclidean
  rw [Measure.map_map gaussianSplit.continuous.measurable (by fun_prop),hs,
    ← Measure.map_map (by fun_prop) e.measurable,he.map_eq,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

private theorem integral_gaussianSplit_fst (f : EuclideanSpace ℝ I → ℝ)
    (hf : AEStronglyMeasurable f (SYK.standardGaussianMeasureOnEuclidean I)) :
    (∫ w, f (gaussianSplit w).1 ∂SYK.standardGaussianMeasureOnEuclidean (I⊕J))=
      ∫ x, f x ∂SYK.standardGaussianMeasureOnEuclidean I := by
  have hm : (SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (fun w ↦ (gaussianSplit w).1)=
      SYK.standardGaussianMeasureOnEuclidean I := by
    change (SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (Prod.fst ∘ gaussianSplit)=_
    rw [← Measure.map_map measurable_fst gaussianSplit.continuous.measurable,gaussianSplit_map]
    simp only [Measure.map_fst_prod,measure_univ,one_smul]
  have hf' : AEStronglyMeasurable f ((SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (fun w ↦ (gaussianSplit w).1)) := by rwa [hm]
  have H := integral_map (μ := SYK.standardGaussianMeasureOnEuclidean (I⊕J)) (by fun_prop) hf'
  rw [hm] at H
  exact H.symm

private theorem integral_gaussianSplit_snd (f : EuclideanSpace ℝ J → ℝ)
    (hf : AEStronglyMeasurable f (SYK.standardGaussianMeasureOnEuclidean J)) :
    (∫ w, f (gaussianSplit w).2 ∂SYK.standardGaussianMeasureOnEuclidean (I⊕J))=
      ∫ x, f x ∂SYK.standardGaussianMeasureOnEuclidean J := by
  have hm : (SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (fun w ↦ (gaussianSplit w).2)=
      SYK.standardGaussianMeasureOnEuclidean J := by
    change (SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (Prod.snd ∘ gaussianSplit)=_
    rw [← Measure.map_map measurable_snd gaussianSplit.continuous.measurable,gaussianSplit_map]
    simp only [Measure.map_snd_prod,measure_univ,one_smul]
  have hf' : AEStronglyMeasurable f ((SYK.standardGaussianMeasureOnEuclidean (I⊕J)).map (fun w ↦ (gaussianSplit w).2)) := by rwa [hm]
  have H := integral_map (μ := SYK.standardGaussianMeasureOnEuclidean (I⊕J)) (by fun_prop) hf'
  rw [hm] at H
  exact H.symm

private def blockLabel : I⊕J → Bool := Sum.elim (fun _ ↦ true) (fun _ ↦ false)

private def joinedLinear (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v : V) : EuclideanSpace ℝ (I⊕J) →L[ℝ] ℝ := innerSL ℝ (gaussianJoin (a v,b v))

private theorem joinedLinear_apply (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v : V) (g : EuclideanSpace ℝ (I⊕J)) :
    joinedLinear a b v g=inner ℝ (a v) (gaussianSplit g).1+inner ℝ (b v) (gaussianSplit g).2 := by
  simp only [joinedLinear,innerSL_apply_apply,PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

private theorem joined_coordinate (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v : V) (i : I⊕J) : coordinateObservable (joinedLinear a b) i v=Sum.elim (a v) (b v) i := by
  simp only [coordinateObservable,joinedLinear,innerSL_apply_apply,
    EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  rfl

private theorem joined_signedKernel (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v w : V) : signedKernel (joinedLinear a b) blockLabel v w=
      inner ℝ (b v) (b w)-inner ℝ (a v) (a w) := by
  simp only [signedKernel,joined_coordinate,Fintype.sum_sum_type,covarianceSign,blockLabel,
    Sum.elim_inl,Sum.elim_inr,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
    neg_one_mul,one_mul,Finset.sum_neg_distrib,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp only [mul_comm,sub_eq_add_neg,add_comm]

private theorem joined_rotation_zero (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v : V) (g : EuclideanSpace ℝ (I⊕J)) :
    joinedLinear a b v (rotation blockLabel 0 g)=inner ℝ (a v) (gaussianSplit g).1 := by
  rw [joinedLinear_apply]
  have h1 : (gaussianSplit (rotation blockLabel 0 g)).1=(gaussianSplit g).1 := by
    ext i
    simp [gaussianSplit,rotation_apply,rotationCoefficient,blockLabel]
  have h2 : (gaussianSplit (rotation blockLabel 0 g)).2=0 := by
    ext j
    simp [gaussianSplit,rotation_apply,rotationCoefficient,blockLabel]
  rw [h1,h2,inner_zero_right,add_zero]

private theorem joined_rotation_pi_div_two (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (v : V) (g : EuclideanSpace ℝ (I⊕J)) :
    joinedLinear a b v (rotation blockLabel (Real.pi/2) g)=inner ℝ (b v) (gaussianSplit g).2 := by
  rw [joinedLinear_apply]
  have h1 : (gaussianSplit (rotation blockLabel (Real.pi/2) g)).1=0 := by
    ext i
    simp [gaussianSplit,rotation_apply,rotationCoefficient,blockLabel]
  have h2 : (gaussianSplit (rotation blockLabel (Real.pi/2) g)).2=(gaussianSplit g).2 := by
    ext j
    simp [gaussianSplit,rotation_apply,rotationCoefficient,blockLabel]
  rw [h1,h2,inner_zero_right,zero_add]

private theorem gaussianJoin_norm_le (a : EuclideanSpace ℝ I) (b : EuclideanSpace ℝ J) :
    ‖gaussianJoin (a,b)‖≤‖a‖+‖b‖ := by
  have hsq : ‖gaussianJoin (a,b)‖^2=‖a‖^2+‖b‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,gaussianJoin,Fintype.sum_sum_type]
    rfl
  nlinarith [norm_nonneg (gaussianJoin (a,b)),norm_nonneg a,norm_nonneg b,mul_nonneg (norm_nonneg a) (norm_nonneg b)]

variable [MeasurableSpace V]

theorem feature_logPartition_integrable (nu : Measure V) [IsProbabilityMeasure nu]
    (a : V → EuclideanSpace ℝ I) (ha : Measurable a) {K : ℝ} (hK : 0≤K)
    (hb : ∀ᵐ v ∂nu, ‖a v‖≤K) :
    Integrable (logPartition nu (fun v ↦ innerSL ℝ (a v))) (stdGaussian (EuclideanSpace ℝ I)) := by
  have hA : Measurable (fun v ↦ innerSL ℝ (a v)) := (innerSL ℝ).continuous.measurable.comp ha
  have hAb : ∀ᵐ v ∂nu, ‖innerSL ℝ (a v)‖≤K := by simpa only [innerSL_apply_norm] using hb
  have hcont := (logPartition_contDiff nu _ hA hK hAb).continuous
  have hi := GaussianSpinInterpolation.gaussian_norm_integrable (ι := I)
  rw [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] at hi
  apply (hi.const_mul K).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun g ↦ by simpa only [Real.norm_eq_abs] using abs_logPartition_le nu _ hA hAb g)

theorem expected_logPartition_abs_sub_le (nu : Measure V) [IsProbabilityMeasure nu]
    (a : V → EuclideanSpace ℝ I) (b : V → EuclideanSpace ℝ J)
    (ha : Measurable a) (hb : Measurable b) {KA KB ddiag dpair : ℝ}
    (hKA : 0≤KA) (hKB : 0≤KB) (hba : ∀ᵐ v ∂nu, ‖a v‖≤KA) (hbb : ∀ᵐ v ∂nu, ‖b v‖≤KB)
    (hdiag : ∀ᵐ v ∂nu, |inner ℝ (a v) (a v)-inner ℝ (b v) (b v)|≤ddiag)
    (hpair : ∀ᵐ p ∂nu.prod nu, |inner ℝ (a p.1) (a p.2)-inner ℝ (b p.1) (b p.2)|≤dpair) :
    |(∫ g, logPartition nu (fun v ↦ innerSL ℝ (a v)) g ∂stdGaussian (EuclideanSpace ℝ I))-
      (∫ g, logPartition nu (fun v ↦ innerSL ℝ (b v)) g ∂stdGaussian (EuclideanSpace ℝ J))|≤
      (ddiag+dpair)/2 := by
  have hLa : Measurable (fun v ↦ innerSL ℝ (a v)) := (innerSL ℝ).continuous.measurable.comp ha
  have hLb : Measurable (fun v ↦ innerSL ℝ (b v)) := (innerSL ℝ).continuous.measurable.comp hb
  have hAa : ∀ᵐ v ∂nu, ‖innerSL ℝ (a v)‖≤KA := by simpa only [innerSL_apply_norm] using hba
  have hBb : ∀ᵐ v ∂nu, ‖innerSL ℝ (b v)‖≤KB := by simpa only [innerSL_apply_norm] using hbb
  have hAm : Integrable (logPartition nu (fun v ↦ innerSL ℝ (a v))) (SYK.standardGaussianMeasureOnEuclidean I) := by
    simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using feature_logPartition_integrable nu a ha hKA hba
  have hBm : Integrable (logPartition nu (fun v ↦ innerSL ℝ (b v))) (SYK.standardGaussianMeasureOnEuclidean J) := by
    simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using feature_logPartition_integrable nu b hb hKB hbb
  have hL : Measurable (joinedLinear a b) := by
    exact (innerSL ℝ).continuous.measurable.comp (gaussianJoin.continuous.measurable.comp (ha.prodMk hb))
  have hAB : ∀ᵐ v ∂nu, ‖joinedLinear a b v‖≤KA+KB := by
    filter_upwards [hba,hbb] with v hva hvb
    change ‖innerSL ℝ (gaussianJoin (a v,b v))‖≤KA+KB
    rw [innerSL_apply_norm]
    exact (gaussianJoin_norm_le (a v) (b v)).trans (add_le_add hva hvb)
  have hD : ∀ᵐ v ∂nu, |signedKernel (joinedLinear a b) blockLabel v v|≤ddiag := by
    filter_upwards [hdiag] with v hv
    rw [joined_signedKernel,abs_sub_comm]
    exact hv
  have hP : ∀ᵐ p ∂nu.prod nu, |signedKernel (joinedLinear a b) blockLabel p.1 p.2|≤dpair := by
    filter_upwards [hpair] with p hp
    rw [joined_signedKernel,abs_sub_comm]
    exact hp
  have H := averagedRotatedLogPartition_abs_sub_le nu (joinedLinear a b) hL (add_nonneg hKA hKB) hAB blockLabel hD hP
  have h0 : averagedRotatedLogPartition nu (joinedLinear a b) blockLabel 0=
      ∫ g, logPartition nu (fun v ↦ innerSL ℝ (a v)) g ∂SYK.standardGaussianMeasureOnEuclidean I := by
    unfold averagedRotatedLogPartition
    calc
      _ = ∫ g, logPartition nu (fun v ↦ innerSL ℝ (a v)) (gaussianSplit g).1
          ∂SYK.standardGaussianMeasureOnEuclidean (I⊕J) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun g ↦ by
          unfold logPartition GaussianSpinInterpolation.moment weight
          dsimp only
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall (fun v ↦ by dsimp only; rw [joined_rotation_zero]; rfl))
      _ = _ := integral_gaussianSplit_fst _ hAm.aestronglyMeasurable
  have hpi : averagedRotatedLogPartition nu (joinedLinear a b) blockLabel (Real.pi/2)=
      ∫ g, logPartition nu (fun v ↦ innerSL ℝ (b v)) g ∂SYK.standardGaussianMeasureOnEuclidean J := by
    unfold averagedRotatedLogPartition
    calc
      _ = ∫ g, logPartition nu (fun v ↦ innerSL ℝ (b v)) (gaussianSplit g).2
          ∂SYK.standardGaussianMeasureOnEuclidean (I⊕J) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun g ↦ by
          unfold logPartition GaussianSpinInterpolation.moment weight
          dsimp only
          congr 1
          apply integral_congr_ae
          exact Eventually.of_forall (fun v ↦ by dsimp only; rw [joined_rotation_pi_div_two]; rfl))
      _ = _ := integral_gaussianSplit_snd _ hBm.aestronglyMeasurable
  rw [hpi,h0,abs_sub_comm] at H
  simpa only [SYK.standardGaussianMeasureOnEuclidean,map_pi_eq_stdGaussian] using H

end
end TensorPCA.NonRSLowerProofs.GaussianFeatureCovarianceComparison
