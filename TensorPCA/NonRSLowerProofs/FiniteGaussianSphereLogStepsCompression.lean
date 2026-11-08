-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression
public import TensorPCA.NonRSLowerProofs.OneStepGaussianTiltEndpoint
public import TensorPCA.PairConcentrationProofs

/-! Explicit variance increments and the spherical linear terminal specialize the small-
height compression bound to delta*N*sum(variance)/2.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianSphereLogStepsCompression
open MeasureTheory ProbabilityTheory Set Filter
open FiniteGaussianLogStepsCompression OneStepGaussianStepLipschitz
open OneStepGaussianTiltEndpoint
open scoped NNReal RealInnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem norm_sqrt_smul_id_sq_le (N : ℕ) {v : ℝ} (hv : 0≤v) :
    ‖Real.sqrt v • (ContinuousLinearMap.id ℝ (Model.Vector N))‖^2≤v := by
  have hNorm : ‖Real.sqrt v • (ContinuousLinearMap.id ℝ (Model.Vector N))‖≤Real.sqrt v := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Model.Vector N)) (Real.sqrt_nonneg v)
  nlinarith [Real.sq_sqrt hv,norm_nonneg (Real.sqrt v • (ContinuousLinearMap.id ℝ (Model.Vector N)))]

theorem gaussianVarianceLogSteps_compress_bounds {N : ℕ} {L : ℝ≥0} {F : Model.Vector N → ℝ}
    (hF : LipschitzWith L F) (layers : List (ℝ×ℝ))
    (hmass : ∀a∈layers,0≤a.1) (hvariance : ∀a∈layers,0≤a.2)
    {delta : ℝ} (hdelta : 0≤delta) (x : Model.Vector N) :
    0≤gaussianLogSteps
        (layers.map (fun a ↦ (a.1,Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N)))) F x-
      gaussianLogSteps
        (layers.map (fun a ↦ (if a.1≤delta then 0 else a.1,
          Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N)))) F x ∧
    gaussianLogSteps
        (layers.map (fun a ↦ (a.1,Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N)))) F x-
      gaussianLogSteps
        (layers.map (fun a ↦ (if a.1≤delta then 0 else a.1,
          Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N)))) F x≤
      delta*(L : ℝ)^2*(layers.map Prod.snd).sum/2 := by
  let steps := layers.map (fun a ↦ (a.1,Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N)))
  have hm : ∀a∈steps,0≤a.1 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hmass b hb
  have H := gaussianLogSteps_compress_small_bounds hF steps
    (fun a ↦ decide (a.1≤delta)) hm hdelta (fun _ _ hs ↦ of_decide_eq_true hs) x
  have hs : (steps.map (fun a ↦ ‖a.2‖^2)).sum≤(layers.map Prod.snd).sum := by
    simp only [steps,List.map_map,Function.comp_def]
    exact List.sum_le_sum (fun a ha ↦ norm_sqrt_smul_id_sq_le N (hvariance a ha))
  have hUpper : gaussianLogSteps steps F x-
      gaussianLogSteps (steps.map (fun a ↦ (if decide (a.1≤delta) then 0 else a.1,a.2))) F x≤
      delta*(L : ℝ)^2*(layers.map Prod.snd).sum/2 := by
    refine H.2.trans ?_
    gcongr
  constructor
  · simpa only [steps,List.map_map,Function.comp_def,decide_eq_true_eq] using H.1
  · simpa only [steps,List.map_map,Function.comp_def,decide_eq_true_eq] using hUpper

theorem log_sphericalLaplace_lipschitz {N : ℕ} (hN : 0<N) :
    LipschitzWith (Real.sqrt (N : ℝ)).toNNReal (fun x ↦ Real.log (sphericalLaplace N x)) := by
  let A := fun u : Model.Vector N ↦ innerSL ℝ (Real.sqrt (N : ℝ) • u)
  have hA : Measurable A :=
    ((innerSL ℝ).continuous.comp (continuous_const_smul (Real.sqrt (N : ℝ)))).measurable
  have hb : ∀ᵐ u ∂Model.spherePrior N,‖A u‖≤Real.sqrt (N : ℝ) := by
    filter_upwards [Geometry.spherePrior_norm_ae hN] with u hu
    simp only [A,innerSL_apply_norm,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),hu,mul_one,le_refl]
  have H := PairConcentrationProofs.logPartition_lipschitz
    (Model.spherePrior N) A hA (Real.sqrt_nonneg _) hb
  have heq : GaussianSpinInterpolation.logPartition (Model.spherePrior N) A=
      (fun x ↦ Real.log (sphericalLaplace N x)) := by
    funext x
    simp only [GaussianSpinInterpolation.logPartition,GaussianSpinInterpolation.moment,
      GaussianSpinInterpolation.weight,sphericalLaplace,one_mul,A,innerSL_apply_apply,real_inner_comm]
  rw [heq] at H
  exact H

theorem sphericalLogSteps_compress_bounds {N : ℕ} (hN : 0<N)
    (layers : List (ℝ×ℝ)) (hmass : ∀a∈layers,0≤a.1) (hvariance : ∀a∈layers,0≤a.2)
    {delta : ℝ} (hdelta : 0≤delta) (x : Model.Vector N) :
    0≤gaussianLogSteps
        (layers.map (fun a ↦ (a.1,Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N))))
        (fun y ↦ Real.log (sphericalLaplace N y)) x-
      gaussianLogSteps
        (layers.map (fun a ↦ (if a.1≤delta then 0 else a.1,
          Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N))))
        (fun y ↦ Real.log (sphericalLaplace N y)) x ∧
    gaussianLogSteps
        (layers.map (fun a ↦ (a.1,Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N))))
        (fun y ↦ Real.log (sphericalLaplace N y)) x-
      gaussianLogSteps
        (layers.map (fun a ↦ (if a.1≤delta then 0 else a.1,
          Real.sqrt a.2 • ContinuousLinearMap.id ℝ (Model.Vector N))))
        (fun y ↦ Real.log (sphericalLaplace N y)) x≤
      delta*(N : ℝ)*(layers.map Prod.snd).sum/2 := by
  have H := gaussianVarianceLogSteps_compress_bounds (log_sphericalLaplace_lipschitz hN)
    layers hmass hvariance hdelta x
  rw [Real.coe_toNNReal _ (Real.sqrt_nonneg _),Real.sq_sqrt (Nat.cast_nonneg N)] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianSphereLogStepsCompression
