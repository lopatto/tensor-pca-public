-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixTransport
public import TensorPCA.NonRSLowerProofs.FiniteGaussianZeroMassCompression

/-! Gaussian absorption of the zero-compressed initial height block. The retained
original node q_r supplies the new quenched covariance exactly.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixGaussian
open MeasureTheory ProbabilityTheory
open FiniteCSGaussianDepthMoment FiniteGaussianHierarchyPrefixTransport
open FiniteGaussianQuadraticStep FiniteGaussianQuadraticSphericalStages
open FiniteGaussianLogStepsCompression FiniteGaussianZeroMassCompression
open FiniteGaussianSphereLogStepsCompression OneStepGaussianStepLipschitz
open OneStepGaussianZeroMassMerge OneStepGaussianTiltEndpoint
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quenched_zero_mean_merge {M : ℕ} {L : ℝ≥0} {F : Model.Vector M→ℝ}
    (hF : LipschitzWith L F) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    (∫g,gaussianLogStep (shift M v) 0 F (Real.sqrt u •g)∂stdGaussian (Model.Vector M))=
      ∫g,F (Real.sqrt (u+v) •g)∂stdGaussian (Model.Vector M) := by
  have H := gaussianLogStep_zero_merge_variances hF
    (ContinuousLinearMap.id ℝ (Model.Vector M)) hu hv (0 : Model.Vector M)
  simpa [shift,gaussianLogStep] using H

theorem sphericalStage_prefix_lower {r s M : ℕ} (hM : 0<M)
    (x : Fin (r+s)→ℝ) (y : Fin (r+s+1)→ℝ)
    (hx : ∀j,0≤x j) (hy : Monotone y) {delta : ℝ} (hdelta : 0≤delta)
    (hsmall : ∀j : Fin r,x (j.castAdd s)≤delta)
    (hlarge : ∀j : Fin s,delta<x (j.natAdd r)) (h : Model.Vector M) :
    gaussianLogStep (shift M (∑j : Fin r,increments (prefixValues y) j)) 0
      (sphericalStage M (fun j : Fin s => x (j.natAdd r)) (increments (suffixValues y)) 0) h≤
      sphericalStage M x (increments y) 0 h := by
  let layers := List.ofFn (fun j : Fin (r+s) => (x j,increments y j))
  let variances := List.ofFn (fun j : Fin r => increments (prefixValues y) j)
  let rest := List.ofFn (fun j : Fin s => (x (j.natAdd r),
    Real.sqrt (increments (suffixValues y) j) •ContinuousLinearMap.id ℝ (Model.Vector M)))
  have hInc (j : Fin (r+s)) : 0≤ increments y j :=
    sub_nonneg.mpr (hy (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hmass : ∀a∈layers,0≤a.1 := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact hx j
  have hvar : ∀a∈layers,0≤a.2 := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact hInc j
  have hVar : ∀v∈variances,0≤v := by
    intro v hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact sub_nonneg.mpr (prefixValues_monotone hy
      (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hMap : layers.map (fun a => (if a.1≤delta then 0 else a.1,
      Real.sqrt a.2 •ContinuousLinearMap.id ℝ (Model.Vector M)))=
      variances.map (fun v => (0,Real.sqrt v •ContinuousLinearMap.id ℝ (Model.Vector M)))++rest := by
    rw [show layers=List.ofFn (fun j : Fin (r+s) => (x j,increments y j)) from rfl,
      variance_layers_split,List.map_append]
    simp only [List.map_ofFn,Function.comp_def,variances,rest]
    congr 1
    · apply congrArg List.ofFn
      funext j
      simp only [if_pos (hsmall j)]
    · apply congrArg List.ofFn
      funext j
      simp only [if_neg (not_le.mpr (hlarge j))]
  have HM := gaussianLogSteps_initial_zero_variances_merge
    (log_sphericalLaplace_lipschitz hM) (ContinuousLinearMap.id ℝ (Model.Vector M))
    variances hVar rest h
  have H := (sphericalLogSteps_compress_bounds hM layers hmass hvar hdelta h).1
  rw [hMap,HM] at H
  have HI := sub_nonneg.mp H
  simpa only [layers,variances,rest,List.map_ofFn,List.sum_ofFn,Function.comp_def,
    sphericalStage,FiniteGaussianQuadraticLogSteps.quadraticSteps,List.drop_zero,shift] using HI

theorem expected_sphericalStage_prefix_lower {r s M : ℕ} (hM : 0<M)
    (x : Fin (r+s)→ℝ) (y : Fin (r+s+1)→ℝ)
    (hx : ∀j,0≤x j) (hy : Monotone y) (hy0 : 0≤y 0)
    {delta : ℝ} (hdelta : 0≤delta)
    (hsmall : ∀j : Fin r,x (j.castAdd s)≤delta)
    (hlarge : ∀j : Fin s,delta<x (j.natAdd r)) :
    (∫g,sphericalStage M (fun j : Fin s => x (j.natAdd r)) (increments (suffixValues y)) 0
        (Real.sqrt (suffixValues y 0) •g)∂stdGaussian (Model.Vector M))≤
      ∫g,sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)∂stdGaussian (Model.Vector M) := by
  let F := sphericalStage M (fun j : Fin s => x (j.natAdd r)) (increments (suffixValues y)) 0
  let v := ∑j : Fin r,increments (prefixValues y) j
  have hv : 0≤v := by
    apply Finset.sum_nonneg
    intro j _
    exact sub_nonneg.mpr (prefixValues_monotone hy
      (show j.castSucc≤j.succ by change (j : ℕ)≤(j : ℕ)+1; omega))
  have hF := sphericalStage_lipschitz hM (fun j : Fin s => x (j.natAdd r)) (increments (suffixValues y)) 0
  have hLeftI : Integrable (fun g : Model.Vector M =>
      gaussianLogStep (shift M v) 0 F (Real.sqrt (y 0) •g)) (stdGaussian (Model.Vector M)) := by
    simpa only [zero_add,shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using
      shifted_integrable (gaussianLogStep_lipschitz hF (shift M v) 0) (shift M (y 0)) (0 : Model.Vector M)
  have hRightI : Integrable (fun g : Model.Vector M =>
      sphericalStage M x (increments y) 0 (Real.sqrt (y 0) •g)) (stdGaussian (Model.Vector M)) := by
    simpa only [zero_add,shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using
      shifted_integrable (sphericalStage_lipschitz hM x (increments y) 0) (shift M (y 0)) (0 : Model.Vector M)
  have H := integral_mono hLeftI hRightI
    (fun g => sphericalStage_prefix_lower hM x y hx hy hdelta hsmall hlarge _)
  rw [quenched_zero_mean_merge hF hy0 hv] at H
  have hhead : y 0+v=suffixValues y 0 := head_add_prefix_increments y
  rw [hhead] at H
  exact H

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianHierarchyPrefixGaussian
