-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorClipping
public import TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorMoments
public import TensorPCA.NonRSLowerProofs.FiniteGaussianOrdinaryStepsMerge

/-! Spherical numerator clipping throughout the tower, averaged over the common Gaussian
root. Increasing masses in (0,1] contract the error to the ordinary Gaussian path.
Variance merging and the spherical second moment give a bound uniform in depth and
mass gaps.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorTowerClipping
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz FiniteGaussianLogStepsCompression
open FiniteGaussianSphereLogStepsCompression OneStepGaussianTiltEndpoint OneStepGaussianTiltOuter
open FiniteGaussianSphericalNumeratorClipping FiniteGaussianSphericalNumeratorMoments
open FiniteGaussianOrdinaryStepsExponentialGrowth FiniteGaussianOrdinaryStepsMerge
open scoped NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

theorem averaged_spherical_root_clipping_bound (hM : 0<M)
    (layers : List (ℝ×ℝ))
    (hm : ∀s∈layers,0<s.1 ∧ s.1≤1)
    (hv : ∀s∈layers,0≤s.2)
    (horder : layers.Pairwise (fun s t => s.1≤t.1))
    {v0 L : ℝ} (hv0 : 0≤v0) (hL : 1≤L) :
    let steps := layers.map (fun s => (s.1,Real.sqrt s.2 • ContinuousLinearMap.id ℝ (Model.Vector M)))
    let raw := fun g : Model.Vector M => gaussianLogSteps steps (fun y => Real.log (sphericalLaplace M y)) (Real.sqrt v0 •g)
    let clipped := fun g : Model.Vector M => gaussianLogSteps steps
      (fun y => min (Real.log (sphericalLaplace M y)) (Real.log L)) (Real.sqrt v0 •g)
    Integrable raw (stdGaussian (Model.Vector M)) ∧
    Integrable clipped (stdGaussian (Model.Vector M)) ∧
    0≤(∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M)) ∧
    (∫g,raw g ∂stdGaussian (Model.Vector M))-(∫g,clipped g ∂stdGaussian (Model.Vector M))≤
      Real.exp (2*(M : ℝ)*(v0+(layers.map Prod.snd).sum))/L := by
  let steps := layers.map (fun s => (s.1,Real.sqrt s.2 • ContinuousLinearMap.id ℝ (Model.Vector M)))
  let F : Model.Vector M→ℝ := fun y => Real.log (sphericalLaplace M y)
  let G : Model.Vector M→ℝ := fun y => min (F y) (Real.log L)
  let H : Model.Vector M→ℝ := fun y => sphericalLaplace M y-min (sphericalLaplace M y) L
  let T : Model.Vector M→L[ℝ]Model.Vector M := ContinuousLinearMap.id ℝ _
  let R := Real.sqrt v0 •T
  have hF := log_sphericalLaplace_lipschitz hM
  have hG := hF.min_const (Real.log L)
  have hIR := OneStepGaussianStepLipschitz.shifted_integrable (gaussianLogSteps_lipschitz hF steps) R 0
  have hIC := OneStepGaussianStepLipschitz.shifted_integrable (gaussianLogSteps_lipschitz hG steps) R 0
  have hRaw : Integrable (fun g : Model.Vector M => gaussianLogSteps steps F (Real.sqrt v0 •g)) (stdGaussian (Model.Vector M)) := by
    simpa only [R,T,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hIR
  have hClip : Integrable (fun g : Model.Vector M => gaussianLogSteps steps G (Real.sqrt v0 •g)) (stdGaussian (Model.Vector M)) := by
    simpa only [R,T,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hIC
  have hH : Measurable H := (sphericalLaplace_measurable M).sub ((sphericalLaplace_measurable M).min measurable_const)
  have hHB : ∀z,|H z|≤2*Real.exp ((2*Real.sqrt (M : ℝ))*‖z‖) := spherical_tail_exponential_growth hM hL
  have hHI := ordinary_steps_shifted_integrable steps hH (by norm_num : (0 : ℝ)≤2)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hHB R 0
  have hOrd : Integrable (fun g : Model.Vector M => gaussianLogSteps (steps.map (fun s => (0,s.2))) H (Real.sqrt v0 •g)) (stdGaussian (Model.Vector M)) := by
    simpa only [R,T,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hHI
  have hms : ∀s∈steps,0<s.1 ∧ s.1≤1 := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact hm a ha
  have hos : steps.Pairwise (fun s t => s.1≤t.1) := by
    simpa only [steps,List.pairwise_map] using horder
  have hB (g : Model.Vector M) := spherical_root_clipping_bound hM steps hms hos hL (Real.sqrt v0 •g)
  have hNonneg : 0≤∫g : Model.Vector M,gaussianLogSteps steps F (Real.sqrt v0 •g)-gaussianLogSteps steps G (Real.sqrt v0 •g) ∂stdGaussian (Model.Vector M) :=
    integral_nonneg (fun g => (hB g).1)
  have hUpper := integral_mono (hRaw.sub hClip) hOrd (fun g => (hB g).2)
  let variances := v0::layers.map Prod.snd
  have hvar : ∀v∈variances,0≤v := by
    intro v hv'
    rcases List.mem_cons.mp hv' with rfl|h
    · exact hv0
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
      exact hv a ha
  have hmerge := ordinary_steps_merge hH (by norm_num : (0 : ℝ)≤2)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hHB T variances hvar 0
  have hMerge : (∫g : Model.Vector M,gaussianLogSteps (steps.map (fun s => (0,s.2))) H (Real.sqrt v0 •g) ∂stdGaussian (Model.Vector M))=
      ∫g : Model.Vector M,H (Real.sqrt (v0+(layers.map Prod.snd).sum) •g) ∂stdGaussian (Model.Vector M) := by
    simpa only [variances,steps,List.map_cons,List.map_map,Function.comp_def,
      gaussianLogSteps,List.foldr_cons,gaussianLogStep,if_pos rfl,ite_true,R,T,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add,List.sum_cons] using hmerge
  rw [hMerge] at hUpper
  have hTail := spherical_gaussian_clipping_tail hM (List.sum_nonneg hvar) hL
  have hFinal := hUpper.trans (by simpa only [variances,List.sum_cons,H] using hTail.2.2)
  simp only [Pi.sub_apply] at hFinal
  rw [integral_sub hRaw hClip] at hNonneg hFinal
  exact ⟨hRaw,hClip,hNonneg,hFinal⟩

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianSphericalNumeratorTowerClipping
