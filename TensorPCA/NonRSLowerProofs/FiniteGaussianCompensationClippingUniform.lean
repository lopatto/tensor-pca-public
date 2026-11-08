-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.FiniteGaussianAffineClipping

/-! Scalar compensation log towers admit cutoffs chosen before every finite hierarchy,
without a lower height gap or depth-dependent constants.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianCompensationClippingUniform
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz FiniteGaussianQuadraticStep FiniteGaussianQuadraticLogSteps
open FiniteGaussianAffineBarrier FiniteGaussianAffineClipping
open FiniteGaussianLogStepsCompression FiniteGaussianLinearLogSteps
open scoped RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem scalar_compensation_clipping_bound (M : ℕ) (steps : List (ℝ×ℝ))
    (hDelta : ∀p∈steps,0≤p.2) (hMass : ∀p∈steps,|p.1|≤1)
    {v0 b cap Y : ℝ} (hv0 : 0≤v0) (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap)
    (hY : v0+(steps.map Prod.snd).sum≤Y) :
    let raw := fun g : Model.Vector 1 => gaussianLogSteps (isotropicSteps 1 steps)
      (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt v0 •g)
    let clipped := fun g : Model.Vector 1 => gaussianLogSteps (isotropicSteps 1 steps)
      (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt v0 •g)
    Integrable raw (stdGaussian (Model.Vector 1)) ∧
    Integrable clipped (stdGaussian (Model.Vector 1)) ∧
    |(∫g,raw g ∂stdGaussian (Model.Vector 1))-(∫g,clipped g ∂stdGaussian (Model.Vector 1))|≤
      (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*Y) := by
  have hRaw : LipschitzWith ‖scalarCoefficient M‖₊
      (fun h : Model.Vector 1 => Real.sqrt (M : ℝ)*h 0) := by
    simpa only [zero_add,scalarCoefficient_inner] using affine_lipschitz (scalarCoefficient M) 0
  have hClip : LipschitzWith ‖scalarCoefficient M‖₊
      (fun h : Model.Vector 1 => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) := by
    simpa only [scalarCoefficient_inner,logClamp_eq_log_mark hb hcap hbc] using
      linear_logClamp_lipschitz (scalarCoefficient M) b cap
  have hIntRaw := shifted_integrable (gaussianLogSteps_lipschitz hRaw (isotropicSteps 1 steps)) (shift 1 v0) 0
  have hIntClip := shifted_integrable (gaussianLogSteps_lipschitz hClip (isotropicSteps 1 steps)) (shift 1 v0) 0
  dsimp only
  refine ⟨?_,?_,?_⟩
  · simpa only [shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hIntRaw
  · simpa only [shift,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,zero_add] using hIntClip
  · have hd : ∀p∈((0,v0) : ℝ×ℝ)::steps,0≤p.2 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl|hp
      · exact hv0
      · exact hDelta p hp
    have hm : ∀p∈((0,v0) : ℝ×ℝ)::steps,|p.1|≤1 := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl|hp
      · norm_num
      · exact hMass p hp
    have hs : ((((0,v0) : ℝ×ℝ)::steps).map Prod.snd).sum≤Y := by
      simpa only [List.map_cons,List.sum_cons] using hY
    have H := affine_tower_positive_mark_clamp_error (scalarCoefficient M) (((0,v0) : ℝ×ℝ)::steps)
      hd hm hb hcap hbc hs
    simpa only [isotropicSteps,List.map_cons,gaussianLogSteps,List.foldr_cons,gaussianLogStep,↓reduceIte,
      scalarCoefficient_inner,scalarCoefficient_norm_sq,shift,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,zero_add] using H

theorem finite_compensation_clipping_bound {d : ℕ} (M : ℕ) (x Delta : Fin d→ℝ)
    (hx0 : ∀j,0≤x j) (hx1 : ∀j,x j≤1) (hDelta : ∀j,0≤Delta j)
    {v0 b cap Y : ℝ} (hv0 : 0≤v0) (hb : 0<b) (hcap : 0<cap) (hbc : b≤cap)
    (hY : v0+∑j : Fin d,Delta j≤Y) :
    let raw := fun g : Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 x Delta)
      (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt v0 •g)
    let clipped := fun g : Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 x Delta)
      (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt v0 •g)
    Integrable raw (stdGaussian (Model.Vector 1)) ∧
    Integrable clipped (stdGaussian (Model.Vector 1)) ∧
    |(∫g,raw g ∂stdGaussian (Model.Vector 1))-(∫g,clipped g ∂stdGaussian (Model.Vector 1))|≤
      (b+cap⁻¹)*Real.exp (3/2*(M : ℝ)*Y) := by
  let steps := List.ofFn (fun j : Fin d => (x j,Delta j))
  have hd : ∀p∈steps,0≤p.2 := by
    intro p hp
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    exact hDelta j
  have hm : ∀p∈steps,|p.1|≤1 := by
    intro p hp
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    rw [abs_of_nonneg (hx0 j)]
    exact hx1 j
  have hs : v0+(steps.map Prod.snd).sum≤Y := by
    simpa only [steps,List.map_ofFn,List.sum_ofFn,Function.comp_def] using hY
  have H := scalar_compensation_clipping_bound M steps hd hm hv0 hb hcap hbc hs
  simpa only [steps,isotropicSteps,List.map_ofFn,Function.comp_def,quadraticSteps] using H

/-- Cutoffs are chosen before the depth, all masses/variances and the head.
The bound is uniform even when the first positive mass tends to zero. -/
theorem exists_uniform_compensation_cutoffs (M : ℕ) (Y : ℝ) {eta : ℝ} (heta : 0<eta) :
    ∃b cap : ℝ,0<b ∧ b≤1 ∧ 1≤cap ∧ ∀(d : ℕ) (x Delta : Fin d→ℝ) (v0 : ℝ),
      (∀j,0≤x j) → (∀j,x j≤1) → (∀j,0≤Delta j) → 0≤v0 → v0+∑j,Delta j≤Y →
      let raw := fun g : Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 x Delta)
        (fun h => Real.sqrt (M : ℝ)*h 0) (Real.sqrt v0 •g)
      let clipped := fun g : Model.Vector 1 => gaussianLogSteps (quadraticSteps 1 x Delta)
        (fun h => Real.log (max b (min (Real.exp (Real.sqrt (M : ℝ)*h 0)) cap))) (Real.sqrt v0 •g)
      Integrable raw (stdGaussian (Model.Vector 1)) ∧
      Integrable clipped (stdGaussian (Model.Vector 1)) ∧
      |(∫g,raw g ∂stdGaussian (Model.Vector 1))-(∫g,clipped g ∂stdGaussian (Model.Vector 1))|≤eta := by
  let C := Real.exp (3/2*(M : ℝ)*Y)
  let cap := 1+2*C/eta
  let b := min 1 (eta/(2*C))
  have hC : 0<C := Real.exp_pos _
  have hCap : 1≤cap := le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hC.le) heta.le)
  have hCap0 : 0<cap := zero_lt_one.trans_le hCap
  have hb : 0<b := lt_min zero_lt_one (div_pos heta (mul_pos (by norm_num) hC))
  have hb1 : b≤1 := min_le_left _ _
  have hCb : b*C≤eta/2 := by
    calc
      _ ≤ (eta/(2*C))*C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
      _ = _ := by field_simp
  have hCCap : C/cap≤eta/2 := by
    apply (div_le_iff₀ hCap0).mpr
    dsimp only [cap]
    field_simp
    nlinarith
  refine ⟨b,cap,hb,hb1,hCap,?_⟩
  intro d x Delta v0 hx0 hx1 hDelta hv0 hTotal
  have H := finite_compensation_clipping_bound M x Delta hx0 hx1 hDelta hv0 hb hCap0 (hb1.trans hCap) hTotal
  refine ⟨H.1,H.2.1,H.2.2.trans ?_⟩
  change (b+cap⁻¹)*C≤eta
  rw [add_mul]
  have HE : cap⁻¹*C=C/cap := by ring
  rw [HE]
  linarith

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianCompensationClippingUniform
