-- Copyright (c) 2026 Patrick Lopatto. Apache-2.0.
module
public import TensorPCA.NonRSLowerProofs.OneStepGaussianAffineBarrier
public import TensorPCA.NonRSLowerProofs.FiniteGaussianLogStepsCompression

/-! Depth-uniform affine error bounds for the existing literal Gaussian log-step list.
Only the sum of the variances enters the bound.
-/
@[expose] public section
namespace TensorPCA.NonRSLowerProofs.FiniteGaussianAffineBarrier
open MeasureTheory ProbabilityTheory
open OneStepGaussianStepLipschitz OneStepGaussianAffineBarrier
open FiniteGaussianQuadraticStep FiniteGaussianLogStepsCompression
open scoped RealInnerProductSpace NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def isotropicSteps (N : ℕ) (steps : List (ℝ×ℝ)) : List (ℝ×(Model.Vector N→L[ℝ]Model.Vector N)) :=
  steps.map (fun p => (p.1,shift N p.2))

theorem gaussianLogSteps_affineBarrier {N : ℕ} {L : ℝ≥0} {F G : Model.Vector N→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G) (steps : List (ℝ×ℝ))
    (hDelta : ∀p∈steps,0≤p.2) (hMass : ∀p∈steps,|p.1|≤1)
    (lambda : Model.Vector N) (hLambda : ‖lambda‖≤(L : ℝ)) {b a : ℝ}
    (hb : 0≤b) (ha : 0≤a) (hFG : ∀y,|F y-G y|≤affineBarrier lambda b a y) (x : Model.Vector N) :
    |gaussianLogSteps (isotropicSteps N steps) F x-gaussianLogSteps (isotropicSteps N steps) G x|≤
      Real.exp (3/2*(L : ℝ)^2*(steps.map Prod.snd).sum)*affineBarrier lambda b a x := by
  revert hDelta hMass x
  induction steps with
  | nil =>
    intro hDelta hMass x
    simpa only [isotropicSteps,List.map_nil,List.sum_nil,mul_zero,Real.exp_zero,one_mul,
      gaussianLogSteps,List.foldr_nil] using hFG x
  | cons p steps ih =>
    intro hDelta hMass x
    have hd : 0≤p.2 := hDelta p (by simp)
    have hm : |p.1|≤1 := hMass p (by simp)
    have hdt : ∀q∈steps,0≤q.2 := fun q hq => hDelta q (by simp [hq])
    have hmt : ∀q∈steps,|q.1|≤1 := fun q hq => hMass q (by simp [hq])
    let r := Real.exp (3/2*(L : ℝ)^2*(steps.map Prod.snd).sum)
    have ht : ∀y,|gaussianLogSteps (isotropicSteps N steps) F y-
        gaussianLogSteps (isotropicSteps N steps) G y|≤affineBarrier lambda (r*b) (r*a) y := by
      intro y
      rw [affineBarrier_scale]
      exact ih hdt hmt y
    have H := gaussianLogStep_affineBarrier_unit_mass
      (gaussianLogSteps_lipschitz hF (isotropicSteps N steps))
      (gaussianLogSteps_lipschitz hG (isotropicSteps N steps)) hd hm x lambda hLambda
      (mul_nonneg (Real.exp_pos _).le hb) (mul_nonneg (Real.exp_pos _).le ha) ht
    rw [affineBarrier_scale] at H
    change |gaussianLogStep (shift N p.2) p.1 (gaussianLogSteps (isotropicSteps N steps) F) x-
      gaussianLogStep (shift N p.2) p.1 (gaussianLogSteps (isotropicSteps N steps) G) x|≤_
    simp only [List.map_cons,List.sum_cons]
    exact H.trans_eq (by
      rw [← mul_assoc,← Real.exp_add]
      congr 1
      ring)

theorem gaussianLogSteps_affineBarrier_at_zero {N : ℕ} {L : ℝ≥0} {F G : Model.Vector N→ℝ}
    (hF : LipschitzWith L F) (hG : LipschitzWith L G) (steps : List (ℝ×ℝ))
    (hDelta : ∀p∈steps,0≤p.2) (hMass : ∀p∈steps,|p.1|≤1)
    (lambda : Model.Vector N) (hLambda : ‖lambda‖≤(L : ℝ)) {b a Y : ℝ}
    (hb : 0≤b) (ha : 0≤a) (hFG : ∀y,|F y-G y|≤affineBarrier lambda b a y)
    (hY : (steps.map Prod.snd).sum≤Y) :
    |gaussianLogSteps (isotropicSteps N steps) F 0-gaussianLogSteps (isotropicSteps N steps) G 0|≤
      (b+a)*Real.exp (3/2*(L : ℝ)^2*Y) := by
  have H := gaussianLogSteps_affineBarrier hF hG steps hDelta hMass lambda hLambda hb ha hFG 0
  simp only [affineBarrier,inner_zero_right,Real.exp_zero,mul_one] at H
  have he : Real.exp (3/2*(L : ℝ)^2*(steps.map Prod.snd).sum)≤
      Real.exp (3/2*(L : ℝ)^2*Y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hY (by positivity))
  exact H.trans ((mul_le_mul_of_nonneg_right he (add_nonneg hb ha)).trans_eq (mul_comm _ _))

end
end TensorPCA.NonRSLowerProofs.FiniteGaussianAffineBarrier
